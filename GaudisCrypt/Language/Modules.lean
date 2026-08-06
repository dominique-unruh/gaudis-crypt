import GaudisCrypt.Language.Programs
import Metatheory.STLCext.Normalization
import Metatheory.STLCext.Confluence
import Mathlib.Data.List.AList
import Mathlib.Logic.Equiv.Defs

namespace GaudisCrypt

/-- Possible types of modules. -/
inductive ModuleTypeRep where
  | proc : ProcedureSignature → ModuleTypeRep
  | prod : ModuleTypeRep → ModuleTypeRep → ModuleTypeRep
  | arr  : ModuleTypeRep → ModuleTypeRep → ModuleTypeRep
  | unit : ModuleTypeRep

abbrev ModuleContext := List ModuleTypeRep

/-- The right-nested product type of a hole signature (native UM copy of the TypedModules definition;
    namespace-scoped under `GaudisCrypt` to avoid clashing with `TypedModules`'s while both coexist). -/
def HoleSigs.toModuleTypeRepTuple : HoleSigs → ModuleTypeRep
  | .empty => .unit
  | .append holes sig => .prod (.proc sig) (HoleSigs.toModuleTypeRepTuple holes)

variable [ProgramSpec]

/-- Untyped module expressions: the raw syntax tree of the module calculus, with no
    context/type indices.  Well-typedness is captured extrinsically by the predicate
    `ModuleExpression.HasType`.  Variables are de Bruijn indices (`Nat`); `abs` carries no
    domain annotation (the domain is recovered by `HasType`). -/
inductive ModuleExpression : Type _ where
  | proc {sig} : Procedure sig → ModuleExpression
  | procHoles {holes} {sig} : holes.NonEmpty → ProcedureWithHoles holes sig → ModuleExpression
  | var  : Nat → ModuleExpression
  | app  : ModuleExpression → ModuleExpression → ModuleExpression
  | fst  : ModuleExpression → ModuleExpression
  | snd  : ModuleExpression → ModuleExpression
  | abs  : ModuleExpression → ModuleExpression
  | pair : ModuleExpression → ModuleExpression → ModuleExpression
  | unit : ModuleExpression

/-- `ModuleExpression.HasType m Δ T` holds when the untyped expression `m` is well-typed in
    module context `Δ` with type `T`.  This is the extrinsic counterpart of the indices of
    `TypedModules.ModuleExpression`: every `TypedModules.ModuleExpression Δ T` erases (via
    `TypedModules.ModuleExpression.erase`) to an `m` with `HasType m Δ T`, and conversely. -/
inductive ModuleExpression.HasType : ModuleExpression → ModuleContext → ModuleTypeRep → Prop where
  | proc {Δ sig} (p : Procedure sig) : HasType (.proc p) Δ (.proc sig)
  | procHoles {Δ holes sig} (ne : holes.NonEmpty) (p : ProcedureWithHoles holes sig) :
        HasType (.procHoles ne p) Δ (.arr (HoleSigs.toModuleTypeRepTuple holes) (.proc sig))
  | var {Δ} (n : Nat) (h : n < Δ.length) : HasType (.var n) Δ Δ[n]
  | app {Δ A B m n} : HasType m Δ (.arr A B) → HasType n Δ A → HasType (.app m n) Δ B
  | fst {Δ A B m} : HasType m Δ (.prod A B) → HasType (.fst m) Δ A
  | snd {Δ A B m} : HasType m Δ (.prod A B) → HasType (.snd m) Δ B
  | abs {Δ A B m} : HasType m (A :: Δ) B → HasType (.abs m) Δ (.arr A B)
  | pair {Δ A B m n} : HasType m Δ A → HasType n Δ B → HasType (.pair m n) Δ (.prod A B)
  | unit {Δ} : HasType .unit Δ .unit


namespace ModuleExpression.HasType

theorem proc_inv {Δ T sig} {p : Procedure sig} (h : HasType (.proc p) Δ T) : T = .proc sig := by
  cases h with | proc _ => rfl

theorem procHoles_inv {Δ T holes sig} {ne : holes.NonEmpty} {p : ProcedureWithHoles holes sig}
    (h : HasType (.procHoles ne p) Δ T) :
    T = .arr (HoleSigs.toModuleTypeRepTuple holes) (.proc sig) := by
  cases h with | procHoles _ _ => rfl

theorem var_inv {Δ T n} (h : HasType (.var n) Δ T) : ∃ hn : n < Δ.length, Δ[n]'hn = T := by
  cases h with | var _ h => exact ⟨h, rfl⟩

theorem app_inv {Δ B m n} (h : HasType (.app m n) Δ B) :
    ∃ A, HasType m Δ (.arr A B) ∧ HasType n Δ A := by
  cases h with | app hm hn => exact ⟨_, hm, hn⟩

theorem fst_inv {Δ A m} (h : HasType (.fst m) Δ A) : ∃ B, HasType m Δ (.prod A B) := by
  cases h with | fst hm => exact ⟨_, hm⟩

theorem snd_inv {Δ B m} (h : HasType (.snd m) Δ B) : ∃ A, HasType m Δ (.prod A B) := by
  cases h with | snd hm => exact ⟨_, hm⟩

theorem abs_inv {Δ T m} (h : HasType (.abs m) Δ T) :
    ∃ A B, T = .arr A B ∧ HasType m (A :: Δ) B := by
  cases h with | abs hm => exact ⟨_, _, rfl, hm⟩

theorem pair_inv {Δ T m n} (h : HasType (.pair m n) Δ T) :
    ∃ A B, T = .prod A B ∧ HasType m Δ A ∧ HasType n Δ B := by
  cases h with | pair hm hn => exact ⟨_, _, rfl, hm, hn⟩

theorem unit_inv {Δ T} (h : HasType .unit Δ T) : T = .unit := by
  cases h with | unit => rfl

end ModuleExpression.HasType
/-! ## De Bruijn renaming and substitution on the untyped tree

The untyped analogues of `TypedModules.ModuleExpression.rename`/`substitute`: since there are no type
indices, a renaming is a plain `Nat → Nat` and a substitution a `Nat → ModuleExpression`.
These are permanent.  Their agreement with the intrinsic versions under `erase` is recorded by
the transitional `erase_rename`/`erase_substitute*` lemmas below. -/

namespace ModuleExpression

/-- Lift a de Bruijn renaming under one binder: index `0` is fixed, `n+1 ↦ ρ n + 1`.
    Untyped analogue of `liftRenaming`. -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => ρ n + 1

/-- Apply a de Bruijn renaming to every variable, going under binders with `liftRen`.
    Untyped analogue of `TypedModules.ModuleExpression.rename`. -/
def rename (ρ : Nat → Nat) : ModuleExpression → ModuleExpression
  | .proc p         => .proc p
  | .procHoles ne p => .procHoles ne p
  | .var n          => .var (ρ n)
  | .app f a        => .app (f.rename ρ) (a.rename ρ)
  | .fst e          => .fst (e.rename ρ)
  | .snd e          => .snd (e.rename ρ)
  | .abs body       => .abs (body.rename (liftRen ρ))
  | .pair a b       => .pair (a.rename ρ) (b.rename ρ)
  | .unit           => .unit

/-- Lift a substitution under one binder: index `0 ↦ var 0`; `n+1 ↦` the weakening of `σ n`.
    Untyped analogue of `liftSubstitution`. -/
def liftSubst (σ : Nat → ModuleExpression) : Nat → ModuleExpression
  | 0     => .var 0
  | n + 1 => (σ n).rename Nat.succ

/-- Apply a simultaneous substitution to every variable, going under binders with `liftSubst`.
    Untyped analogue of `substituteSimultaneously`. -/
def substituteSimultaneously (σ : Nat → ModuleExpression) : ModuleExpression → ModuleExpression
  | .proc p         => .proc p
  | .procHoles ne p => .procHoles ne p
  | .var n          => σ n
  | .app f a        => .app (f.substituteSimultaneously σ) (a.substituteSimultaneously σ)
  | .fst e          => .fst (e.substituteSimultaneously σ)
  | .snd e          => .snd (e.substituteSimultaneously σ)
  | .abs body       => .abs (body.substituteSimultaneously (liftSubst σ))
  | .pair a b       => .pair (a.substituteSimultaneously σ) (b.substituteSimultaneously σ)
  | .unit           => .unit

/-- Single-variable substitution map: `0 ↦ arg`, `n+1 ↦ var n`.
    Untyped analogue of `variableSubstitution`. -/
def variableSubstitution (arg : ModuleExpression) : Nat → ModuleExpression
  | 0     => arg
  | n + 1 => .var n

/-- Single-variable de Bruijn substitution: replace index `0` in `body` by `arg`. -/
def substitute (body arg : ModuleExpression) : ModuleExpression :=
  body.substituteSimultaneously (variableSubstitution arg)

end ModuleExpression

/-! ## Reduction on the untyped tree, and type preservation

`ReductionStep` mirrors the intrinsic one but on raw syntax; the payoff is `HasType.preservation`
— what intrinsic typing gave for free must now be proved.  All permanent. -/

/-- The untyped tuple of procedures corresponding to an instantiation (untyped analogue of
    `HoleSigs.Instantiation.toModuleTuple`). -/
def HoleSigs.Instantiation.toModuleExpr :
    {holes : HoleSigs} → holes.Instantiation → ModuleExpression
  | .empty,      _    => .unit
  | .append _ _, inst =>
      .pair (.proc (inst .zero))
        (HoleSigs.Instantiation.toModuleExpr (fun idx => inst (.succ idx)))

/-- Non-deterministic single-step reduction on untyped module expressions. -/
inductive ModuleExpression.ReductionStep : ModuleExpression → ModuleExpression → Prop where
  | beta {body arg} : ReductionStep (.app (.abs body) arg) (body.substitute arg)
  | appL {f f' arg} : ReductionStep f f' → ReductionStep (.app f arg) (.app f' arg)
  | appR {f arg arg'} : ReductionStep arg arg' → ReductionStep (.app f arg) (.app f arg')
  | lam {body body'} : ReductionStep body body' → ReductionStep (.abs body) (.abs body')
  | pairL {a a' b} : ReductionStep a a' → ReductionStep (.pair a b) (.pair a' b)
  | pairR {a b b'} : ReductionStep b b' → ReductionStep (.pair a b) (.pair a b')
  | fstPair {a b} : ReductionStep (.fst (.pair a b)) a
  | fst {e e'} : ReductionStep e e' → ReductionStep (.fst e) (.fst e')
  | sndPair {a b} : ReductionStep (.snd (.pair a b)) b
  | snd {e e'} : ReductionStep e e' → ReductionStep (.snd e) (.snd e')
  | delta {holes sigs} (ne : holes.NonEmpty) (proc : ProcedureWithHoles holes sigs)
          (inst : holes.Instantiation) :
      ReductionStep (.app (.procHoles ne proc) inst.toModuleExpr)
        (.proc (proc.instantiate inst))

def ModuleExpression.MultiStepReduction : ModuleExpression → ModuleExpression → Prop :=
  Rewriting.Star ModuleExpression.ReductionStep

namespace ModuleExpression.HasType

/-- A de Bruijn renaming `ρ` maps context `Δ` into `Γ` if every `Δ`-index has a `Γ`-index of
    the same type sitting at the renamed position. -/
def IsRenaming (Δ Γ : ModuleContext) (ρ : Nat → Nat) : Prop :=
  ∀ {n} (h : n < Δ.length), ∃ h' : ρ n < Γ.length, Γ[ρ n]'h' = Δ[n]'h

omit [ProgramSpec] in
/-- Weakening: prepending a binder is the renaming `Nat.succ`. -/
theorem isRenaming_succ {Γ A} : IsRenaming Γ (A :: Γ) Nat.succ :=
  fun {n} h => ⟨by simpa using h, by simp⟩

omit [ProgramSpec] in
/-- A context renaming lifts under one binder to `liftRen ρ`. -/
theorem IsRenaming.lift {Δ Γ A ρ} (h : IsRenaming Δ Γ ρ) :
    IsRenaming (A :: Δ) (A :: Γ) (ModuleExpression.liftRen ρ) := by
  intro n hn
  cases n with
  | zero => exact ⟨Nat.succ_pos _, rfl⟩
  | succ n' =>
      have hn' : n' < Δ.length := by simpa using hn
      obtain ⟨hj, heq⟩ := h hn'
      refine ⟨by simpa [ModuleExpression.liftRen] using hj, ?_⟩
      simp only [ModuleExpression.liftRen, List.getElem_cons_succ]
      exact heq

/-- Renaming preserves typing along a context renaming. -/
theorem rename {m Δ T} (h : HasType m Δ T) :
    ∀ {Γ : ModuleContext} {ρ : Nat → Nat}, IsRenaming Δ Γ ρ → HasType (m.rename ρ) Γ T := by
  induction h with
  | proc p => intro Γ ρ _; exact .proc p
  | procHoles ne p => intro Γ ρ _; exact .procHoles ne p
  | var n hn =>
      intro Γ ρ hρ
      obtain ⟨hj, heq⟩ := hρ hn
      simp only [ModuleExpression.rename]
      rw [← heq]
      exact .var (ρ n) hj
  | app _ _ ihf iha => intro Γ ρ hρ; exact .app (ihf hρ) (iha hρ)
  | fst _ ihe => intro Γ ρ hρ; exact .fst (ihe hρ)
  | snd _ ihe => intro Γ ρ hρ; exact .snd (ihe hρ)
  | abs _ ihb => intro Γ ρ hρ; exact .abs (ihb hρ.lift)
  | pair _ _ iha ihb => intro Γ ρ hρ; exact .pair (iha hρ) (ihb hρ)
  | unit => intro Γ ρ _; exact .unit

/-- A substitution `σ` maps `Δ` into `Γ` if it sends every `Δ`-index to a `Γ`-typed term. -/
def IsSubst (Δ Γ : ModuleContext) (σ : Nat → ModuleExpression) : Prop :=
  ∀ {n} (h : n < Δ.length), HasType (σ n) Γ (Δ[n]'h)

/-- A well-typed substitution lifts under one binder to `liftSubst σ`. -/
theorem IsSubst.lift {Δ Γ A σ} (h : IsSubst Δ Γ σ) :
    IsSubst (A :: Δ) (A :: Γ) (ModuleExpression.liftSubst σ) := by
  intro n hn
  cases n with
  | zero =>
      simp only [ModuleExpression.liftSubst]
      exact HasType.var 0 (by simp)
  | succ n' =>
      have hn' : n' < Δ.length := by simpa using hn
      simp only [ModuleExpression.liftSubst, List.getElem_cons_succ]
      exact (h hn').rename isRenaming_succ

/-- Simultaneous substitution preserves typing along a well-typed substitution. -/
theorem substituteSimultaneously {m Δ T} (h : HasType m Δ T) :
    ∀ {Γ : ModuleContext} {σ : Nat → ModuleExpression},
      IsSubst Δ Γ σ → HasType (m.substituteSimultaneously σ) Γ T := by
  induction h with
  | proc p => intro Γ σ _; exact .proc p
  | procHoles ne p => intro Γ σ _; exact .procHoles ne p
  | var n hn => intro Γ σ hσ; exact hσ hn
  | app _ _ ihf iha => intro Γ σ hσ; exact .app (ihf hσ) (iha hσ)
  | fst _ ihe => intro Γ σ hσ; exact .fst (ihe hσ)
  | snd _ ihe => intro Γ σ hσ; exact .snd (ihe hσ)
  | abs _ ihb => intro Γ σ hσ; exact .abs (ihb hσ.lift)
  | pair _ _ iha ihb => intro Γ σ hσ; exact .pair (iha hσ) (ihb hσ)
  | unit => intro Γ σ _; exact .unit

/-- Single-variable substitution preserves typing (the β-substitution lemma). -/
theorem substitute {Δ u t body arg}
    (hb : HasType body (u :: Δ) t) (ha : HasType arg Δ u) :
    HasType (body.substitute arg) Δ t := by
  unfold ModuleExpression.substitute
  refine hb.substituteSimultaneously ?_
  intro n hn
  cases n with
  | zero => simpa [ModuleExpression.variableSubstitution] using ha
  | succ n' =>
      have hn' : n' < Δ.length := by simpa using hn
      simp only [ModuleExpression.variableSubstitution, List.getElem_cons_succ]
      exact .var n' hn'

/-- A term only mentions the variables its context declares, so a substitution that is the
    identity on those leaves it alone — whatever it does to the indices beyond `Δ`.  For a *closed*
    term (`Δ = []`) the hypothesis is vacuous: `Module.substituteSimultaneously_expression`. -/
theorem substituteSimultaneously_eq_self {m Δ T} (h : HasType m Δ T) :
    ∀ {σ : Nat → ModuleExpression}, (∀ n, n < Δ.length → σ n = .var n) →
      m.substituteSimultaneously σ = m := by
  induction h with
  | proc p => intro σ _; rfl
  | procHoles ne p => intro σ _; rfl
  | var n hn => intro σ hσ; exact hσ n hn
  | app _ _ ihf iha => intro σ hσ; simp [ModuleExpression.substituteSimultaneously, ihf hσ, iha hσ]
  | fst _ ihe => intro σ hσ; simp [ModuleExpression.substituteSimultaneously, ihe hσ]
  | snd _ ihe => intro σ hσ; simp [ModuleExpression.substituteSimultaneously, ihe hσ]
  | pair _ _ iha ihb => intro σ hσ; simp [ModuleExpression.substituteSimultaneously, iha hσ, ihb hσ]
  | unit => intro σ _; rfl
  | abs _ ihb =>
      intro σ hσ
      simp only [ModuleExpression.substituteSimultaneously]
      rw [ihb ?_]
      intro n hn
      cases n with
      | zero => rfl
      | succ n' =>
          simp [ModuleExpression.liftSubst, hσ n' (by simpa using hn), ModuleExpression.rename]

/-- **Type preservation** (subject reduction): reduction preserves the typing judgment.  This is
    the extrinsic replacement for what the intrinsic `TypedModules.ModuleExpression` guaranteed by
    construction. -/
theorem preservation {m m'} (hstep : m.ReductionStep m') :
    ∀ {Δ T}, HasType m Δ T → HasType m' Δ T := by
  induction hstep with
  | beta =>
      intro Δ T h
      obtain ⟨A, hf, ha⟩ := h.app_inv
      obtain ⟨A', B', harr, hbody⟩ := hf.abs_inv
      injection harr with hA hT
      subst hA; subst hT
      exact substitute hbody ha
  | appL _ ih => intro Δ T h; obtain ⟨A, hf, ha⟩ := h.app_inv; exact .app (ih hf) ha
  | appR _ ih => intro Δ T h; obtain ⟨A, hf, ha⟩ := h.app_inv; exact .app hf (ih ha)
  | lam _ ih =>
      intro Δ T h
      obtain ⟨A, B, hT, hbody⟩ := h.abs_inv
      subst hT; exact .abs (ih hbody)
  | pairL _ ih =>
      intro Δ T h
      obtain ⟨A, B, hT, ha, hb⟩ := h.pair_inv
      subst hT; exact .pair (ih ha) hb
  | pairR _ ih =>
      intro Δ T h
      obtain ⟨A, B, hT, ha, hb⟩ := h.pair_inv
      subst hT; exact .pair ha (ih hb)
  | fstPair =>
      intro Δ T h
      obtain ⟨B, hp⟩ := h.fst_inv
      obtain ⟨A2, B2, hTp, ha, hb⟩ := hp.pair_inv
      injection hTp with h1 h2; subst h1; exact ha
  | fst _ ih => intro Δ T h; obtain ⟨B, hp⟩ := h.fst_inv; exact .fst (ih hp)
  | sndPair =>
      intro Δ T h
      obtain ⟨A, hp⟩ := h.snd_inv
      obtain ⟨A2, B2, hTp, ha, hb⟩ := hp.pair_inv
      injection hTp with h1 h2; subst h2; exact hb
  | snd _ ih => intro Δ T h; obtain ⟨A, hp⟩ := h.snd_inv; exact .snd (ih hp)
  | delta ne proc inst =>
      intro Δ T h
      obtain ⟨A, hf, _⟩ := h.app_inv
      have hT := hf.procHoles_inv
      injection hT with _ hTeq
      subst hTeq
      exact .proc _

end ModuleExpression.HasType

def IsProcArgType : ModuleTypeRep → Prop
  | .unit => True
  | .prod (.proc _) rest => IsProcArgType rest
  | _ => False

/-! ## Normal forms on the untyped tree

Untyped analogues of `IsProcHoles`/`IsProcTuple`/`Normal`/`Neutral`/`NormalClosed`.  Permanent;
mirror the intrinsic versions structurally. -/

namespace ModuleExpression

/-- `m` is a right-nested tuple of hole-free procedures (`.unit`, or `.pair (.proc _) rest`
    with `IsProcTuple rest`) — the ground arguments a procedure-with-holes accepts. -/
def IsProcTuple : ModuleExpression → Prop
  | .unit               => True
  | .pair (.proc _) rest => IsProcTuple rest
  | _                   => False

instance instDecidableIsProcTuple : (m : ModuleExpression) → Decidable (IsProcTuple m)
  | .unit => isTrue trivial
  | .pair a rest =>
      match a with
      | .proc _ =>
          match instDecidableIsProcTuple rest with
          | isTrue h => isTrue h
          | isFalse h => isFalse h
      | .unit | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .procHoles _ _ =>
          isFalse (by simp [IsProcTuple])
  | .proc _ | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .procHoles _ _ =>
      isFalse (by simp [IsProcTuple])


mutual

/-- Beta-normal form: no redex anywhere. -/
inductive Normal : ModuleExpression → Prop where
  | neutral {e} : Neutral e → Normal e
  | abs {body} : Normal body → Normal (.abs body)
  | pair {a b} : Normal a → Normal b → Normal (.pair a b)
  | proc {sig} {p : Procedure sig} : Normal (.proc p)
  | procHoles {holes sig} {ne : holes.NonEmpty} {p : ProcedureWithHoles holes sig} :
      Normal (.procHoles ne p)
  | unit : Normal .unit

/-- Neutral form: no outermost redex — the head is a variable, or a procedure-with-holes
    applied to a normal non-proc-tuple (so the δ-rule is stuck). -/
inductive Neutral : ModuleExpression → Prop where
  | var {n} : Neutral (.var n)
  | app {f arg} : Neutral f → Normal arg → Neutral (.app f arg)
  | appProcHoles {holes sig arg} {p : ProcedureWithHoles holes sig} (ne : holes.NonEmpty) :
       Normal arg → ¬ IsProcTuple arg → Neutral (.app (.procHoles ne p) arg)
  | fst {e} : Neutral e → Neutral (.fst e)
  | snd {e} : Neutral e → Neutral (.snd e)

end

/-- Joint decidability of `Normal`/`Neutral`, sharing one structural recursion (untyped port of
    `TypedModules.decidableNormalNeutral`). -/
private def decidableNormalNeutral (m : ModuleExpression) :
    Decidable (Normal m) × Decidable (Neutral m) :=
  match m with
  | .unit => ⟨.isTrue .unit, .isFalse fun h => nomatch h⟩
  | .var _  => ⟨.isTrue (.neutral .var), .isTrue .var⟩
  | .proc _ => ⟨.isTrue .proc, .isFalse fun h => nomatch h⟩
  | .procHoles _ _ => ⟨.isTrue .procHoles, .isFalse fun h => nomatch h⟩
  | .abs body =>
      match (decidableNormalNeutral body).1 with
      | .isTrue hn   => ⟨.isTrue (.abs hn), .isFalse fun h => nomatch h⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .abs hb => hb | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .pair a b =>
      match (decidableNormalNeutral a).1, (decidableNormalNeutral b).1 with
      | .isTrue ha, .isTrue hb =>
          ⟨.isTrue (.pair ha hb), .isFalse fun h => nomatch h⟩
      | .isFalse ha, _ =>
          ⟨.isFalse fun h => ha (match h with | .pair hp _ => hp | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
      | .isTrue _, .isFalse hb =>
          ⟨.isFalse fun h => hb (match h with | .pair _ hq => hq | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .app f arg => by
      have df := decidableNormalNeutral f
      have da := decidableNormalNeutral arg
      have dN : Decidable (Neutral (.app f arg)) := by
        match df.2, da.1 with
        | .isTrue nf, .isTrue na => exact .isTrue (.app nf na)
        | _, .isFalse na =>
            exact .isFalse fun h => by
              cases h with
              | app _ na' => exact na na'
              | appProcHoles _ na' _ => exact na na'
        | .isFalse nf, .isTrue na =>
            match f, nf with
            | .procHoles ne p, nf =>
                match instDecidableIsProcTuple arg with
                | .isFalse hpt => exact .isTrue (.appProcHoles ne na hpt)
                | .isTrue hpt =>
                    exact .isFalse fun h => by
                      cases h with
                      | app nf' _ => exact nf nf'
                      | appProcHoles _ _ hpt' => exact hpt' hpt
            | .proc _, nf | .var _, nf | .app _ _, nf | .fst _, nf | .snd _, nf
            | .abs _, nf | .pair _ _, nf | .unit, nf =>
                exact .isFalse fun h => by
                  cases h with
                  | app nf' _ => exact nf nf'
      exact ⟨(match dN with
              | .isTrue h => .isTrue (.neutral h)
              | .isFalse h =>
                  .isFalse fun hn => by cases hn with | neutral hne => exact h hne), dN⟩
  | .fst e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.fst hn)), .isTrue (.fst hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.fst he) => he),
           .isFalse fun h => hnn (match h with | .fst he => he)⟩
  | .snd e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.snd hn)), .isTrue (.snd hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.snd he) => he),
           .isFalse fun h => hnn (match h with | .snd he => he)⟩

instance (m : ModuleExpression) : Decidable (Normal m) := (decidableNormalNeutral m).1
instance (m : ModuleExpression) : Decidable (Neutral m) := (decidableNormalNeutral m).2

/-- Normal form of a closed term.  Neutral terms cannot occur closed (they need a free
    variable), so there are fewer cases than `Normal`; the `abs` body is still general
    `Normal` (it lives under one binder). -/
inductive NormalClosed : ModuleExpression → Prop where
  | proc {sig} {p : Procedure sig} : NormalClosed (.proc p)
  | procHoles {holes sig} {ne : holes.NonEmpty} {p : ProcedureWithHoles holes sig} :
      NormalClosed (.procHoles ne p)
  | abs {body} : Normal body → NormalClosed (.abs body)
  | pair {a b} : NormalClosed a → NormalClosed b → NormalClosed (.pair a b)
  | unit : NormalClosed .unit

omit [ProgramSpec] in
/-- A hole-signature's argument tuple type is always a procedure-argument type. -/
private theorem toModuleTypeRepTuple_isProcArgType (holes : HoleSigs) :
    IsProcArgType (HoleSigs.toModuleTypeRepTuple holes) := by
  induction holes with
  | empty => simp [HoleSigs.toModuleTypeRepTuple, IsProcArgType]
  | append rest sig ih => exact ih


/-- Progress for the closed fragment: a well-typed closed term is never neutral, and a closed
    normal term of procedure-argument type is a procedure tuple.  Untyped port of
    `TypedModules.closed_progress`; the intrinsic index becomes an explicit `HasType` hypothesis. -/
private theorem closedProgress : ∀ {m : ModuleExpression} {T},
    m.HasType [] T → (¬ Neutral m) ∧ (IsProcArgType T → Normal m → IsProcTuple m) := by
  intro m
  induction m with
  | unit => intro T hty; exact ⟨(fun hne => nomatch hne), fun _ _ => trivial⟩
  | proc p =>
      intro T hty; obtain rfl := hty.proc_inv
      exact ⟨(fun hne => nomatch hne), fun ht _ => absurd ht (by simp [IsProcArgType])⟩
  | procHoles ne p =>
      intro T hty; obtain rfl := hty.procHoles_inv
      exact ⟨(fun hne => nomatch hne), fun ht _ => absurd ht (by simp [IsProcArgType])⟩
  | var n =>
      intro T hty; obtain ⟨i, _⟩ := hty.var_inv; exact nomatch i
  | app f arg ihf iharg =>
      intro T hty
      obtain ⟨A, hf, harg⟩ := hty.app_inv
      have h1 : ¬ Neutral (.app f arg) := by
        intro hne
        cases hne with
        | app nf _ => exact (ihf hf).1 nf
        | appProcHoles hph ha hpt =>
            have he := hf.procHoles_inv
            rw [ModuleTypeRep.arr.injEq] at he
            obtain ⟨rfl, _⟩ := he
            exact hpt ((iharg harg).2 (toModuleTypeRepTuple_isProcArgType _) ha)
      exact ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | fst e ihe =>
      intro T hty
      obtain ⟨B, he⟩ := hty.fst_inv
      have h1 : ¬ Neutral (.fst e) := by
        intro hne; cases hne with | fst ne => exact (ihe he).1 ne
      exact ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | snd e ihe =>
      intro T hty
      obtain ⟨A, he⟩ := hty.snd_inv
      have h1 : ¬ Neutral (.snd e) := by
        intro hne; cases hne with | snd ne => exact (ihe he).1 ne
      exact ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | abs body ihb =>
      intro T hty
      obtain ⟨A, B, rfl, _⟩ := hty.abs_inv
      exact ⟨(fun hne => nomatch hne), fun ht _ => absurd ht (by simp [IsProcArgType])⟩
  | pair a b iha ihb =>
      intro T hty
      obtain ⟨A, B, rfl, ha, hb⟩ := hty.pair_inv
      refine ⟨(fun hne => nomatch hne), fun ht hn => ?_⟩
      cases hn with
      | neutral hne => exact nomatch hne
      | pair hpa hpb =>
          cases a with
          | unit => obtain rfl := ha.unit_inv; simp [IsProcArgType] at ht
          | proc p => obtain rfl := ha.proc_inv; exact (ihb hb).2 ht hpb
          | var r => obtain ⟨i, _⟩ := ha.var_inv; exact nomatch i
          | app _ _ => cases hpa with | neutral hne => exact absurd hne (iha ha).1
          | fst _ => cases hpa with | neutral hne => exact absurd hne (iha ha).1
          | snd _ => cases hpa with | neutral hne => exact absurd hne (iha ha).1
          | abs _ => obtain ⟨A', B', rfl, _⟩ := ha.abs_inv; simp [IsProcArgType] at ht
          | procHoles _ _ => obtain rfl := ha.procHoles_inv; simp [IsProcArgType] at ht
          | pair _ _ => obtain ⟨A', B', rfl, _, _⟩ := ha.pair_inv; simp [IsProcArgType] at ht


/- /-! #### Type erasure (untyped analogue)

On the untyped tree `erasedEqual` coincides with equality; the family is kept to mirror `TypedModules`. -/

-- TODO remove whole section

/-- Structural "erased equality": equal up to the (already-absent) type indices. -/
def erasedEqual : ModuleExpression → ModuleExpression → Prop
  | .proc p, .proc p' => p ≍ p'
  | .procHoles _ p, .procHoles _ p' => p ≍ p'
  | .var r, .var r' => r = r'
  | .app f a, .app f' a' => erasedEqual f f' ∧ erasedEqual a a'
  | .fst e, .fst e' => erasedEqual e e'
  | .snd e, .snd e' => erasedEqual e e'
  | .pair a b, .pair a' b' => erasedEqual a a' ∧ erasedEqual b b'
  | .abs body, .abs body' => erasedEqual body body'
  | .unit, .unit => True
  | _, _ => False

theorem erasedEqual_refl (m : ModuleExpression) : erasedEqual m m := by
  induction m with
  | unit => trivial
  | proc => exact HEq.refl _
  | procHoles => exact HEq.refl _
  | var r => simp [erasedEqual]
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | fst e ih => exact ih
  | snd e ih => exact ih
  | pair a b iha ihb => exact ⟨iha, ihb⟩
  | abs body ih => exact ih

theorem erasedEqual_pair_right (a : ModuleExpression) {b b' : ModuleExpression}
    (h : erasedEqual b b') : erasedEqual (.pair a b) (.pair a b') :=
  ⟨erasedEqual_refl a, h⟩

theorem erasedEqual_pair_left {a a' : ModuleExpression} (b : ModuleExpression)
    (h : erasedEqual a a') : erasedEqual (.pair a b) (.pair a' b) :=
  ⟨h, erasedEqual_refl b⟩
 -/

/-! #### Embedding into `Metatheory.STLCext` -/

private scoped instance instModuleExpressionSTLCspec : Metatheory.STLCext.STLCspec where
  baseTypes := ProcedureSignature
  baseTypeValue := fun sig => { s : ProcedureSignature // s = sig } × Procedure sig
  funcData := Σ holes : HoleSigs, Σ sig : ProcedureSignature, ProcedureWithHoles holes sig

/-- Erase a `ModuleTypeRep` to an STLC type (untyped port of `TypedModules.ModuleTypeRep.toSTLC`;
    `TypedModules`'s homonym is `private`, so it gets a hygienic mangled name and does not clash). -/
private def ModuleTypeRep.toSTLC : ModuleTypeRep → Metatheory.STLCext.Ty
  | .prod A B => .prod (ModuleTypeRep.toSTLC A) (ModuleTypeRep.toSTLC B)
  | .arr A B => .arr (ModuleTypeRep.toSTLC A) (ModuleTypeRep.toSTLC B)
  | .proc sig => .base sig
  | .unit => .unit

private theorem toModuleTypeRepTuple_isArrowFree (holes : HoleSigs) :
    (ModuleTypeRep.toSTLC (HoleSigs.toModuleTypeRepTuple holes)).isArrowFree := by
  induction holes with
  | empty => simp [HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC, Metatheory.STLCext.Ty.isArrowFree]
  | append _ _ ih =>
      simp [HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC, Metatheory.STLCext.Ty.isArrowFree, ih]

open Metatheory.STLCext in
private def basicTermHoleLookup : (holes : HoleSigs) →
    BasicTerm (ModuleTypeRep.toSTLC (HoleSigs.toModuleTypeRepTuple holes)) → holes.Instantiation
  | .empty, _ => fun n => nomatch n
  | .append Γ _, .pair (.value v) rest => fun n =>
      match n with
      | .zero   => v.2
      | .succ m => basicTermHoleLookup Γ rest m

open Metatheory.STLCext in
private noncomputable def pwhToSTLC {holes sig}
    (proc : ProcedureWithHoles holes sig) : Term :=
    let inputType := ModuleTypeRep.toSTLC (HoleSigs.toModuleTypeRepTuple holes)
    let outputType := ModuleTypeRep.toSTLC (ModuleTypeRep.proc sig)
    let inputArrowFree : inputType.isArrowFree := toModuleTypeRepTuple_isArrowFree holes
    let outputArrowFree : outputType.isArrowFree := by
      simp [outputType, ModuleTypeRep.toSTLC, Metatheory.STLCext.Ty.isArrowFree]
    let substitution : BasicTerm inputType → BasicTerm outputType :=
      fun basicTerm => .value (⟨sig, rfl⟩, proc.instantiate (basicTermHoleLookup holes basicTerm))
    .func (t := inputType) (u := outputType)
      (ht := inputArrowFree) (hu := outputArrowFree) ⟨holes, sig, proc⟩ substitution

private noncomputable def toSTLC : ModuleExpression → Metatheory.STLCext.Term
  | .unit => .unit
  | .proc (sig := sig) p => .value (⟨sig, rfl⟩, p)
  | .procHoles _ p => pwhToSTLC p
  | .var n => .var n
  | .app M N => .app (toSTLC M) (toSTLC N)
  | .fst M => .fst (toSTLC M)
  | .snd M => .snd (toSTLC M)
  | .abs M => .lam (toSTLC M)
  | .pair M N => .pair (toSTLC M) (toSTLC N)

private def ModuleContext.toSTLC : ModuleContext → Metatheory.STLCext.Context
  | [] => []
  | T :: Γ => ModuleTypeRep.toSTLC T :: ModuleContext.toSTLC Γ

private theorem ModuleContext.toSTLC_getElem {Δ : ModuleContext} {n} (h : n < Δ.length) :
    (ModuleContext.toSTLC Δ)[n]? = some (ModuleTypeRep.toSTLC (Δ[n]'h)) := by
  induction Δ generalizing n with
  | nil => simp only [List.length_nil] at h; omega
  | cons T Γ ih =>
      cases n with
      | zero => simp [ModuleContext.toSTLC]
      | succ n' =>
          have hn' : n' < Γ.length := by simpa using h
          simp only [ModuleContext.toSTLC, List.getElem_cons_succ]
          exact ih hn'

private theorem toSTLC_rename_shift (d : Nat) (m : ModuleExpression) :
    ∀ (c : Nat) (ρ : Nat → Nat)
      (_ : ∀ r, r < c → ρ r = r) (_ : ∀ r, r ≥ c → ρ r = r + d),
      toSTLC (m.rename ρ) = Metatheory.STLCext.Term.shift d c (toSTLC m) := by
  induction m with
  | proc p => intro c ρ _ _; rfl
  | procHoles ne p =>
      intro c ρ _ _; simp only [rename, toSTLC, pwhToSTLC, Metatheory.STLCext.Term.shift]
  | var n =>
      intro c ρ h1 h2
      simp only [rename, toSTLC, Metatheory.STLCext.Term.shift]
      by_cases hn : n < c
      · rw [if_pos hn, h1 n hn]
      · rw [if_neg hn, h2 n (Nat.le_of_not_lt hn)]; congr 1
  | app f a ihf iha =>
      intro c ρ h1 h2
      simp only [rename, toSTLC, Metatheory.STLCext.Term.shift, ihf c ρ h1 h2, iha c ρ h1 h2]
  | fst e ih =>
      intro c ρ h1 h2
      simp only [rename, toSTLC, Metatheory.STLCext.Term.shift, ih c ρ h1 h2]
  | snd e ih =>
      intro c ρ h1 h2
      simp only [rename, toSTLC, Metatheory.STLCext.Term.shift, ih c ρ h1 h2]
  | abs body ih =>
      intro c ρ h1 h2
      simp only [rename, toSTLC, Metatheory.STLCext.Term.shift]
      rw [ih (c + 1) (liftRen ρ) ?lt ?ge]
      case lt =>
        intro r hr; cases r with
        | zero => rfl
        | succ k => simp only [liftRen]; rw [h1 k (by omega)]
      case ge =>
        intro r hr; cases r with
        | zero => omega
        | succ k => simp only [liftRen]; rw [h2 k (by omega)]; omega
  | pair a b iha ihb =>
      intro c ρ h1 h2
      simp only [rename, toSTLC, Metatheory.STLCext.Term.shift, iha c ρ h1 h2, ihb c ρ h1 h2]
  | unit => intro c ρ _ _; rfl

private theorem toSTLC_substAll_level (N_stlc : Metatheory.STLCext.Term) (m : ModuleExpression) :
    ∀ (k : Nat) (σ : Nat → ModuleExpression)
      (_ : ∀ r, toSTLC (σ r) = Metatheory.STLCext.Term.subst k
              (Metatheory.STLCext.Term.shift k 0 N_stlc) (Metatheory.STLCext.Term.var r)),
      toSTLC (m.substituteSimultaneously σ) = Metatheory.STLCext.Term.subst k
        (Metatheory.STLCext.Term.shift k 0 N_stlc) (toSTLC m) := by
  induction m with
  | unit => intros; simp [substituteSimultaneously, toSTLC, Metatheory.STLCext.Term.subst]
  | proc p => intros; simp [substituteSimultaneously, toSTLC, Metatheory.STLCext.Term.subst]
  | procHoles ne p =>
      intros
      simp [substituteSimultaneously, toSTLC, pwhToSTLC, Metatheory.STLCext.Term.subst]
  | var r => intro k σ hσ; simp [substituteSimultaneously, toSTLC, hσ]
  | app f a ihf iha =>
      intro k σ hσ
      simp [substituteSimultaneously, toSTLC, Metatheory.STLCext.Term.subst, ihf k σ hσ, iha k σ hσ]
  | fst e ih =>
      intro k σ hσ
      simp [substituteSimultaneously, toSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | snd e ih =>
      intro k σ hσ
      simp [substituteSimultaneously, toSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | pair a b iha ihb =>
      intro k σ hσ
      simp [substituteSimultaneously, toSTLC, Metatheory.STLCext.Term.subst, iha k σ hσ, ihb k σ hσ]
  | abs body ih =>
      intro k σ hσ
      simp only [substituteSimultaneously, toSTLC, Metatheory.STLCext.Term.subst]
      congr 1
      have hshift : (Metatheory.STLCext.Term.shift k 0 N_stlc).shift1 =
          Metatheory.STLCext.Term.shift (k + 1) 0 N_stlc := by
        simp only [Metatheory.STLCext.Term.shift1]
        rw [show (1 : Int) = ((1 : Nat) : Int) from by norm_num,
            Metatheory.STLCext.Term.shift_shift]
        congr 1; omega
      rw [hshift]
      apply ih (k + 1) (liftSubst σ)
      intro r
      cases r with
      | zero =>
        simp only [liftSubst, toSTLC, Metatheory.STLCext.Term.subst]
        simp [show ¬ (0 : Nat) > k + 1 from Nat.not_lt.mpr (Nat.zero_le _)]
      | succ r' =>
        simp only [liftSubst]
        rw [toSTLC_rename_shift 1 (σ r') 0 Nat.succ
          (fun r hr => absurd hr (Nat.not_lt.mpr (Nat.zero_le _)))
          (fun r _ => rfl)]
        rw [hσ r']
        have key := Metatheory.STLCext.Term.shift1_subst
            (Metatheory.STLCext.Term.var r')
            (Metatheory.STLCext.Term.shift (↑k) 0 N_stlc) k
        simp only [Metatheory.STLCext.Term.shift1] at key hshift
        rw [show (↑(1 : Nat) : Int) = (1 : Int) from by norm_cast, key, hshift]
        simp only [Metatheory.STLCext.Term.shift,
                   show ¬ (r' < (0 : Nat)) from Nat.not_lt.mpr (Nat.zero_le _), ite_false]
        norm_cast

private theorem toSTLC_subst (body arg : ModuleExpression) :
    toSTLC (body.substitute arg) =
    Metatheory.STLCext.Term.subst0 (toSTLC arg) (toSTLC body) := by
  simp only [substitute]
  rw [toSTLC_substAll_level (toSTLC arg) body 0 (variableSubstitution arg)]
  · simp [Metatheory.STLCext.Term.shift_zero]
  · intro r
    cases r with
    | zero =>
      simp only [variableSubstitution, Metatheory.STLCext.Term.subst]
      simp [Metatheory.STLCext.Term.shift_zero]
    | succ r' =>
      simp only [variableSubstitution, toSTLC, Metatheory.STLCext.Term.subst]
      simp [show r' + 1 > 0 from Nat.succ_pos _]

private def isBasicType_toModuleTuple {holes : HoleSigs} (inst : holes.Instantiation) :
    Metatheory.STLCext.Term.isBasicType (ModuleTypeRep.toSTLC (HoleSigs.toModuleTypeRepTuple holes))
        (toSTLC (HoleSigs.Instantiation.toModuleExpr inst)) := by
  induction holes with
  | empty => trivial
  | append holeTail sig ih => exact ⟨rfl, ih (fun idx => inst (.succ idx))⟩

private def basicTermHoleLookup_toModuleTuple {holes : HoleSigs} (inst : holes.Instantiation)
    {sig : ProcedureSignature} (n : HoleIndex holes sig) :
    basicTermHoleLookup holes
      (Metatheory.STLCext.Term.toBasicTerm _ _ (isBasicType_toModuleTuple inst)) n = inst n := by
  induction holes with
  | empty => exact nomatch n
  | append holeTail sig' ih =>
      cases n with
      | zero => rfl
      | succ m => exact ih (fun idx => inst (.succ idx)) m

private theorem StmtWithHoles.instantiate_congr_of_agree {holes : HoleSigs} {l : Type}
    (s : StmtWithHoles holes l) {f g : holes.Instantiation}
    (h : ∀ {sig} (n : HoleIndex holes sig), f n = g n) :
    s.instantiate f = s.instantiate g := by
  induction s with
  | hole n _ _ => simp only [StmtWithHoles.instantiate]; rw [h n]
  | seq _ _ ih1 ih2 => simp only [StmtWithHoles.instantiate]; rw [ih1 h, ih2 h]
  | ifThenElse _ _ _ iht ihe => simp only [StmtWithHoles.instantiate]; rw [iht h, ihe h]
  | «while» _ _ ihb => simp only [StmtWithHoles.instantiate]; rw [ihb h]
  | _ => rfl

private theorem instantiate_congr {holes : HoleSigs} (args : holes.Instantiation)
    {sig : ProcedureSignature} (proc : ProcedureWithHoles holes sig) :
    proc.instantiate (basicTermHoleLookup holes
      (Metatheory.STLCext.Term.toBasicTerm _ _ (isBasicType_toModuleTuple args)))
    = proc.instantiate args := by
  obtain ⟨_, body, _⟩ := proc
  simp only [ProcedureWithHoles.instantiate]
  congr 1
  exact StmtWithHoles.instantiate_congr_of_agree body
    (fun n => basicTermHoleLookup_toModuleTuple args n)

private theorem toModuleTuple_of_basicType {holes : HoleSigs} (arg : ModuleExpression)
    (h : Metatheory.STLCext.Term.isBasicType
      (ModuleTypeRep.toSTLC (HoleSigs.toModuleTypeRepTuple holes)) (toSTLC arg)) :
    HoleSigs.Instantiation.toModuleExpr
      (basicTermHoleLookup holes (Metatheory.STLCext.Term.toBasicTerm _ _ h)) = arg := by
  induction holes generalizing arg with
  | empty =>
      cases arg with
      | unit => rfl
      | proc _ | procHoles _ _ | var _ | app _ _ | fst _ | snd _ | abs _ | pair _ _ =>
          simp only [toSTLC, pwhToSTLC, ModuleTypeRep.toSTLC, HoleSigs.toModuleTypeRepTuple,
            Metatheory.STLCext.Term.isBasicType] at h
  | append holeTail sig ih =>
      cases arg with
      | pair a rest =>
          cases a with
          | proc p =>
              obtain ⟨h1, h2⟩ := h
              simp only [toSTLC, ModuleTypeRep.toSTLC, Metatheory.STLCext.Term.isBasicType] at h1
              subst h1
              exact congrArg (ModuleExpression.pair (.proc p)) (ih rest h2)
          | procHoles _ _ | var _ | app _ _ | fst _ | snd _ | abs _ | pair _ _ | unit =>
              simp only [toSTLC, pwhToSTLC, ModuleTypeRep.toSTLC, HoleSigs.toModuleTypeRepTuple,
                Metatheory.STLCext.Term.isBasicType, false_and] at h
      | proc _ | procHoles _ _ | var _ | app _ _ | fst _ | snd _ | abs _ | unit =>
          simp only [toSTLC, pwhToSTLC, ModuleTypeRep.toSTLC, HoleSigs.toModuleTypeRepTuple,
            Metatheory.STLCext.Term.isBasicType] at h

private theorem reductionStep_stlc_compat (m m' : ModuleExpression) (h : m.ReductionStep m') :
    Metatheory.STLCext.Step (toSTLC m) (toSTLC m') := by
  induction h with
  | beta => simp only [toSTLC]; rw [toSTLC_subst]; exact .beta _ _
  | appL _ ih => simp only [toSTLC]; exact .appL ih
  | appR _ ih => simp only [toSTLC]; exact .appR ih
  | lam _ ih => simp only [toSTLC]; exact .lam ih
  | pairL _ ih => simp only [toSTLC]; exact .pairL ih
  | pairR _ ih => simp only [toSTLC]; exact .pairR ih
  | fstPair => simp only [toSTLC]; exact .fstPair _ _
  | fst _ ih => simp only [toSTLC]; exact .fst ih
  | sndPair => simp only [toSTLC]; exact .sndPair _ _
  | snd _ ih => simp only [toSTLC]; exact .snd ih
  | delta ne proc inst =>
      simp only [toSTLC, pwhToSTLC]
      rw [(instantiate_congr inst proc).symm]
      exact Metatheory.STLCext.Step.funcApp _ _ _ (isBasicType_toModuleTuple inst)

private theorem toSTLC_hasType {m : ModuleExpression} {Δ T} (h : m.HasType Δ T) :
    Metatheory.STLCext.HasType (ModuleContext.toSTLC Δ) (toSTLC m) (ModuleTypeRep.toSTLC T) := by
  induction h with
  | proc p => simp only [toSTLC]; exact Metatheory.STLCext.HasType.value _
  | procHoles ne p => exact Metatheory.STLCext.HasType.func _ _
  | app _ _ ihm ihn => simp only [toSTLC]; exact Metatheory.STLCext.HasType.app ihm ihn
  | fst _ ih => simp only [toSTLC]; exact Metatheory.STLCext.HasType.fst ih
  | snd _ ih => simp only [toSTLC]; exact Metatheory.STLCext.HasType.snd ih
  | abs _ ih =>
      simp only [toSTLC, ModuleTypeRep.toSTLC, ModuleContext.toSTLC] at *
      exact Metatheory.STLCext.HasType.lam ih
  | pair _ _ ihm ihn => simp only [toSTLC]; exact Metatheory.STLCext.HasType.pair ihm ihn
  | unit => exact Metatheory.STLCext.HasType.unit
  | var n hn =>
      simp only [toSTLC]
      exact Metatheory.STLCext.HasType.var (ModuleContext.toSTLC_getElem hn)

private theorem reductionStep_stlc_complete (m : ModuleExpression) (M' : Metatheory.STLCext.Term)
    (h : Metatheory.STLCext.Step (toSTLC m) M') :
    ∃ m', m.ReductionStep m' ∧ toSTLC m' = M' := by
  induction m generalizing M' with
  | unit | proc _ | procHoles _ _ | var _ => simp only [toSTLC] at h; cases h
  | app f arg ihf iharg =>
      cases f with
      | abs body =>
          simp only [toSTLC] at h
          cases h with
          | beta => exact ⟨substitute body arg, .beta, toSTLC_subst body arg⟩
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp only [toSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.abs body) arg', .appR hnd, by simp only [toSTLC, heq]⟩
      | procHoles ne proc =>
          simp only [toSTLC, pwhToSTLC] at h
          cases h with
          | appL step => nomatch step
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.procHoles ne proc) arg', .appR hnd, by simp only [toSTLC, pwhToSTLC, heq]⟩
          | funcApp d g N hbasic =>
              refine ⟨.proc (proc.instantiate (basicTermHoleLookup _
                  (Metatheory.STLCext.Term.toBasicTerm _ _ hbasic))), ?_, rfl⟩
              exact Eq.subst
                (motive := fun x => ReductionStep (.app (.procHoles ne proc) x)
                  (.proc (proc.instantiate (basicTermHoleLookup _
                    (Metatheory.STLCext.Term.toBasicTerm _ _ hbasic)))))
                (toModuleTuple_of_basicType arg hbasic)
                (ReductionStep.delta ne proc _)
      | proc _ | var _ | app _ _ | fst _ | snd _ | pair _ _ | unit =>
          simp only [toSTLC] at h
          cases h with
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp only [toSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app _ arg', .appR hnd, by simp only [toSTLC, heq]⟩
  | abs body ih =>
      simp only [toSTLC] at h
      cases h with
      | lam step =>
          obtain ⟨body', hnd, heq⟩ := ih _ step
          exact ⟨.abs body', .lam hnd, by simp only [toSTLC, heq]⟩
  | pair a b iha ihb =>
      simp only [toSTLC] at h
      cases h with
      | pairL step =>
          obtain ⟨a', hnd, heq⟩ := iha _ step
          exact ⟨.pair a' b, .pairL hnd, by simp only [toSTLC, heq]⟩
      | pairR step =>
          obtain ⟨b', hnd, heq⟩ := ihb _ step
          exact ⟨.pair a b', .pairR hnd, by simp only [toSTLC, heq]⟩
  | fst e ih =>
      cases e with
      | pair e1 e2 =>
          simp only [toSTLC] at h
          cases h with
          | fstPair => exact ⟨e1, .fstPair, rfl⟩
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp only [toSTLC, heq]⟩
      | proc _ | procHoles _ _ | var _ | app _ _ | fst _ | snd _ | abs _ | unit =>
          simp only [toSTLC] at h
          cases h with
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp only [toSTLC, heq]⟩
  | snd e ih =>
      cases e with
      | pair e1 e2 =>
          simp only [toSTLC] at h
          cases h with
          | sndPair => exact ⟨e2, .sndPair, rfl⟩
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp only [toSTLC, heq]⟩
      | proc _ | procHoles _ _ | var _ | app _ _ | fst _ | snd _ | abs _ | unit =>
          simp only [toSTLC] at h
          cases h with
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp only [toSTLC, heq]⟩

private theorem multiStepReduction_to_stlc_star {m m' : ModuleExpression}
    (h : m.MultiStepReduction m') :
    Rewriting.Star Metatheory.STLCext.Step (toSTLC m) (toSTLC m') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (reductionStep_stlc_compat _ _ hbc)

private theorem toSTLC_normal_isNormalForm {m : ModuleExpression} :
    Normal m → Rewriting.IsNormalForm Metatheory.STLCext.Step (toSTLC m) := by
  · intro hm
    have tuple_isProcTuple : ∀ {hh : HoleSigs} (i : hh.Instantiation),
        (HoleSigs.Instantiation.toModuleExpr i).IsProcTuple := by
      intro hh i
      induction hh with
      | empty => simp [HoleSigs.Instantiation.toModuleExpr, IsProcTuple]
      | append _ _ ih => simp only [HoleSigs.Instantiation.toModuleExpr]; exact ih _
    suffices key : ∀ (m' : ModuleExpression),
        (Normal m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (toSTLC m')) ∧
        (Neutral m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (toSTLC m') ∧
                     (∀ body, toSTLC m' ≠ Metatheory.STLCext.Term.lam body) ∧
                     (∀ P Q, toSTLC m' ≠ Metatheory.STLCext.Term.pair P Q)) from
      (key m).1 hm
    intro m'
    induction m' with
    | unit =>
      refine ⟨fun _ N h => ?_, fun hne => nomatch hne⟩
      simp only [toSTLC] at h; cases h
    | var n =>
      constructor
      · intro _ N h; simp only [toSTLC] at h; cases h
      · intro _; refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
        · simp only [toSTLC] at h; cases h
        · intro h; cases h
        · intro h; cases h
    | proc _ | procHoles _ _ =>
      refine ⟨fun _ N h => ?_, fun h => by cases h⟩
      simp only [toSTLC, pwhToSTLC] at h; cases h
    | abs body ih =>
      refine ⟨fun hn N h => ?_, fun h => nomatch h⟩
      simp only [toSTLC] at h
      cases hn with
      | neutral hne => exact nomatch hne
      | abs hb => cases h with | lam step => exact (ih.1 hb) _ step
    | pair a b iha ihb =>
      refine ⟨fun hn N h => ?_, fun h => nomatch h⟩
      simp only [toSTLC] at h
      cases hn with
      | neutral hne => exact nomatch hne
      | pair ha hb =>
        cases h with
        | pairL step => exact (iha.1 ha) _ step
        | pairR step => exact (ihb.1 hb) _ step
    | app f arg ihf iharg =>
      constructor
      · intro hn N h
        simp only [toSTLC] at h
        cases hn with
        | neutral hne =>
          cases hne with
          | app hf_n harg_n =>
            obtain ⟨ihf_step, ihf_lam, _⟩ := ihf.2 hf_n
            generalize hF : toSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [toSTLC] at hF
          | appProcHoles hph ha hpt =>
            simp only [toSTLC, pwhToSTLC] at h
            cases h with
            | appL step => nomatch step
            | appR step => exact (iharg.1 ha) _ step
            | funcApp d g N' hbasic =>
                exact absurd
                  (toModuleTuple_of_basicType arg hbasic ▸ tuple_isProcTuple _) hpt
      · intro hne
        cases hne with
        | app hf_n harg_n =>
          obtain ⟨ihf_step, ihf_lam, ihf_pair⟩ := ihf.2 hf_n
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [toSTLC] at h
            generalize hF : toSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [toSTLC] at hF
          · intro h; cases h
          · intro h; cases h
        | appProcHoles hph ha hpt =>
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [toSTLC, pwhToSTLC] at h
            cases h with
            | appL step => nomatch step
            | appR step => exact (iharg.1 ha) _ step
            | funcApp d g N' hbasic =>
                exact absurd
                  (toModuleTuple_of_basicType arg hbasic ▸ tuple_isProcTuple _) hpt
          · intro h; cases h
          · intro h; cases h
    | fst e ihe =>
      constructor
      · intro hn N h
        simp only [toSTLC] at h
        cases hn with | neutral hne => cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : toSTLC e = E at h
          cases h with
          | fstPair => exact absurd hE (ihe_pair _ _)
          | fst step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [toSTLC] at h
            generalize hE : toSTLC e = E at h
            cases h with
            | fstPair => exact absurd hE (ihe_pair _ _)
            | fst step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h
    | snd e ihe =>
      constructor
      · intro hn N h
        simp only [toSTLC] at h
        cases hn with | neutral hne => cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : toSTLC e = E at h
          cases h with
          | sndPair => exact absurd hE (ihe_pair _ _)
          | snd step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [toSTLC] at h
            generalize hE : toSTLC e = E at h
            cases h with
            | sndPair => exact absurd hE (ihe_pair _ _)
            | snd step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h

private theorem pwhToSTLC_inj {holes holes' : HoleSigs} {sig sig' : ProcedureSignature}
    {p : ProcedureWithHoles holes sig} {p' : ProcedureWithHoles holes' sig'} :
    pwhToSTLC p = pwhToSTLC p' → holes = holes' ∧ sig = sig' ∧ p ≍ p' := by
  intro h
  simp only [pwhToSTLC] at h
  injection h with _ _ h3
  cases h3
  exact ⟨rfl, rfl, HEq.rfl⟩

private theorem toSTLC_injective_new (m m' : ModuleExpression) :
    toSTLC m = toSTLC m' → m = m' := by
  intro h
  induction m generalizing m' with
  | proc p => cases m' <;> simp only [toSTLC] at h <;> first | contradiction | (cases h; rfl)
  | procHoles ne p =>
      cases m' <;> simp only [toSTLC] at h <;>
        first | contradiction | (obtain ⟨rfl, rfl, hp⟩ := pwhToSTLC_inj h; rw [eq_of_heq hp])
  | var n =>
      cases m' <;> simp only [toSTLC] at h <;>
        first | (injection h with h1; rw [h1]) | contradiction
  | app f a ihf iha =>
      cases m' <;> simp only [toSTLC] at h <;>
        first | (injection h with h1 h2; rw [ihf _ h1, iha _ h2]) | contradiction
  | fst e ih =>
      cases m' <;> simp only [toSTLC] at h <;>
        first | (injection h with h1; rw [ih _ h1]) | contradiction
  | snd e ih =>
      cases m' <;> simp only [toSTLC] at h <;>
        first | (injection h with h1; rw [ih _ h1]) | contradiction
  | abs b ih =>
      cases m' <;> simp only [toSTLC] at h <;>
        first | (injection h with h1; rw [ih _ h1]) | contradiction
  | pair a b iha ihb =>
      cases m' <;> simp only [toSTLC] at h <;>
        first | (injection h with h1 h2; rw [iha _ h1, ihb _ h2]) | contradiction
  | unit => cases m' <;> simp only [toSTLC] at h <;> first | rfl | contradiction


/-! ### Shape predicates for call-by-value reduction (untyped analogues) -/

/- /-- `m` is a lambda-abstraction. -/
-- TODO check needed
def IsAbs : ModuleExpression → Prop
  | .abs _ => True
  | _      => False

-- TODO check needed
instance : (m : ModuleExpression) → Decidable (IsAbs m)
  | .abs _ => isTrue trivial
  | .proc _ | .procHoles _ _ | .var _ | .app _ _ | .fst _ | .snd _ | .pair _ _ | .unit =>
      isFalse (by simp [IsAbs])

/-- The body of an abstraction. -/
-- TODO check needed
def IsAbs.body {m : ModuleExpression} (h : IsAbs m) : ModuleExpression := by
  cases m with
  | abs body => exact body
  | _ => simp [IsAbs] at h -/

/- /-- `m` is a pair. -/
-- TODO check needed
def IsPair : ModuleExpression → Prop
  | .pair _ _ => True
  | _         => False

instance : (m : ModuleExpression) → Decidable (IsPair m)
  | .pair _ _ => isTrue trivial
  | .proc _ | .procHoles _ _ | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .unit =>
      isFalse (by simp [IsPair])

/-- The two components of a pair. -/
def IsPair.split {m : ModuleExpression} (h : IsPair m) : ModuleExpression × ModuleExpression := by
  cases m with
  | pair a b => exact (a, b)
  | _ => simp [IsPair] at h

def IsPair.fst {m : ModuleExpression} (h : IsPair m) : ModuleExpression := h.split.1
def IsPair.snd {m : ModuleExpression} (h : IsPair m) : ModuleExpression := h.split.2
 -/

theorem NormalClosed.normal {m : ModuleExpression} (h : m.NormalClosed) : m.Normal := by
  induction h with
  | proc => exact .proc
  | procHoles => exact .procHoles
  | abs hb => exact .abs hb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit

/-- Typing is preserved along multi-step reduction. -/
theorem HasType.preservation_multi {m m' : ModuleExpression} {Δ T} (hm : m.HasType Δ T)
    (h : m.MultiStepReduction m') : m'.HasType Δ T := by
  induction h with
  | refl => exact hm
  | tail _ hstep ih => exact ModuleExpression.HasType.preservation hstep ih

def Stuck (m : ModuleExpression) : Prop := ¬∃ n, m.ReductionStep n

theorem Normal.stuck {m : ModuleExpression} (h : m.Normal) : Stuck m := by
  rintro ⟨n, hstep⟩
  exact toSTLC_normal_isNormalForm h _ (reductionStep_stlc_compat _ _ hstep)

/-- `m` terminates: it multi-step reduces to some normal form. -/
def Terminating (m : ModuleExpression) : Prop :=
  ∃ n : ModuleExpression, n.Stuck ∧ m.MultiStepReduction n

lemma Stuck.terminating {m : ModuleExpression} (h : Stuck m) : Terminating m := ⟨m, h, .refl m⟩

lemma Normal.terminating {m : ModuleExpression} (h : Normal m) : Terminating m :=
  h.stuck.terminating

/- -- TODO: check whether we actually want to keep this
def reduce_all (m : ModuleExpression) : Set ModuleExpression :=
  { n | n.Stuck ∧ m.MultiStepReduction n } -/

theorem multiStepReduction_confluence {m n1 n2 : ModuleExpression}
  (_ : m.MultiStepReduction n1) (_ : m.MultiStepReduction n2)
  (_ : n1.Stuck) (_ : n2.Stuck) :
  n1 = n2 := by
  have stuck_nf : ∀ {k : ModuleExpression}, Stuck k →
      Rewriting.IsNormalForm Metatheory.STLCext.Step (toSTLC k) := by
    intro k hk M' hstep
    obtain ⟨k', hnd, _⟩ := reductionStep_stlc_complete k M' hstep
    exact hk ⟨k', hnd⟩
  exact toSTLC_injective_new n1 n2
    (Rewriting.normalForm_unique Metatheory.STLCext.step_confluent
      (multiStepReduction_to_stlc_star ‹m.MultiStepReduction n1›)
      (multiStepReduction_to_stlc_star ‹m.MultiStepReduction n2›)
      (stuck_nf ‹n1.Stuck›) (stuck_nf ‹n2.Stuck›))

/- theorem reduce_all_subsingleton {m : ModuleExpression} :
    Set.Subsingleton (reduce_all m) := by
  have stuck_nf : ∀ {k : ModuleExpression}, Stuck k →
      Rewriting.IsNormalForm Metatheory.STLCext.Step (toSTLC k) := by
    intro k hk M' hstep
    obtain ⟨k', hnd, _⟩ := reductionStep_stlc_complete k M' hstep
    exact hk ⟨k', hnd⟩
  intro x hx y hy
  obtain ⟨hxstuck, hxred⟩ := hx
  obtain ⟨hystuck, hyred⟩ := hy
  exact toSTLC_injective_new x y
    (Rewriting.normalForm_unique Metatheory.STLCext.step_confluent
      (multiStepReduction_to_stlc_star hxred) (multiStepReduction_to_stlc_star hyred)
      (stuck_nf hxstuck) (stuck_nf hystuck)) -/

/- theorem Terminating.reduce_all_nonempty {m : ModuleExpression} (h : Terminating m) :
    (reduce_all m).Nonempty := by
  cases h with
  | intro n hn => exact ⟨n, hn⟩ -/

/- -- TODO check needed
def omega : ModuleExpression :=
  .app (.abs (.app (.var 0) (.var 0))) (.abs (.app (.var 0) (.var 0)))

theorem omega_nonterminating : ¬Terminating omega := by
  have step_omega : ∀ c, omega.ReductionStep c → c = omega := by
    intro c h
    cases h with
    | beta => rfl
    | appL h' => cases h' with | lam h'' => cases h'' with
        | appL h3 => cases h3
        | appR h3 => cases h3
    | appR h' => cases h' with | lam h'' => cases h'' with
        | appL h3 => cases h3
        | appR h3 => cases h3
  have red_omega : ∀ n, omega.MultiStepReduction n → n = omega := by
    intro n h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact step_omega _ (ih ▸ hbc)
  rintro ⟨n, hstuck, hred⟩
  have hn : n = omega := red_omega n hred
  subst hn
  exact hstuck ⟨_, ReductionStep.beta⟩ -/

/-- Convertibility: the equivalence relation generated by `ReductionStep`, i.e. its
    reflexive, symmetric, transitive closure. -/
def convertible : ModuleExpression → ModuleExpression → Prop :=
  Relation.EqvGen ReductionStep

open Classical in
/-- β-normal form: a chosen normal form reachable from `m` when it terminates, else `unit`. -/
noncomputable def reduce (m : ModuleExpression) : ModuleExpression :=
  if h : Terminating m
  then h.choose
  else Set.Nonempty.some (⟨m, Relation.EqvGen.refl m⟩ : {n | convertible m n}.Nonempty)


/- @[simp] theorem reduce_all_of_stuck {m : ModuleExpression} (h : m.Stuck) :
    reduce_all m = {m} := by
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨h, .refl m⟩, ?_⟩
  rintro n ⟨-, hred⟩
  induction hred with
  | refl => rfl
  | tail _ hbc ih => exact absurd ⟨_, ih ▸ hbc⟩ h -/

/- theorem reduce_all_stuck {m : ModuleExpression} (n : ModuleExpression) (h : n ∈ reduce_all m) :
  n.Stuck := h.1 -/

theorem reduce_stuck {m : ModuleExpression} (ht : Terminating m) : (reduce m).Stuck := by
  rw [reduce]
  split
  · rename_i h; exact h.choose_spec.1
  · rename_i h; exact absurd ht h

/- theorem multiStepReduction_reduce_all {m n : ModuleExpression} (h : n ∈ reduce_all m) :
  m.MultiStepReduction n := h.2 -/

/-- Reflect a multi-step STLC reduction out of the `toSTLC` image back to a module reduction:
    everything reachable from `toSTLC m` is `toSTLC` of a reduct of `m`. -/
private theorem multiStepReduction_of_stlc_star {m : ModuleExpression}
    {N : Metatheory.STLCext.Term}
    (h : Rewriting.Star Metatheory.STLCext.Step (toSTLC m) N) :
    ∃ m', toSTLC m' = N ∧ m.MultiStepReduction m' := by
  induction h with
  | refl => exact ⟨m, rfl, .refl m⟩
  | tail _ hbc ih =>
      obtain ⟨m', heq, hred⟩ := ih
      subst heq
      obtain ⟨m'', hnd, heq'⟩ := reductionStep_stlc_complete m' _ hbc
      exact ⟨m'', heq', Rewriting.Star.tail hred hnd⟩

theorem multiStepReduction_terminating {m n} (h : m.MultiStepReduction n) :
    Terminating m ↔ Terminating n := by
  constructor
  · rintro ⟨k, hk, hmk⟩
    refine ⟨k, hk, ?_⟩
    have hknf : Rewriting.IsNormalForm Metatheory.STLCext.Step (toSTLC k) := by
      intro M' hstep
      obtain ⟨k', hnd, _⟩ := reductionStep_stlc_complete k M' hstep
      exact hk ⟨k', hnd⟩
    obtain ⟨d, hnd, hkd⟩ := Metatheory.STLCext.step_confluent _ _ _
      (multiStepReduction_to_stlc_star h) (multiStepReduction_to_stlc_star hmk)
    have hd := Rewriting.star_normalForm_eq hkd hknf
    subst hd
    obtain ⟨n', heq, hred⟩ := multiStepReduction_of_stlc_star hnd
    exact toSTLC_injective_new n' k heq ▸ hred
  · rintro ⟨k, hk, hnk⟩
    exact ⟨k, hk, Rewriting.Star.trans h hnk⟩

theorem multiStepReduction_reduce {m : ModuleExpression} (h : Terminating m) :
    m.MultiStepReduction (reduce m) := by
  rw [reduce, dif_pos h]
  exact h.choose_spec.2

@[simp] theorem reduce_of_stuck {m : ModuleExpression} (h : m.Stuck) : reduce m = m :=
  multiStepReduction_confluence
    (multiStepReduction_reduce h.terminating) (Rewriting.Star.refl m) (reduce_stuck h.terminating) h

/-- Multi-step reduction refines convertibility. -/
theorem convertible_of_multiStep {a b : ModuleExpression} (h : a.MultiStepReduction b) :
    convertible a b := by
  unfold convertible
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

/-- Termination is invariant along equireducibility: each `ReductionStep` preserves it via
    `multiStepReduction_terminating`, and refl/symm/trans closure is immediate. -/
theorem convertible_terminating {m n : ModuleExpression} (h : convertible m n) :
    Terminating m ↔ Terminating n := by
  unfold convertible at h
  induction h with
  | rel x y hxy =>
      exact multiStepReduction_terminating (Rewriting.Star.head hxy (Rewriting.Star.refl _))
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- On a non-terminating input, `reduce` is the chosen representative of the convertible class. -/
private theorem reduce_of_not_terminating {m : ModuleExpression} (h : ¬Terminating m) :
    reduce m =
      Set.Nonempty.some (⟨m, Relation.EqvGen.refl m⟩ : {n | convertible m n}.Nonempty) := by
  rw [reduce, dif_neg h]

/-- `reduce m` is always convertible to `m` (a reduct if terminating, a class rep otherwise). -/
theorem convertible_reduce {m : ModuleExpression} : convertible m (reduce m) := by
  by_cases h : Terminating m
  · exact convertible_of_multiStep (multiStepReduction_reduce h)
  · rw [reduce_of_not_terminating h]; exact Set.Nonempty.some_mem _

/-- `reduce` is constant on a convertible class of non-terminating expressions. -/
private theorem reduce_eq_of_convertible_not_term {m n : ModuleExpression}
    (h : convertible m n) (hm : ¬Terminating m) (hn : ¬Terminating n) :
    reduce m = reduce n := by
  rw [reduce_of_not_terminating hm, reduce_of_not_terminating hn]
  -- `Set.Nonempty.some` depends only on the set: equal sets give equal representatives
  -- (the nonempty witnesses are proof-irrelevant).
  have some_congr : ∀ {α : Type _} {s t : Set α} (_ : s = t)
      (hs : s.Nonempty) (ht : t.Nonempty), hs.some = ht.some := by
    intro α s t hst hs ht; subst hst; rfl
  apply some_congr
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hk; exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hk
  · intro hk; exact Relation.EqvGen.trans _ _ _ h hk

theorem reduce_terminating {m : ModuleExpression} : Terminating m ↔ Terminating (reduce m) := by
  constructor
  · intro h; exact (reduce_stuck h).terminating
  · intro h
    by_contra hm
    exact hm ((convertible_terminating convertible_reduce).mpr h)

theorem HasType.terminating {m Δ T} (h : m.HasType Δ T) : Terminating m := by
  obtain ⟨N, hstar, hnf⟩ :=
    Metatheory.STLCext.hasNormalForm_of_SN
      (Metatheory.STLCext.strong_normalization (toSTLC_hasType h))
  obtain ⟨m', heq, hred⟩ := multiStepReduction_of_stlc_star hstar
  refine ⟨m', ?_, hred⟩
  rintro ⟨k, hstep⟩
  exact hnf (toSTLC k) (heq ▸ reductionStep_stlc_compat _ _ hstep)

/-- Reduction preserves typing. -/
theorem reduce_hasType {m Δ T} (h : m.HasType Δ T) : (reduce m).HasType Δ T :=
  h.preservation_multi (multiStepReduction_reduce h.terminating)

/-- A well-typed proc-tuple is the module-expression image of some instantiation (the existence
    content of `procTupleLookup`/`procTupleLookup_toModuleTuple`, but as a `Prop`). -/
private theorem exists_toModuleExpr {holes : HoleSigs} :
    ∀ {Δ : ModuleContext} {a : ModuleExpression},
      a.HasType Δ (HoleSigs.toModuleTypeRepTuple holes) → a.IsProcTuple →
      ∃ inst : holes.Instantiation, a = inst.toModuleExpr := by
  induction holes with
  | empty =>
      intro Δ a hty h
      cases a with
      | unit => exact ⟨(fun {_} n => nomatch n), rfl⟩
      | pair x y => obtain ⟨A, B, heq, _, _⟩ := hty.pair_inv;
                    simp [HoleSigs.toModuleTypeRepTuple] at heq
      | proc _ => exact absurd h (by simp [IsProcTuple])
      | procHoles _ _ => exact absurd h (by simp [IsProcTuple])
      | var _ => exact absurd h (by simp [IsProcTuple])
      | app _ _ => exact absurd h (by simp [IsProcTuple])
      | fst _ => exact absurd h (by simp [IsProcTuple])
      | snd _ => exact absurd h (by simp [IsProcTuple])
      | abs _ => exact absurd h (by simp [IsProcTuple])
  | append rest sig ih =>
      intro Δ a hty h
      cases a with
      | pair x y =>
          cases x with
          | proc p =>
              obtain ⟨A, B, heq, hx, hy⟩ := hty.pair_inv
              simp only [HoleSigs.toModuleTypeRepTuple] at heq
              injection heq with hA hB
              subst hA; subst hB
              cases hx
              obtain ⟨instTail, rfl⟩ := ih hy (h : IsProcTuple y)
              exact ⟨fun {_} idx => match idx with
                      | .zero => p
                      | .succ idx' => instTail idx', rfl⟩
          | unit => exact absurd h (by simp [IsProcTuple])
          | pair _ _ => exact absurd h (by simp [IsProcTuple])
          | procHoles _ _ => exact absurd h (by simp [IsProcTuple])
          | var _ => exact absurd h (by simp [IsProcTuple])
          | app _ _ => exact absurd h (by simp [IsProcTuple])
          | fst _ => exact absurd h (by simp [IsProcTuple])
          | snd _ => exact absurd h (by simp [IsProcTuple])
          | abs _ => exact absurd h (by simp [IsProcTuple])
      | unit => have hui := hty.unit_inv; simp [HoleSigs.toModuleTypeRepTuple] at hui
      | proc _ => exact absurd h (by simp [IsProcTuple])
      | procHoles _ _ => exact absurd h (by simp [IsProcTuple])
      | var _ => exact absurd h (by simp [IsProcTuple])
      | app _ _ => exact absurd h (by simp [IsProcTuple])
      | fst _ => exact absurd h (by simp [IsProcTuple])
      | snd _ => exact absurd h (by simp [IsProcTuple])
      | abs _ => exact absurd h (by simp [IsProcTuple])

/-- Progress for well-typed (possibly open) terms: a non-normal well-typed term reduces. -/
theorem progress {m : ModuleExpression} :
    ∀ {Δ T}, m.HasType Δ T → ¬ m.Normal → ∃ n, m.ReductionStep n := by
  induction m with
  | unit => intro Δ T hty nn; exact absurd .unit nn
  | var n => intro Δ T hty nn; exact absurd (.neutral .var) nn
  | proc p => intro Δ T hty nn; exact absurd .proc nn
  | procHoles ne p => intro Δ T hty nn; exact absurd .procHoles nn
  | abs body ih =>
      intro Δ T hty nn
      by_cases hb : body.Normal
      · exact absurd (.abs hb) nn
      · obtain ⟨A, B, _, hbody⟩ := hty.abs_inv
        obtain ⟨n, hn⟩ := ih hbody hb
        exact ⟨_, .lam hn⟩
  | pair a b iha ihb =>
      intro Δ T hty nn
      obtain ⟨A, B, _, ha, hb⟩ := hty.pair_inv
      by_cases hna : a.Normal
      · by_cases hnb : b.Normal
        · exact absurd (.pair hna hnb) nn
        · obtain ⟨n, hn⟩ := ihb hb hnb; exact ⟨_, .pairR hn⟩
      · obtain ⟨n, hn⟩ := iha ha hna; exact ⟨_, .pairL hn⟩
  | fst e ihe =>
      intro Δ T hty nn
      obtain ⟨B, he⟩ := hty.fst_inv
      by_cases hne : e.Normal
      · cases hne with
        | neutral ne => exact absurd (.neutral (.fst ne)) nn
        | pair _ _ => exact ⟨_, .fstPair⟩
        | abs _ => nomatch he
        | proc => nomatch he
        | procHoles => nomatch he
        | unit => nomatch he
      · obtain ⟨n, hn⟩ := ihe he hne; exact ⟨_, .fst hn⟩
  | snd e ihe =>
      intro Δ T hty nn
      obtain ⟨A, he⟩ := hty.snd_inv
      by_cases hne : e.Normal
      · cases hne with
        | neutral ne => exact absurd (.neutral (.snd ne)) nn
        | pair _ _ => exact ⟨_, .sndPair⟩
        | abs _ => nomatch he
        | proc => nomatch he
        | procHoles => nomatch he
        | unit => nomatch he
      · obtain ⟨n, hn⟩ := ihe he hne; exact ⟨_, .snd hn⟩
  | app f arg ihf iharg =>
      intro Δ T hty nn
      obtain ⟨A, hf, harg⟩ := hty.app_inv
      by_cases hnf : f.Normal
      · by_cases hnarg : arg.Normal
        · cases hnf with
          | neutral ne => exact absurd (.neutral (.app ne hnarg)) nn
          | abs _ => exact ⟨_, .beta⟩
          | pair _ _ => nomatch hf
          | proc => nomatch hf
          | unit => nomatch hf
          | @procHoles holes sig ne p =>
              by_cases hpt : arg.IsProcTuple
              · have hpinv := hf.procHoles_inv
                rw [ModuleTypeRep.arr.injEq] at hpinv
                obtain ⟨rfl, rfl⟩ := hpinv
                obtain ⟨inst, rfl⟩ := exists_toModuleExpr harg hpt
                exact ⟨_, .delta ne p inst⟩
              · exact absurd (.neutral (.appProcHoles (by trivial) hnarg hpt)) nn
        · obtain ⟨n, hn⟩ := iharg harg hnarg; exact ⟨_, .appR hn⟩
      · obtain ⟨n, hn⟩ := ihf hf hnf; exact ⟨_, .appL hn⟩

theorem Stuck.normal {m : ModuleExpression} (h : m.Stuck) (hty : m.HasType Δ T) :
  m.Normal := by
  by_contra nn
  exact h (progress hty nn)

/-- A normal well-typed closed term is closed-normal. -/
theorem Normal.normalClosed {m : ModuleExpression} {T} (_h : Normal m)
    (_hty : m.HasType [] T) : NormalClosed m := by
  induction m generalizing T with
  | proc p => exact .proc
  | procHoles ne p => exact .procHoles
  | unit => exact .unit
  | var n => exact absurd .var (closedProgress _hty).1
  | abs body ih =>
      cases _h with
      | abs hb => exact .abs hb
      | neutral hne => exact absurd hne (closedProgress _hty).1
  | app f arg ihf iharg =>
      cases _h with | neutral hne => exact absurd hne (closedProgress _hty).1
  | fst e ihe =>
      cases _h with | neutral hne => exact absurd hne (closedProgress _hty).1
  | snd e ihe =>
      cases _h with | neutral hne => exact absurd hne (closedProgress _hty).1
  | pair a b iha ihb =>
      obtain ⟨A, B, rfl, hta, htb⟩ := _hty.pair_inv
      cases _h with
      | pair ha hb => exact .pair (iha ha hta) (ihb hb htb)
      | neutral hne => exact absurd hne (closedProgress _hty).1

/-- The reduct of a well-typed closed term is closed-normal. -/
theorem reduce_normal {m} (h : m.HasType Δ T) : (reduce m).Normal :=
  Stuck.normal (reduce_stuck h.terminating) (reduce_hasType h)

/-- The reduct of a well-typed closed term is closed-normal. -/
theorem reduce_normalClosed {m T} (h : m.HasType [] T) : (reduce m).NormalClosed :=
  Normal.normalClosed (reduce_normal h) (reduce_hasType h)

theorem reduce_idempotent (m : ModuleExpression) : reduce (reduce m) = reduce m := by
  by_cases h : Terminating m
  · exact reduce_of_stuck (reduce_stuck h)
  · have hnr : ¬Terminating (reduce m) := fun hh =>
      h ((convertible_terminating convertible_reduce).mpr hh)
    exact reduce_eq_of_convertible_not_term (Relation.EqvGen.symm _ _ convertible_reduce) hnr h

/-- A normal term is its own reduct (normal terms are stuck). -/
@[simp] theorem reduce_of_normal {m : ModuleExpression} (h : m.Normal) : reduce m = m :=
  reduce_of_stuck h.stuck

@[simp] theorem reduce_proc {sig} (p : Procedure sig) : reduce (.proc p) = .proc p :=
  reduce_of_stuck Normal.proc.stuck

theorem confluence {m m1 m2 : ModuleExpression}
    (h1 : m.MultiStepReduction m1) (h2 : m.MultiStepReduction m2) : reduce m1 = reduce m2 := by
  by_cases ht : Terminating m1
  · have ht2 : Terminating m2 :=
      (multiStepReduction_terminating h2).mp ((multiStepReduction_terminating h1).mpr ht)
    exact multiStepReduction_confluence
      (Rewriting.Star.trans h1 (multiStepReduction_reduce ht))
      (Rewriting.Star.trans h2 (multiStepReduction_reduce ht2))
      (reduce_stuck ht) (reduce_stuck ht2)
  · have ht2 : ¬ Terminating m2 := fun h =>
      ht ((multiStepReduction_terminating h1).mp ((multiStepReduction_terminating h2).mpr h))
    have h12 : convertible m1 m2 :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (convertible_of_multiStep h1))
        (convertible_of_multiStep h2)
    exact reduce_eq_of_convertible_not_term h12 ht ht2

theorem reduce_step {m n : ModuleExpression} (h : m.ReductionStep n) : reduce m = reduce n :=
  confluence (.refl _) (Rewriting.Star.head h (Rewriting.Star.refl _))

theorem reduce_convertible {m n : ModuleExpression} (_ : convertible m n) :
  reduce m = reduce n := by
  rename_i h
  unfold convertible at h
  induction h with
  | rel x y hxy => exact reduce_step hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem reduce_multiStepReduction {m n : ModuleExpression} (h : m.MultiStepReduction n) :
    reduce m = reduce n :=
  reduce_convertible (convertible_of_multiStep h)

theorem reduce_convertible_iff {m n : ModuleExpression} :
  convertible m n ↔ reduce m = reduce n := by
  constructor
  · exact reduce_convertible
  · intro h
    exact Relation.EqvGen.trans _ _ _ (h ▸ convertible_reduce)
      (Relation.EqvGen.symm _ _ convertible_reduce)


theorem reduce_beta (body arg : ModuleExpression) :
    reduce (.app (.abs body) arg) = reduce (body.substitute arg) :=
  confluence (.refl _) (Rewriting.Star.head ReductionStep.beta (Rewriting.Star.refl _))

/-! ### Misc -/

/-- Progress for the closed fragment (untyped analogue of `TypedModules.closed_progress`); typing pins the
    empty context. -/
private theorem closed_progress {m : ModuleExpression} {T} (_h : m.HasType [] T) :
    (¬ Neutral m) ∧ (IsProcArgType T → Normal m → IsProcTuple m) := closedProgress _h

/-- A well-typed closed term is never neutral. -/
theorem hasType_empty_context_not_neutral {m : ModuleExpression} {T} (h : m.HasType [] T) :
    ¬ Neutral m := (closed_progress h).1

/-- `app` is a congruence for multi-step reduction. -/
theorem multiStepReduction_app_cong {m1 m1' m2 m2' : ModuleExpression}
    (h1 : m1.MultiStepReduction m1') (h2 : m2.MultiStepReduction m2') :
    (ModuleExpression.app m1 m2).MultiStepReduction (ModuleExpression.app m1' m2') := by
  have left : (ModuleExpression.app m1 m2).MultiStepReduction (ModuleExpression.app m1' m2) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appL hbc)
  have right : (ModuleExpression.app m1' m2).MultiStepReduction (ModuleExpression.app m1' m2') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appR hbc)
  exact Rewriting.Star.trans left right

/-- `fst` is a congruence for multi-step reduction. -/
theorem multiStepReduction_fst_cong {e e' : ModuleExpression} (h : e.MultiStepReduction e') :
    (ModuleExpression.fst e).MultiStepReduction (ModuleExpression.fst e') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (.fst hbc)

/-- `pair` is a congruence for multi-step reduction. -/
theorem multiStepReduction_pair_cong {a a' b b' : ModuleExpression}
    (h1 : a.MultiStepReduction a') (h2 : b.MultiStepReduction b') :
    (ModuleExpression.pair a b).MultiStepReduction (ModuleExpression.pair a' b') := by
  have left : (ModuleExpression.pair a b).MultiStepReduction (ModuleExpression.pair a' b) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairL hbc)
  have right : (ModuleExpression.pair a' b).MultiStepReduction (ModuleExpression.pair a' b') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairR hbc)
  exact Rewriting.Star.trans left right

/-- A pair of stuck expressions is stuck: `pair` can only step via `pairL`/`pairR`. -/
theorem stuck_pair {a b : ModuleExpression} (ha : Stuck a) (hb : Stuck b) :
    Stuck (.pair a b) := by
  rintro ⟨n, hstep⟩
  cases hstep with
  | pairL h => exact ha ⟨_, h⟩
  | pairR h => exact hb ⟨_, h⟩

theorem reduce_pair_terminating {m1 m2 : ModuleExpression}
    (h1 : Terminating m1) (h2 : Terminating m2) :
    reduce (.pair m1 m2) = .pair (reduce m1) (reduce m2) := by
  have hst : Stuck (.pair (reduce m1) (reduce m2)) :=
    stuck_pair (reduce_stuck h1) (reduce_stuck h2)
  have hred : (ModuleExpression.pair m1 m2).MultiStepReduction (.pair (reduce m1) (reduce m2)) :=
    multiStepReduction_pair_cong (multiStepReduction_reduce h1) (multiStepReduction_reduce h2)
  have hterm : Terminating (.pair m1 m2) := ⟨_, hst, hred⟩
  exact multiStepReduction_confluence
    (multiStepReduction_reduce hterm) hred (reduce_stuck hterm) hst

/-- `toModuleExpr inst` is always a proc-tuple (untyped analogue of
    `TypedModules.toModuleTuple_isProcTuple`). -/
private theorem toModuleExpr_isProcTuple {holes : HoleSigs} (inst : holes.Instantiation) :
    (HoleSigs.Instantiation.toModuleExpr inst).IsProcTuple := by
  induction holes with
  | empty => simp [HoleSigs.Instantiation.toModuleExpr, IsProcTuple]
  | append holeTail sig ih =>
      simp only [HoleSigs.Instantiation.toModuleExpr]
      exact ih (fun idx => inst (.succ idx))

/-! #### Remaining `reduce` specification lemmas -/

@[simp] theorem reduce_fst (m m' : ModuleExpression) :
    reduce (.fst (.pair m m')) = reduce m := reduce_step .fstPair

@[simp] theorem reduce_snd (m m' : ModuleExpression) :
    reduce (.snd (.pair m m')) = reduce m' := reduce_step .sndPair

theorem reduce_fst_cong (m m' : ModuleExpression) :
    reduce m = reduce m' → reduce (.fst m) = reduce (.fst m') := by
  rw [← reduce_convertible_iff, ← reduce_convertible_iff]
  intro h
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (.fst hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem reduce_snd_cong (m m' : ModuleExpression) :
    reduce m = reduce m' → reduce (.snd m) = reduce (.snd m') := by
  rw [← reduce_convertible_iff, ← reduce_convertible_iff]
  intro h
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (.snd hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Congruence form for `.pair`: combines two independently-computed simplifications
    `reduce a = a'` / `reduce b = b'` (however they were obtained — `a'`/`b'` need not
    themselves be fully reduced) into one for the surrounding `.pair`. Proved directly via
    `convertible`: `pairL`/`pairR` lift `convertible_reduce` through `.pair` on each side, and
    `reduce_convertible_iff` turns the resulting `convertible` witness back into a `reduce`
    equation. -/
theorem reduce_pair_cong {a a' b b' : ModuleExpression} (ha : reduce a = a') (hb : reduce b = b') :
    reduce (.pair a b) = reduce (.pair a' b') := by
  have congL : ∀ {a b c : ModuleExpression}, convertible a b →
      convertible (.pair a c) (.pair b c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.pairL hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have congR : ∀ {a b c : ModuleExpression}, convertible b c →
      convertible (.pair a b) (.pair a c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.pairR hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  rw [← reduce_convertible_iff]
  exact Relation.EqvGen.trans _ _ _
    (congL (ha ▸ convertible_reduce)) (congR (hb ▸ convertible_reduce))

/-- Congruence form for `.app`, matching `reduce_pair_cong`. -/
theorem reduce_app_cong {a a' b b' : ModuleExpression} (ha : reduce a = a') (hb : reduce b = b') :
    reduce (.app a b) = reduce (.app a' b') := by
  have congL : ∀ {a b c : ModuleExpression}, convertible a b →
      convertible (.app a c) (.app b c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.appL hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have congR : ∀ {a b c : ModuleExpression}, convertible b c →
      convertible (.app a b) (.app a c) := by
    intro a b c h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.appR hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  rw [← reduce_convertible_iff]
  exact Relation.EqvGen.trans _ _ _
    (congL (ha ▸ convertible_reduce)) (congR (hb ▸ convertible_reduce))

/-- Congruence form for `.abs`, matching `reduce_pair_cong`/`reduce_app_cong`. -/
theorem reduce_abs_cong {a a' : ModuleExpression} (ha : reduce a = a') :
    reduce (.abs a) = reduce (.abs a') := by
  have cong : ∀ {a b : ModuleExpression}, convertible a b → convertible (.abs a) (.abs b) := by
    intro a b h
    induction h with
    | rel x y hxy => exact Relation.EqvGen.rel _ _ (.lam hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  rw [← reduce_convertible_iff]
  exact cong (ha ▸ convertible_reduce)

/-! #### Stripping an inner `reduce`

`reduce` only cares about its argument up to convertibility, so a subterm that is already a
`reduce` can be replaced by what it reduces (`reduce_idempotent` on both sides of the matching
`_cong` lemma).  This is what makes the `.reduce`s that `toModule` leaves behind disappear when a
composite expression is reduced — see `Module.reduce_pair_expression`. -/

theorem reduce_app_left (f x : ModuleExpression) :
    (ModuleExpression.app f.reduce x).reduce = (ModuleExpression.app f x).reduce := by
  rw [(reduce_app_cong rfl rfl : reduce (.app f x) = reduce (.app f.reduce x.reduce)),
    (reduce_app_cong rfl rfl :
      reduce (.app f.reduce x) = reduce (.app f.reduce.reduce x.reduce)), reduce_idempotent]

theorem reduce_app_right (f x : ModuleExpression) :
    (ModuleExpression.app f x.reduce).reduce = (ModuleExpression.app f x).reduce := by
  rw [(reduce_app_cong rfl rfl : reduce (.app f x) = reduce (.app f.reduce x.reduce)),
    (reduce_app_cong rfl rfl :
      reduce (.app f x.reduce) = reduce (.app f.reduce x.reduce.reduce)), reduce_idempotent]

theorem reduce_fst_inner (m : ModuleExpression) :
    (ModuleExpression.fst m.reduce).reduce = (ModuleExpression.fst m).reduce :=
  reduce_fst_cong _ _ (reduce_idempotent m)

theorem reduce_snd_inner (m : ModuleExpression) :
    (ModuleExpression.snd m.reduce).reduce = (ModuleExpression.snd m).reduce :=
  reduce_snd_cong _ _ (reduce_idempotent m)

/-- A well-typed closed normal term of product type is a pair. -/
theorem pair_type_is_pair {m : ModuleExpression} {t1 t2}
    (hty : m.HasType [] (.prod t1 t2)) (h : NormalClosed m) :
    ∃ m1 m2, m = .pair m1 m2 := by
  cases h with
  | pair => exact ⟨_, _, rfl⟩
  | proc => cases hty
  | procHoles => cases hty
  | abs _ => cases hty
  | unit => cases hty

end ModuleExpression

/-! # Tactics -/

/-! ## `moduletyping` -/

/-- Syntax-directed closer for `ModuleExpression.HasType m Δ T`: peels off the `HasType`
    constructor matching `m`'s head, leaves whatever it cannot close (e.g. an unprovable
    `.var` bound) as an open goal. See `moduletyping!` for a variant that fails loudly
    instead. -/
macro "moduletyping" : tactic => do
  -- `Module.typed_weaken` is declared further down this file, so a quotation identifier cannot
  -- name it: hygiene resolves those *here*, where it does not exist yet.  `mkIdent` builds a
  -- macro-scope-free identifier instead, which is resolved at the expansion site.
  let weaken := Lean.mkIdent `GaudisCrypt.Module.typed_weaken
  `(tactic| repeat' first
    -- a leaf that is an already-formed module (`m.expression`): closed, hence well-typed in
    -- any context.  Tried first, since it is the only rule matching that head.
    | exact $weaken _ _
    | apply ModuleExpression.HasType.proc
    | apply ModuleExpression.HasType.procHoles
    | apply ModuleExpression.HasType.unit
    | apply ModuleExpression.HasType.pair
    | apply ModuleExpression.HasType.abs
    | apply ModuleExpression.HasType.app
    | apply ModuleExpression.HasType.fst
    | apply ModuleExpression.HasType.snd
    | (apply ModuleExpression.HasType.var
       try (simp only [List.length_cons, List.length_nil]; omega)))

open Lean Elab Tactic Meta in
/-- Describe why a single leftover goal (from `moduletyping`'s core script) couldn't be
    closed. Recognises the two shapes that script can actually leave behind: an
    `n < Δ.length` residual (the `.var` bound, when `simp`/`omega` couldn't discharge it) and
    a `HasType m Δ T` residual whose head constructor's conclusion type didn't match `T`
    (`.proc`/`.procHoles`/`.unit`/`.var`/`.abs`/`.pair` are the constructors with a
    target-type-shape requirement; `.app`/`.fst`/`.snd` are fully generic in their conclusion
    type and so never get stuck at their own node, only inside a premise). Falls back to the
    raw goal for anything else. -/
private def describeStuckModuleTypingGoal (g : MVarId) : MetaM MessageData := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``LT.lt 4 then
    let rhs := ty.getAppArgs[3]!
    if rhs.isAppOfArity ``List.length 2 then
      let n := ty.getAppArgs[2]!
      let ctx := rhs.getAppArgs[1]!
      return m!"`.var {n}` occurs in typing context {ctx}, which does not (provably) \
        contain more than {n} element(s) (need `{n} < {rhs}`)"
  -- `HasType`/`ModuleExpression`'s constructors all carry the ambient `[ProgramSpec]` as their
  -- first (instance-implicit) argument, hence arity `3 + 1` / `k + 1` below.
  if ty.isAppOfArity ``ModuleExpression.HasType 4 then
    let #[_inst, m, ctx, t] := ty.getAppArgs | pure ()
    let head := m.getAppFn
    if head.isConstOf ``ModuleExpression.var then
      let n := m.getAppArgs[1]!
      return m!"`.var {n}` does not type-check in context {ctx} at type {t}: that context \
        does not provide a `{n}`-th entry of that type"
    else if head.isConstOf ``ModuleExpression.proc then
      return m!"`.proc _` always has a `.proc sig`-shaped type, but the expected type \
        {t} is not of that shape"
    else if head.isConstOf ``ModuleExpression.procHoles then
      return m!"`.procHoles _ _` always has an `.arr _ (.proc sig)`-shaped type, but the \
        expected type {t} is not of that shape"
    else if head.isConstOf ``ModuleExpression.unit then
      return m!"`.unit` has type `.unit`, but the expected type {t} is not `.unit`"
    else if head.isConstOf ``ModuleExpression.abs then
      return m!"`.abs _` always has an `.arr _ _`-shaped (function) type, but the expected \
        type {t} is not of that shape"
    else if head.isConstOf ``ModuleExpression.pair then
      return m!"`.pair _ _` always has a `.prod _ _`-shaped type, but the expected type \
        {t} is not of that shape"
  return m!"could not close:\n{← ppGoal g}"

open Lean Elab Tactic Meta in
/-- `moduletyping`, but fails loudly instead of leaving unclosed goals open. Not fail-fast:
    it still runs the core script to completion (closing everything it can) before reporting,
    one "Cannot show ‹original goal›: ‹reason›" line per leftover goal, with the reason
    coming from `describeStuckModuleTypingGoal`. -/
elab "moduletyping!" : tactic => do
  let origGoal ← getMainGoal
  let origType ← origGoal.withContext (instantiateMVars (← origGoal.getType))
  let numSiblings := (← getGoals).length - 1
  evalTactic (← `(tactic| moduletyping))
  let after ← getGoals
  let leftover := after.take (after.length - numSiblings)
  unless leftover.isEmpty do
    let lines ← leftover.mapM fun g => do
      return m!"Cannot show {origType}: {← describeStuckModuleTypingGoal g}"
    throwError MessageData.joinSep lines "\n\n"

/-! ### Smoke tests -/

example : ModuleExpression.HasType .unit [] .unit := by moduletyping

example (A : ModuleTypeRep) : ModuleExpression.HasType (.var 0) [A] A := by moduletyping

example :
    ModuleExpression.HasType (.pair .unit .unit) [] (.prod .unit .unit) := by moduletyping

example : ModuleExpression.HasType (.fst (.pair .unit .unit)) [] .unit := by moduletyping

-- `.unit` applied to `.unit` is not well-typed (`.unit` isn't a function). `moduletyping`
-- peels the outer `.app`, closes the argument side (`HasType .unit [] ?A` via `.unit`, forcing
-- `?A := .unit`), and leaves the un-closable function side open instead of failing — so the
-- tactic block below ends with a genuine (and genuinely false) unsolved goal, caught by
-- `#guard_msgs` rather than papered over with a permanent `sorry`.
/-- error: unsolved goals
case a
inst✝ : ProgramSpec
⊢ ModuleExpression.unit.HasType [] (ModuleTypeRep.unit.arr ModuleTypeRep.unit) -/
#guard_msgs (whitespace := lax) in
example : ModuleExpression.HasType (.app .unit .unit) [] .unit := by
  moduletyping
  guard_target = ModuleExpression.HasType .unit [] (.arr .unit .unit)

-- `moduletyping!` fails loudly on the same goal, with a message pinpointing the `.unit` node
-- (not a function) rather than just the outer `.app` goal.
/-- error: Cannot show (ModuleExpression.unit.app ModuleExpression.unit).HasType [] ModuleTypeRep.unit: `.unit` has type `.unit`, but the expected type ModuleTypeRep.unit.arr ModuleTypeRep.unit is not `.unit` -/
#guard_msgs (whitespace := lax) in
example : ModuleExpression.HasType (.app .unit .unit) [] .unit := by
  moduletyping!

-- `.proc _` mismatch.
/-- error: Cannot show (ModuleExpression.proc p).HasType [] T: `.proc _` always has a `.proc sig`-shaped type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example {sig : ProcedureSignature} (p : Procedure sig) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.proc p) [] T := by
  moduletyping!

-- `.procHoles _ _` mismatch.
/-- error: Cannot show (ModuleExpression.procHoles ne p).HasType [] T: `.procHoles _ _` always has an `.arr _ (.proc sig)`-shaped type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.procHoles ne p) [] T := by
  moduletyping!

-- `.abs _` mismatch (expected type isn't `.arr _ _`-shaped).
/-- error: Cannot show body.abs.HasType [] T: `.abs _` always has an `.arr _ _`-shaped (function) type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example (body : ModuleExpression) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.abs body) [] T := by
  moduletyping!

-- `.pair _ _` mismatch (expected type isn't `.prod _ _`-shaped).
/-- error: Cannot show (a.pair b).HasType [] T: `.pair _ _` always has a `.prod _ _`-shaped type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example (a b : ModuleExpression) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.pair a b) [] T := by
  moduletyping!

-- `.var _` mismatch: no context can supply an entry of an unrelated, opaque type `T`.
/-- error: Cannot show (ModuleExpression.var 0).HasType [] T: `.var 0` does not type-check in context [] at type T: that context does not provide a `0`-th entry of that type -/
#guard_msgs (whitespace := lax) in
example (T : ModuleTypeRep) : ModuleExpression.HasType (.var 0) [] T := by
  moduletyping!

-- `.var _`'s bound, genuinely un-dischargeable by `moduletyping`: `A :: Γ` is a real (if
-- partly opaque) context, so unifying the *type* of `.var 1` structurally peels the concrete
-- `A` and lands on `Γ[0]'_`, unifying with the target via proof irrelevance and leaving the
-- outer bound `1 < (A :: Γ).length` as a genuine residual goal. It's actually true — `hΓ`
-- witnesses `Γ` is nonempty — but `hΓ` is `Nonempty`-wrapped rather than a plain arithmetic
-- hypothesis, so `simp`/`omega` (which only look at arithmetic hypotheses) can't see it.
/-- error: Cannot show (ModuleExpression.var 1).HasType (A :: Γ) Γ[0]:
    `.var 1` occurs in typing context A :: Γ, which does not (provably) contain more than 1 element(s) (need `1 < (A :: Γ).length`) -/
#guard_msgs (whitespace := lax) in
example (A : ModuleTypeRep) (Γ : ModuleContext) (hΓ : Nonempty (0 < Γ.length)) :
    ModuleExpression.HasType (.var 1) (A :: Γ) (Γ[0]'hΓ.some) := by
  moduletyping!

-- No fail-fast: both branches of a `.pair` are independently un-closable, and both reasons are
-- reported together in one error instead of stopping at the first.
/-- error: Cannot show ((ModuleExpression.proc p).pair body.abs).HasType [] (T.prod U): `.proc _` always has a `.proc sig`-shaped type, but the expected type T is not of that shape

Cannot show ((ModuleExpression.proc p).pair body.abs).HasType [] (T.prod U): `.abs _` always has an `.arr _ _`-shaped (function) type, but the expected type U is not of that shape -/
#guard_msgs (whitespace := lax) in
example {sig : ProcedureSignature} (p : Procedure sig) (body : ModuleExpression)
    (T U : ModuleTypeRep) :
    ModuleExpression.HasType (.pair (.proc p) (.abs body)) [] (.prod T U) := by
  moduletyping!

/-! ## `normalmodule` -/

/-- One step of `normalmodule`'s core script, factored out so `normalmodule` can require it to
    fire at least once (see below) while still repeating it leniently afterwards. -/
syntax "normalmoduleStep" : tactic
macro_rules
  | `(tactic| normalmoduleStep) =>
    `(tactic| first
      | assumption
      | apply ModuleExpression.Normal.unit
      | apply ModuleExpression.Normal.proc
      | apply ModuleExpression.Normal.procHoles
      | apply ModuleExpression.Normal.abs
      | apply ModuleExpression.Normal.pair
      | apply ModuleExpression.Neutral.var
      | apply ModuleExpression.Neutral.fst
      | apply ModuleExpression.Neutral.snd
      | (apply ModuleExpression.Neutral.appProcHoles
         all_goals try (first | assumption | (simp [ModuleExpression.IsProcTuple] <;> done)))
      | apply ModuleExpression.Neutral.app
      | apply ModuleExpression.Normal.neutral)

/-- Syntax-directed closer for `Normal m` / `Neutral m`: peels the constructor matching `m`'s
    head, disambiguating `.app`'s two constructors by checking whether the function side is a
    literal `.procHoles` node, and leaves whatever it cannot close open. Fails outright if it
    cannot make even one step of progress (e.g. `Neutral (.pair _ _)`, which no constructor can
    ever produce) rather than silently no-op'ing. See `normalmodule!` for a variant that fails
    loudly with a diagnosed reason on *every* unclosed goal, not just a wholly-stuck one. -/
macro "normalmodule" : tactic =>
  `(tactic| (normalmoduleStep; repeat' normalmoduleStep))

open Lean Elab Tactic Meta in
/-- Describe why a single leftover goal (from `normalmodule`'s core script) couldn't be closed.
    Recognises the shapes that script can actually leave behind: a `¬ IsProcTuple arg` residual
    (the `.appProcHoles` side condition), a `Neutral m` residual whose head is a `Normal`-only
    constructor (a genuine impossibility — that shape is never neutral), and a bare `Normal`/
    `Neutral` of an opaque free subterm (no matching hypothesis in scope). Falls back to the raw
    goal for anything else. -/
private def describeStuckNormalModuleGoal (g : MVarId) : MetaM MessageData := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``Not 1 then
    let inner := ty.getAppArgs[0]!
    if inner.isAppOfArity ``ModuleExpression.IsProcTuple 2 then
      let arg := inner.getAppArgs[1]!
      return m!"could not show `{arg}` is not a hole-free procedure tuple (needed so the \
        `.procHoles`-applied-to-`{arg}` node stays stuck, i.e. genuinely `Neutral`)"
  -- `Normal`/`Neutral`'s constructors all carry the ambient `[ProgramSpec]` as their first
  -- (instance-implicit) argument, hence arity `1 + 1` below.
  if ty.isAppOfArity ``ModuleExpression.Neutral 2 then
    let m := ty.getAppArgs[1]!
    let head := m.getAppFn
    if head.isConstOf ``ModuleExpression.unit then
      return m!"`.unit` is always `Normal` (via `.unit`), never `Neutral` — it has no \
        variable/`.procHoles`-application head for a redex to get stuck on"
    else if head.isConstOf ``ModuleExpression.proc then
      return m!"`.proc _` is always `Normal` (via `.proc`), never `Neutral`"
    else if head.isConstOf ``ModuleExpression.procHoles then
      return m!"`.procHoles _ _` is always `Normal` (via `.procHoles`) when bare; it's only \
        ever `Neutral` once applied to an argument (`.app`), never on its own"
    else if head.isConstOf ``ModuleExpression.pair then
      return m!"`.pair _ _` is always `Normal` (via `.pair`), never `Neutral`"
    else if head.isConstOf ``ModuleExpression.abs then
      return m!"`.abs _` is always `Normal` (via `.abs`), never `Neutral`"
    else if m.isFVar then
      return m!"`{m}` is an opaque subterm; no `Normal`/`Neutral` hypothesis for it is in \
        scope (`assumption` failed)"
  if ty.isAppOfArity ``ModuleExpression.Normal 2 then
    let m := ty.getAppArgs[1]!
    if m.isFVar then
      return m!"`{m}` is an opaque subterm; no `Normal`/`Neutral` hypothesis for it is in \
        scope (`assumption` failed)"
  return m!"could not close:\n{← ppGoal g}"

open Lean Elab Tactic Meta in
/-- `normalmodule`, but fails loudly instead of leaving unclosed goals open. Not fail-fast: it
    still runs the core script to completion (closing everything it can) before reporting, one
    "Cannot show ‹original goal›: ‹reason›" line per leftover goal, with the reason coming from
    `describeStuckNormalModuleGoal`. -/
elab "normalmodule!" : tactic => do
  let origGoal ← getMainGoal
  let origType ← origGoal.withContext (instantiateMVars (← origGoal.getType))
  let numSiblings := (← getGoals).length - 1
  evalTactic (← `(tactic| repeat' normalmoduleStep))
  let after ← getGoals
  let leftover := after.take (after.length - numSiblings)
  unless leftover.isEmpty do
    let lines ← leftover.mapM fun g => do
      return m!"Cannot show {origType}: {← describeStuckNormalModuleGoal g}"
    throwError MessageData.joinSep lines "\n\n"

/-! ### Smoke tests -/

example : ModuleExpression.Normal .unit := by normalmodule

example {sig : ProcedureSignature} (p : Procedure sig) :
    ModuleExpression.Normal (.proc p) := by normalmodule

example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) :
    ModuleExpression.Normal (.procHoles ne p) := by normalmodule

example : ModuleExpression.Normal (.var 3 : ModuleExpression) := by normalmodule

example (a b : ModuleExpression) (ha : a.Normal) (hb : b.Normal) :
    ModuleExpression.Normal (.pair a b) := by normalmodule

example (body : ModuleExpression) (hbody : body.Normal) :
    ModuleExpression.Normal (.abs body) := by normalmodule

-- `.app` of a bare `.procHoles` node to a non-tuple normal argument: the `.appProcHoles` branch.
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) :
    ModuleExpression.Neutral (.app (.procHoles ne p) (.var 0)) := by normalmodule

-- `.app` of a genuine variable head: the `.app` branch, not `.appProcHoles`.
example (arg : ModuleExpression) (harg : arg.Normal) :
    ModuleExpression.Neutral (.app (.var 0) arg) := by normalmodule

example : ModuleExpression.Neutral (.fst (.var 0 : ModuleExpression)) := by normalmodule

-- `.pair _ _` can never be `Neutral` (only `Normal`); no branch of `normalmodule`'s core script
-- applies to this goal at all, so it now fails outright (rather than silently leaving the goal
-- untouched) — the error is `first`'s report of its last alternative's failure.
/-- error: Tactic `apply` failed: could not unify the conclusion of `@ModuleExpression.Normal.neutral`
  ModuleExpression.Normal ?e
with the goal
  (a.pair b).Neutral

Note: The full type of `@ModuleExpression.Normal.neutral` is
  ∀ [inst : ProgramSpec] {e : ModuleExpression}, e.Neutral → e.Normal

inst✝ : ProgramSpec
a b : ModuleExpression
⊢ (a.pair b).Neutral -/
#guard_msgs (whitespace := lax) in
example (a b : ModuleExpression) : ModuleExpression.Neutral (.pair a b) := by
  normalmodule

-- `normalmodule!` fails loudly on the same goal, pinpointing *why* `.pair` can't be `Neutral`.
/-- error: Cannot show (a.pair b).Neutral: `.pair _ _` is always `Normal` (via `.pair`), never `Neutral` -/
#guard_msgs (whitespace := lax) in
example (a b : ModuleExpression) : ModuleExpression.Neutral (.pair a b) := by
  normalmodule!

/-- error: Cannot show ModuleExpression.unit.Neutral: `.unit` is always `Normal` (via `.unit`), never `Neutral` — it has no variable/`.procHoles`-application head for a redex to get stuck on -/
#guard_msgs (whitespace := lax) in
example : ModuleExpression.Neutral (.unit : ModuleExpression) := by
  normalmodule!

/-- error: Cannot show (ModuleExpression.proc p).Neutral: `.proc _` is always `Normal` (via `.proc`), never `Neutral` -/
#guard_msgs (whitespace := lax) in
example {sig : ProcedureSignature} (p : Procedure sig) :
    ModuleExpression.Neutral (.proc p) := by
  normalmodule!

/-- error: Cannot show (ModuleExpression.procHoles ne p).Neutral: `.procHoles _ _` is always `Normal` (via `.procHoles`) when bare; it's only ever `Neutral` once applied to an argument (`.app`), never on its own -/
#guard_msgs (whitespace := lax) in
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) :
    ModuleExpression.Neutral (.procHoles ne p) := by
  normalmodule!

/-- error: Cannot show body.abs.Neutral: `.abs _` is always `Normal` (via `.abs`), never `Neutral` -/
#guard_msgs (whitespace := lax) in
example (body : ModuleExpression) : ModuleExpression.Neutral (.abs body) := by
  normalmodule!

-- Opaque subterm, no hypothesis: `assumption` fails, no constructor matches an fvar head.
/-- error: Cannot show m.Normal: `m` is an opaque subterm; no `Normal`/`Neutral` hypothesis for it is in scope (`assumption` failed) -/
#guard_msgs (whitespace := lax) in
example (m : ModuleExpression) : ModuleExpression.Normal m := by
  normalmodule!

-- The `.appProcHoles` side condition, genuinely undecidable: `arg` is opaque (so `decide` can't
-- reduce it) and only `Normal arg` is in context, not `¬ IsProcTuple arg`.
/-- error: Cannot show ((ModuleExpression.procHoles ne p).app arg).Neutral: could not show `arg` is not a hole-free procedure tuple (needed so the `.procHoles`-applied-to-`arg` node stays stuck, i.e. genuinely `Neutral`) -/
#guard_msgs (whitespace := lax) in
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) (arg : ModuleExpression) (harg : arg.Normal) :
    ModuleExpression.Neutral (.app (.procHoles ne p) arg) := by
  normalmodule!

/-! ## `reduce_simp`

Rejected approach (kept here as a warning, not a plan): configuring plain `simp` with
`reduce_of_normal`/`reduce_step`/`reduce_pair_cong`/etc. as a lemma set plus a custom
discharger. It *looked* declarative and simple, but tuning it was pure trial-and-error —
`reduce_step`-shaped lemmas (result determined only by a hypothesis, not the LHS pattern)
silently refuse to fire at all under `simp`, and unconditional lemmas like the old (now-removed)
`reduce_app` compete with `reduce_beta` in an order-sensitive way that only showed up
empirically. None of that is
predictable from reading the tactic; it has to be discovered by testing, which is exactly the
failure mode to avoid.

Actual design: a small, fully explicit, deterministic tactic (`reduce_simp_head`) that performs
*one* reduction step on a goal of shape `ModuleExpression.reduce x = ?m` — every branch is a
plain `apply`/`assumption`, no `simp`, no discharger, nothing whose behavior depends on lemma
declaration order or internal heuristics. Then a thin `simproc` wrapper runs `reduce_simp_head`
at each `reduce _` site and hands the single resulting step to `simp`'s traversal machinery,
which *is* reliable (the earlier failures were all in simp's conditional-rewrite *discharge*
step, not its ordinary congruence-based subterm traversal) — so it naturally keeps visiting
freshly-exposed `reduce _` subterms without any extra looping logic on our part.

`reduce_simp_head`'s branches, matching `ModuleExpression`'s 9 constructors:
* `.app (.abs _) _` (a β-redex): `reduce_beta`.
* `.fst (.pair _ _)` / `.snd (.pair _ _)`: `reduce_fst`/`reduce_snd`.
* A context hypothesis `x.ReductionStep n` / `x.MultiStepReduction n` / `convertible x n`:
  `reduce_step`/`reduce_multiStepReduction`/`reduce_convertible` applied, `n` pinned by
  `assumption` (this works because `apply`'s unification handles an output metavariable
  determined only by a later hypothesis just fine — unlike `simp`'s conditional rewriting, which
  is where the earlier design broke).
* A direct `x.reduce = n` hypothesis: `assumption`.
* `.pair a b` / `.app a b` / `.abs a` (general case, not caught by the direct rules above —
  covers e.g. a neutral `.app` whose argument still has work to do): `reduce_pair_cong`/
  `reduce_app_cong`/`reduce_abs_cong`, whose side conditions `reduce a = ?a'` (etc.) are filled
  by *recursively calling `reduce_simp_head`* — genuine recursion, not simp discharge.
* `.fst e` / `.snd e` for `e` not literally `.pair`-shaped yet: `reduce_fst_cong`/
  `reduce_snd_cong`, same recursive-fill pattern.
* Otherwise (`.unit`/`.proc`/`.procHoles`/`.var`, or any of the above once fully decomposed):
  `reduce_of_normal`, with `normalmodule!` proving the `Normal x` side condition. Fails loudly
  (via `normalmodule!`) if `x` isn't actually normal and no earlier branch matched — which means
  every one-step call either succeeds or points at a genuine gap in the branch list, not a
  silent no-op.

Each branch produces *one* step, so its result can itself still be `reduce`-headed (e.g.
`reduce_beta`'s RHS is `reduce (body.substitute arg)`, not a fully collapsed value) — that's
intentional, matching the "single reduction step" contract; full normalization comes from the
`simproc` below re-visiting whatever it exposes. -/

syntax "reduce_simp_head" : tactic

macro_rules
  | `(tactic| reduce_simp_head) =>
    `(tactic|
        (-- `reduce_beta`'s RHS, `body.substitute arg`, is *not* automatically reduced to a plain
         -- `ModuleExpression` constructor tree — `substitute` is a separate structurally-recursive
         -- `def`, and every branch below matches on literal constructors. Unfold it first (safe,
         -- terminates: purely structural on the `ModuleExpression` argument, no loops).
         try simp only [ModuleExpression.substitute, ModuleExpression.substituteSimultaneously,
           ModuleExpression.variableSubstitution, ModuleExpression.liftSubst]
         first
         | apply ModuleExpression.reduce_beta
         | apply ModuleExpression.reduce_fst
         | apply ModuleExpression.reduce_snd
         | (apply ModuleExpression.reduce_step; assumption)
         | (apply ModuleExpression.reduce_multiStepReduction; assumption)
         | (apply ModuleExpression.reduce_convertible; assumption)
         | assumption
         -- Tried *before* structural decomposition: if the whole term is already `Normal`
         -- outright (e.g. after a recursive call below has already simplified its components),
         -- stop here rather than always re-decomposing via `.pair`/`.app`/`.abs`-cong, which
         -- would keep re-deriving the same answer without ever collapsing the `reduce` wrapper.
         | (apply ModuleExpression.reduce_of_normal; normalmodule!)
         -- `apply`, not `refine ... ?_ rfl`: `refine` tries to eagerly resolve the *other*
         -- implicit (`a'`/`b'`) at refine-time and fails ("don't know how to synthesize implicit
         -- argument"), since nothing pins it down yet apart from the later goal. `apply` defers
         -- both hypotheses to goals normally, so they can just be handled positionally.
         | (apply ModuleExpression.reduce_pair_cong; reduce_simp_head; rfl) -- pair-left
         | (apply ModuleExpression.reduce_pair_cong; rfl; reduce_simp_head) -- pair-right
         | (apply ModuleExpression.reduce_app_cong; reduce_simp_head; rfl) -- app-left
         | (apply ModuleExpression.reduce_app_cong; rfl; reduce_simp_head) -- app-right
         | (apply ModuleExpression.reduce_abs_cong; reduce_simp_head)
         | (apply ModuleExpression.reduce_fst_cong; reduce_simp_head)
         | (apply ModuleExpression.reduce_snd_cong; reduce_simp_head)))

/-! ### `reduce_simp_head` smoke tests

Written as `∃ m, reduce x = m`, proved by `⟨_, by reduce_simp_head⟩`: the witness `_` is a
genuine metavariable the tactic assigns via unification, unlike `example : reduce x = _ := ...`
directly (there, the `_` sits in the *stated type*, which Lean fully elaborates — including
resolving its own holes — before the tactic block ever runs, so it can't be left for the tactic
to fill; confirmed empirically, "don't know how to synthesize placeholder"). The anonymous
constructor's fields, by contrast, are genuinely elaborated together with the tactic proof. -/

example : ∃ m, ModuleExpression.reduce (.fst (.pair .unit .unit)) = m := ⟨_, by reduce_simp_head⟩
example : ∃ m, ModuleExpression.reduce (.app (.abs .unit) .unit) = m := ⟨_, by reduce_simp_head⟩

example (m n : ModuleExpression) (h : m.ReductionStep n) :
    ∃ m', ModuleExpression.reduce m = m' := ⟨_, by reduce_simp_head⟩

-- General `.pair` case: recurses into both components independently.
example (a b : ModuleExpression) (ha : a.Normal) (hb : b.Normal) :
    ∃ m, ModuleExpression.reduce (.pair a b) = m := ⟨_, by reduce_simp_head⟩

-- Base case, no redex anywhere: falls through to `reduce_of_normal` + `normalmodule!`.
example : ∃ m, ModuleExpression.reduce (.unit : ModuleExpression) = m := ⟨_, by reduce_simp_head⟩

open Lean Meta Simp in
/-- Run `reduce_simp_head` on a fresh `ModuleExpression.reduce x = ?m` goal and report the result
    as a `Simp.Step`. Returns `.continue` (no rewrite) if `reduce_simp_head` can't make even one
    step of progress — matching `moduletyping`/`normalmodule`'s leniency: an unreducible term
    (e.g. containing an opaque free variable with no matching hypothesis) is left as-is rather
    than treated as an error. -/
private def reduceSimpProcImpl (e : Lean.Expr) : SimpM Simp.Step := do
  try
    let mTarget ← mkFreshExprMVar (← inferType e)
    let target ← mkEq e mTarget
    let goalMVar ← mkFreshExprMVar target
    let remaining ← Elab.Tactic.run goalMVar.mvarId!
      (Elab.Tactic.evalTactic (← `(tactic| reduce_simp_head))) |>.run'
    if !remaining.isEmpty then
      return .continue
    let m ← instantiateMVars mTarget
    let proof ← instantiateMVars goalMVar
    return .visit { expr := m, proof? := some proof }
  catch _ =>
    -- `reduce_simp_head` genuinely throwing (rather than just leaving goals open) means every
    -- branch failed outright — e.g. `normalmodule!` couldn't prove `Normal` for an opaque
    -- subterm with no matching hypothesis. Lenient like `moduletyping`/`normalmodule`: leave the
    -- site untouched rather than aborting the whole `reduce_simp` call.
    return .continue

/- The obvious next step, `simproc reduceSimp (ModuleExpression.reduce _) := reduceSimpProcImpl`,
   doesn't work: the `simproc` command elaborates its *pattern* in an isolated `TermElabM`
   (`Lean.Elab.elabSimprocPattern`, confirmed by reading the source), disconnected from this
   section's `variable [ProgramSpec]` — and then force-synthesizes every instance-implicit in it
   (`Term.synthesizeSyntheticMVars`), so it always fails to find a `ProgramSpec` (there isn't a
   global one; that's the whole point of it being a section variable). This isn't a workaround-
   able syntax issue, it's structural: *no* `[ProgramSpec]`-parameterized declaration can be
   registered as a discrimination-tree-keyed `simproc` this way.

   So `reduce_simp` doesn't register anything globally. It drives `Lean.Meta.Simp.main` itself,
   at tactic-run time (where a concrete `ProgramSpec` *is* available, from the calling goal's own
   context), passing a custom `Simp.Methods.post` hook instead of a `Simprocs`/discrimination-tree
   entry — `post` is a plain `Expr → SimpM Step`, checked by hand (`isAppOfArity`) against the
   already-elaborated `Expr`s simp's traversal visits, no pattern registration involved at all.
   Simp's own bottom-up traversal (confirmed reliable all along — only its conditional-rewrite
   *discharge* step was ever the problem) still does the "keep visiting exposed subterms" work. -/
open Lean Meta Elab Tactic in
/-- Fully normalize `reduce m` subterms via `reduce_simp_head`, repeatedly, including inside
    freshly-exposed nested `reduce`s (handled by `simp`'s own subterm traversal, not by this
    tactic). Lenient: leaves whatever it can't reduce untouched; closes the goal outright if it
    simplifies all the way to `True`. -/
elab "reduce_simp" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let simpTheorems ← Lean.Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
    let congrTheorems ← getSimpCongrTheorems
    let ctx ← Simp.mkContext (simpTheorems := #[simpTheorems]) (congrTheorems := congrTheorems)
    -- `post`: try our own hook first, then fall through to `Simp.postDefault` (no simprocs of
    -- its own, but it's what actually consults `ctx.simpTheorems` — needed so e.g. a fully
    -- reduced `x = x` goal collapses to `True` via `eq_self`, which a bare custom `post`
    -- wouldn't do on its own since it doesn't touch `ctx.simpTheorems` at all).
    let methods : Simp.Methods :=
      { pre := Simp.preDefault #[]
        post :=
          (fun e => do
            if e.isAppOfArity ``ModuleExpression.reduce 2 then
              reduceSimpProcImpl e
            else
              return .continue) >> Simp.postDefault #[] }
    let (r, _) ← Simp.main target ctx (methods := methods)
    if r.expr.isConstOf ``True then
      match r.proof? with
      | some proof => goal.assign (← mkOfEqTrue proof)
      | none => goal.assign (mkConst ``True.intro)
      replaceMainGoal []
    else
      replaceMainGoal [← applySimpResultToTarget goal target r]

/-! ### Smoke tests -/

example : ModuleExpression.reduce (.fst (.pair .unit .unit)) = .unit := by reduce_simp

example : ModuleExpression.reduce (.app (.abs .unit) .unit) = .unit := by reduce_simp

example (m n : ModuleExpression) (h : m.ReductionStep n) (hn : n.Normal) :
    ModuleExpression.reduce m = n := by
  reduce_simp

example (m n : ModuleExpression) (h : m.MultiStepReduction n) (hn : n.Normal) :
    ModuleExpression.reduce m = n := by
  reduce_simp

example (m n : ModuleExpression) (h : ModuleExpression.convertible m n) (hn : n.Normal) :
    ModuleExpression.reduce m = n := by
  reduce_simp

example (m : ModuleExpression) (h : ModuleExpression.reduce m = .unit) :
    ModuleExpression.reduce (.fst (.pair m .unit)) = .unit := by
  reduce_simp

-- The pair as a whole isn't (yet provably) `Normal` — its first component
-- `.fst (.pair .unit .unit)` is a genuine redex — so `reduceSimp` can't collapse it in one visit
-- at the top; `reduce_pair_cong` (inside `reduce_simp_head`) peels each component, and `simp`'s
-- traversal revisits the result, which *is* now directly `Normal`.
example (b : ModuleExpression) (hb : b.Normal) :
    ModuleExpression.reduce (.pair (.fst (.pair .unit .unit)) b) = .pair .unit b := by
  reduce_simp

-- A `reduce ...` term whose argument itself already contains a nested `reduce`: `simp`'s
-- traversal must simplify that inner occurrence too, not just the outer one.
example (a c : ModuleExpression) (ha : a.Normal) (hc : c.Normal) :
    ModuleExpression.reduce (.pair (ModuleExpression.reduce a) c) = .pair a c := by
  reduce_simp

/- # Modules -/

structure Module (T : ModuleTypeRep) where
  expression : ModuleExpression
  typed : expression.HasType [] T
  normal : expression.NormalClosed

/-- Build a `Module` from a well-typed closed expression by normalising it. -/
noncomputable def ModuleExpression.toModule {T : ModuleTypeRep}
    (m : ModuleExpression) (h : m.HasType [] T := by moduletyping!) : Module T :=
  ⟨m.reduce, m.reduce_hasType h, m.reduce_normalClosed h⟩

noncomputable instance : CoeFun (Module (.arr T U)) (fun _ ↦ Module T → Module U) where
  coe f x := (f.expression.app x.expression).toModule (.app f.typed x.typed)

noncomputable def Module.fst' {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toModule (.fst m.typed)

noncomputable def Module.snd' {T U} (m : Module (.prod T U)) : Module U :=
  m.expression.snd.toModule (.snd m.typed)

noncomputable def Module.pair' {T U} (m1 : Module T) (m2 : Module U) : Module (.prod T U) :=
  (m1.expression.pair m2.expression).toModule (.pair m1.typed m2.typed)

@[ext]
theorem Module.ext {T} {m1 m2 : Module T} (h : m1.expression = m2.expression) :
  m1 = m2 := by
  obtain ⟨e1, t1, n1⟩ := m1; obtain ⟨e2, t2, n2⟩ := m2
  simp only at h; subst h; rfl

@[simp]
theorem Module.expression_fst' {T U} (m : Module (.prod T U)) :
    m.fst'.expression = m.expression.fst.reduce := rfl

@[simp]
theorem Module.expression_snd' {T U} (m : Module (.prod T U)) :
    m.snd'.expression = m.expression.snd.reduce := rfl


@[simp]
theorem Module.toModule_expression {T} (m : ModuleExpression) (h : m.HasType [] T) :
    (m.toModule h).expression = m.reduce := rfl

@[simp]
theorem Module.reduce_expression {T} (m : Module T) :
  m.expression.reduce = m.expression :=
  ModuleExpression.reduce_of_stuck m.normal.normal.stuck

/-- A module's expression is closed, so a substitution leaves it alone. -/
@[simp]
theorem Module.substituteSimultaneously_expression {T} (m : Module T)
    (σ : Nat → ModuleExpression) :
    m.expression.substituteSimultaneously σ = m.expression :=
  m.typed.substituteSimultaneously_eq_self (by simp)

/-- Pairing two modules pairs their expressions — no `reduce` left over, both being normal. -/
theorem Module.expression_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).expression = .pair m1.expression m2.expression :=
  ModuleExpression.reduce_of_normal (.pair m1.normal.normal m2.normal.normal)

/-- Reducing a pair componentwise: if the components reduce to the expressions of the modules
    `m1`/`m2`, the pair reduces to the expression of their `Module.pair'`.  The engine behind the
    `X.apply_simp` lemmas of the `module` command (`GaudisCrypt/Language/Syntax2.lean`): it turns a
    `reduce` of a whole record of procedures into the record of the reduced procedures, with no
    detour through termination — normality of the *result* comes from the modules `m1`/`m2`. -/
theorem Module.reduce_pair_expression {T U} {a b : ModuleExpression}
    (m1 : Module T) (m2 : Module U)
    (ha : a.reduce = m1.expression) (hb : b.reduce = m2.expression) :
    (ModuleExpression.pair a b).reduce = (m1.pair' m2).expression := by
  rw [ModuleExpression.reduce_pair_cong ha hb, Module.expression_pair',
    ModuleExpression.reduce_of_normal (.pair m1.normal.normal m2.normal.normal)]

@[simp]
theorem Module.fst_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).fst' = m1 := by
  ext
  change ((m1.expression.pair m2.expression).reduce.fst).reduce = m1.expression
  rw [ModuleExpression.reduce_of_stuck
        (ModuleExpression.NormalClosed.pair m1.normal m2.normal).normal.stuck,
      ModuleExpression.reduce_fst, m1.reduce_expression]

@[simp]
theorem Module.snd_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).snd' = m2 := by
  ext
  change ((m1.expression.pair m2.expression).reduce.snd).reduce = m2.expression
  rw [ModuleExpression.reduce_of_stuck
        (ModuleExpression.NormalClosed.pair m1.normal m2.normal).normal.stuck,
      ModuleExpression.reduce_snd, m2.reduce_expression]


theorem Module.pair_fst_snd' : (Module.fst' m).pair' (Module.snd' m) = m := by
  obtain ⟨a, b, he⟩ := ModuleExpression.pair_type_is_pair m.typed m.normal
  have hn : (ModuleExpression.pair a b).NormalClosed := he ▸ m.normal
  obtain ⟨hna, hnb⟩ : a.NormalClosed ∧ b.NormalClosed := by
    cases hn with | pair x y => exact ⟨x, y⟩
  ext
  change ((m.expression.fst.reduce).pair (m.expression.snd.reduce)).reduce = m.expression
  rw [he, ModuleExpression.reduce_fst, ModuleExpression.reduce_snd,
      ModuleExpression.reduce_of_stuck hna.normal.stuck,
      ModuleExpression.reduce_of_stuck hnb.normal.stuck,
      ModuleExpression.reduce_of_stuck hn.normal.stuck]


abbrev Module.Unit := Module .unit
noncomputable def Module.unit : Module .unit := ModuleExpression.unit.toModule .unit

class IsModule (T : Type _) where
  moduleTypeRep : ModuleTypeRep
  isModule : T = Module moduleTypeRep := by rfl

@[reducible]
instance : IsModule (Module t) where
  moduleTypeRep := t
  isModule := rfl

def Module.moduleTypeRep (T : Type _) [inst : IsModule T] := inst.moduleTypeRep

def Module.cast (T : Type _) [inst : IsModule T] (m : T) : Module (Module.moduleTypeRep T) :=
  inst.isModule ▸ m

def Module.cast' (T : Type _) [inst : IsModule T] (m : Module (Module.moduleTypeRep T)) : T :=
  inst.isModule.symm ▸ m

def Module.Arr (M : Type _) (N : Type _) [IsModule M] [IsModule N] : Type _ :=
  Module (ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N))

instance (M : Type _) (N : Type _) [IsModule M] [IsModule N] : IsModule (Module.Arr M N) where
  moduleTypeRep := ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N)
  isModule := rfl

def Module.Proc (sig : ProcedureSignature) : Type _ :=
  Module (ModuleTypeRep.proc sig)

instance {sig} : IsModule (Module.Proc sig) where
  moduleTypeRep := ModuleTypeRep.proc sig

noncomputable def Module.app' (m : Module (.arr A B)) (m' : Module A) : Module B :=
  (m.expression.app m'.expression).toModule (.app m.typed m'.typed)

noncomputable def Module.app {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m : Module.Arr M N) (m' : M) : N :=
  have hMN : Module.Arr M N =
      Module (ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Arr]
  iN.isModule.symm ▸ Module.app' (hMN ▸ m) (iM.isModule ▸ m')

theorem Module.cast_app [IsModule M] [IsModule N] (a : Module.Arr M N) (b : M) :
    Module.cast _ (Module.app a b)
      = Module.app' (Module.cast (Module.Arr M N) a) (Module.cast M b) := by
  unfold Module.cast Module.app
  simp only [eqRec_eq_cast, cast_cast, cast_eq]
  rfl

def Module.Prod (M : Type _) (N : Type _) [IsModule M] [IsModule N] : Type _ :=
  Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N))

instance (M : Type _) (N : Type _) [IsModule M] [IsModule N] : IsModule (Module.Prod M N) where
  moduleTypeRep := ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)
  isModule := rfl

noncomputable def Module.fst {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m : Module.Prod M N) : M :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  iM.isModule.symm ▸ Module.fst' (hMN ▸ m)

noncomputable def Module.snd {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m : Module.Prod M N) : N :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  iN.isModule.symm ▸ Module.snd' (hMN ▸ m)

noncomputable def Module.pair {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m1 : M) (m2 : N) : Module.Prod M N :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  hMN ▸ Module.pair' (iM.isModule ▸ m1) (iN.isModule ▸ m2)

@[simp]
theorem Module.fst_pair {M N : Type max 1 u} [IsModule M] [IsModule N] (m1 : M) (m2 : N) :
    Module.fst (Module.pair m1 m2) = m1 := by
  simp only [Module.fst, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast, cast_eq,
    Module.fst_pair']

@[simp]
theorem Module.snd_pair {M N : Type max 1 u} [IsModule M] [IsModule N] (m1 : M) (m2 : N) :
    Module.snd (Module.pair m1 m2) = m2 := by
  simp only [Module.snd, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast, cast_eq,
    Module.snd_pair']

theorem Module.pair_fst_snd {M N : Type max 1 u} [IsModule M] [IsModule N] (m : Module.Prod M N) :
    Module.pair (Module.fst m) (Module.snd m) = m := by
  simp only [Module.fst, Module.snd, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast,
    cast_eq, Module.pair_fst_snd']

noncomputable def Module.proc {sig} (p : Procedure sig) : Module.Proc sig :=
  (ModuleExpression.proc p).toModule (.proc p)

/-- Canonical forms at procedure type: a *closed normal* expression of type `.proc sig` is
    literally a `.proc p` node. -/
theorem proc_type_is_proc {sig : ProcedureSignature}
    {m : ModuleExpression} (ht : m.HasType [] (.proc sig)) (h : m.NormalClosed) :
    ∃ p : Procedure sig, m = .proc p := by
  cases h with
  | «proc» =>
      rename_i p
      injection ht.proc_inv with hs
      subst hs
      exact ⟨p, rfl⟩
  | procHoles => cases ht
  | abs _ => cases ht
  | pair _ _ => cases ht
  | unit => cases ht

/-- The procedure of a proc-typed module — the inverse of `Module.proc`.  (`Classical.choose`
    only escapes the Prop-to-data restriction; the witness is unique — see
    `Module.procedure_spec` and `Module.procedure_proc`.) -/
-- TODO don't use choose but pattern match
-- TODO use Module.Proc
noncomputable def Module.procedure
    {sig : ProcedureSignature} (m : Module (.proc sig)) : Procedure sig :=
  (proc_type_is_proc m.typed m.normal).choose

/-- `Module.procedure` is characterized by its defining equation (the witness of
    `proc_type_is_proc` is unique by constructor injectivity). -/
-- TODO use Module.Proc
theorem Module.procedure_spec
    {sig : ProcedureSignature} (m : Module (.proc sig)) :
    m.expression = .proc m.procedure :=
  (proc_type_is_proc m.typed m.normal).choose_spec

/-- Round-trip: wrapping a procedure as a module and extracting recovers it. -/
-- TODO use Module.Proc
@[simp] theorem Module.procedure_proc
    {sig : ProcedureSignature} (p : Procedure sig) :
    ((ModuleExpression.proc p).toModule (.proc p)).procedure = p := by
  have h1 : ((ModuleExpression.proc p).toModule (.proc p)).expression = .proc p :=
    Module.reduce_expression ⟨.proc p, .proc p, .proc⟩
  have h2 := Module.procedure_spec ((ModuleExpression.proc p).toModule (.proc p))
  rw [h1] at h2
  injection h2 with hsig h
  exact h.symm

/-- Renaming by a function that's pointwise the identity is the identity, regardless of `ρ`'s
    behavior elsewhere (needed below since `IsRenaming [] Δ ρ` holds vacuously for *any* `ρ`,
    but we specifically want the renamed term to be syntactically unchanged). -/
private theorem ModuleExpression.rename_id :
    ∀ (m : ModuleExpression) (ρ : Nat → Nat), (∀ n, ρ n = n) → m.rename ρ = m := by
  intro m
  induction m with
  | unit => intro ρ _; rfl
  | proc p => intro ρ _; rfl
  | procHoles ne p => intro ρ _; rfl
  | var n => intro ρ hρ; simp [ModuleExpression.rename, hρ]
  | app f a ihf iha => intro ρ hρ; simp [ModuleExpression.rename, ihf ρ hρ, iha ρ hρ]
  | fst e ih => intro ρ hρ; simp [ModuleExpression.rename, ih ρ hρ]
  | snd e ih => intro ρ hρ; simp [ModuleExpression.rename, ih ρ hρ]
  | pair a b iha ihb => intro ρ hρ; simp [ModuleExpression.rename, iha ρ hρ, ihb ρ hρ]
  | abs body ih =>
      intro ρ hρ
      simp only [ModuleExpression.rename]
      congr 1
      apply ih
      intro n
      cases n with
      | zero => rfl
      | succ n' => simp [ModuleExpression.liftRen, hρ]

/-- A closed term (well-typed in the empty context) is well-typed in *any* context: `Δ = []`
    makes `IsRenaming [] Δ' ρ` hold vacuously for any `ρ`, so picking `ρ := id` and cancelling
    the resulting `rename id` via `rename_id` gives back `m` itself, unchanged, in the wider
    context `Δ'`. -/
private theorem ModuleExpression.HasType.weaken_of_empty {m : ModuleExpression} {T : ModuleTypeRep}
    (h : m.HasType [] T) (Δ : ModuleContext) : m.HasType Δ T := by
  have hIsRen : ModuleExpression.HasType.IsRenaming [] Δ id :=
    fun {n} hn => absurd hn (Nat.not_lt_zero n)
  have hren := h.rename hIsRen
  rwa [ModuleExpression.rename_id m id (fun _ => rfl)] at hren

/-- A module's expression is well-typed in *any* context, not just the empty one — it is closed.
This is what lets `moduletyping` type an expression built from already-formed modules (whose
leaves are `m.expression` rather than a `HasType` constructor). -/
theorem Module.typed_weaken {T : ModuleTypeRep} (m : Module T) (Δ : ModuleContext) :
    m.expression.HasType Δ T := m.typed.weaken_of_empty Δ

noncomputable def Module.const {T U} [IsModule T] [iu : IsModule U] (m : U) : Module.Arr T U :=
  let expr : ModuleExpression := (iu.isModule ▸ m).expression
  have h : expr.HasType [] (Module.moduleTypeRep U) := by
    exact (iu.isModule ▸ m).typed
  let abs : ModuleExpression := .abs expr
  have habs :
      abs.HasType [] (ModuleTypeRep.arr (Module.moduleTypeRep T) (Module.moduleTypeRep U)) := by
    exact .abs (h.weaken_of_empty _)
  abs.toModule habs

noncomputable def Module.procWithHoles {holes : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles holes sig) :
    Module.Arr (Module holes.toModuleTypeRepTuple) (Module.Proc sig) :=
  match h : holes with
  | .empty =>
    Module.const (Module.proc p)
  | .append x y =>
    show Module (.arr (HoleSigs.append x y).toModuleTypeRepTuple (.proc sig))
    from (ModuleExpression.procHoles (by trivial) p).toModule

/- # Demo -/



section Demo

axiom sig : ProcedureSignature
def TestModule := Module (ModuleTypeRep.prod (ModuleTypeRep.proc sig) (ModuleTypeRep.proc sig))

noncomputable
def TestModule.main (m : TestModule) : Module (ModuleTypeRep.proc sig) := m.fst'
noncomputable
def TestModule.aux (m : TestModule) : Module (ModuleTypeRep.proc sig) := m.snd'

structure TestModuleStruct where
  main : Module (ModuleTypeRep.proc sig)
  aux : Module (ModuleTypeRep.proc sig)

noncomputable
def TestModuleStruct.destruct (str : TestModuleStruct) : TestModule :=
  str.main.pair' str.aux

noncomputable
def TestModule.mk (str : TestModuleStruct) : TestModule := str.main.pair' str.aux

axiom testMain : Module (ModuleTypeRep.proc sig)
axiom testAux : Module (ModuleTypeRep.proc sig)

noncomputable
def myMod := TestModule.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModule.main, myMod, TestModule.mk]


end Demo

end GaudisCrypt
