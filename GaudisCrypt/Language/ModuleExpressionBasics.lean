import GaudisCrypt.Language.Programs
import Mathlib.Data.List.AList
import Mathlib.Logic.Equiv.Defs

/-! # Module expressions, basics

The raw calculus underlying modules: `ModuleTypeRep` (the types), the untyped syntax tree
`ModuleExpression` with extrinsic typing (`ModuleExpression.HasType`), de Bruijn
renaming/substitution, call-by-value reduction with its normal forms, and the deciding tactics
`moduletyping` and `normalmodule`.

This is the part of the development that depends neither on confluence
(`ModuleExpressionConfluence.lean`) nor on normalization
(`ModuleExpressionNormalization.lean`); their consequences — the `reduce` theory and the
`reduce_simp` tactic — live in `ModuleExpression.lean`, which is what downstream modules import.

`Modules.lean` builds `Module T` — a closed, well-typed, normal expression — on top of that. -/

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
  | .cons sig holes => .prod (.proc sig) (HoleSigs.toModuleTypeRepTuple holes)

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
  | .empty,               _    => .unit
  | .cons _ .empty,       inst => .pair (.proc inst) .unit
  | .cons _ (.cons ..),   inst =>
      .pair (.proc inst.1) (HoleSigs.Instantiation.toModuleExpr inst.2)

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

/-- Transitive-reflexive closure of `ReductionStep`. -/
def ModuleExpression.MultiStepReduction : ModuleExpression → ModuleExpression → Prop :=
  Relation.ReflTransGen ReductionStep

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

/-- The same for a renaming: a term only mentions the variables its context declares, so a renaming
    that is the identity on those leaves it alone.  For a *closed* term (`Δ = []`) the hypothesis is
    vacuous: `Module.rename_expression`. -/
theorem rename_eq_self {m Δ T} (h : HasType m Δ T) :
    ∀ {ρ : Nat → Nat}, (∀ n, n < Δ.length → ρ n = n) → m.rename ρ = m := by
  induction h with
  | «proc» p => intro ρ _; rfl
  | procHoles ne p => intro ρ _; rfl
  | «var» n hn => intro ρ hρ; simp [ModuleExpression.rename, hρ n hn]
  | app _ _ ihf iha => intro ρ hρ; simp [ModuleExpression.rename, ihf hρ, iha hρ]
  | fst _ ihe => intro ρ hρ; simp [ModuleExpression.rename, ihe hρ]
  | snd _ ihe => intro ρ hρ; simp [ModuleExpression.rename, ihe hρ]
  | pair _ _ iha ihb => intro ρ hρ; simp [ModuleExpression.rename, iha hρ, ihb hρ]
  | unit => intro ρ _; rfl
  | abs _ ihb =>
      intro ρ hρ
      simp only [ModuleExpression.rename]
      rw [ihb ?_]
      intro n hn
      cases n with
      | zero => rfl
      | succ n' => simp [ModuleExpression.liftRen, hρ n' (by simpa using hn)]

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
  | cons sig rest ih => exact ih


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




/-! ### Shape predicates for call-by-value reduction (untyped analogues) -/

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

/-- `toModuleExpr inst` is always a proc-tuple (untyped analogue of
    `TypedModules.toModuleTuple_isProcTuple`). -/
private theorem toModuleExpr_isProcTuple {holes : HoleSigs} (inst : holes.Instantiation) :
    (HoleSigs.Instantiation.toModuleExpr inst).IsProcTuple := by
  induction holes with
  | empty => simp [HoleSigs.Instantiation.toModuleExpr, IsProcTuple]
  | cons sig holeTail ih =>
      cases holeTail with
      | empty    => simp [HoleSigs.Instantiation.toModuleExpr, IsProcTuple]
      | cons _ _ =>
          simp only [HoleSigs.Instantiation.toModuleExpr]
          exact ih inst.2

/-- Whatever reduces has a redex, so it is not normal.  Every case is closed by inverting
    the `Normal`/`Neutral` derivation: a redex head (`.abs`, `.pair` under `.fst`/`.snd`,
    a `.procHoles` applied to a proc-tuple) is never neutral, and the congruence cases
    contradict the induction hypothesis on the reducing subterm. -/
theorem ReductionStep.not_normal {m n : ModuleExpression} (h : m.ReductionStep n) :
    ¬ m.Normal := by
  induction h with
  | beta =>
      rintro ⟨hne⟩
      cases hne with
      | app hf _ => cases hf
  | appL _ ih =>
      rintro ⟨hne⟩
      cases hne with
      | app hf _ => exact ih (.neutral hf)
      | appProcHoles _ _ _ => exact ih .procHoles
  | appR _ ih =>
      rintro ⟨hne⟩
      cases hne with
      | app _ ha => exact ih ha
      | appProcHoles _ ha _ => exact ih ha
  | lam _ ih =>
      intro hn
      cases hn with
      | neutral hne => cases hne
      | abs hb => exact ih hb
  | pairL _ ih =>
      intro hn
      cases hn with
      | neutral hne => cases hne
      | pair ha _ => exact ih ha
  | pairR _ ih =>
      intro hn
      cases hn with
      | neutral hne => cases hne
      | pair _ hb => exact ih hb
  | fstPair =>
      rintro ⟨hne⟩
      cases hne with
      | fst he => cases he
  | fst _ ih =>
      rintro ⟨hne⟩
      cases hne with
      | fst he => exact ih (.neutral he)
  | sndPair =>
      rintro ⟨hne⟩
      cases hne with
      | snd he => cases he
  | snd _ ih =>
      rintro ⟨hne⟩
      cases hne with
      | snd he => exact ih (.neutral he)
  | delta _ _ inst =>
      rintro ⟨hne⟩
      cases hne with
      | app hf _ => cases hf
      | appProcHoles _ _ hnpt => exact hnpt (toModuleExpr_isProcTuple inst)

theorem Normal.stuck {m : ModuleExpression} (h : m.Normal) : Stuck m := by
  rintro ⟨_, hstep⟩
  exact hstep.not_normal h

/-- `m` terminates: it multi-step reduces to some normal form. -/
def Terminating (m : ModuleExpression) : Prop :=
  ∃ n : ModuleExpression, n.Stuck ∧ m.MultiStepReduction n

lemma Stuck.terminating {m : ModuleExpression} (h : Stuck m) : Terminating m := ⟨m, h, .refl⟩

lemma Normal.terminating {m : ModuleExpression} (h : Normal m) : Terminating m :=
  h.stuck.terminating

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

theorem reduce_stuck {m : ModuleExpression} (ht : Terminating m) : (reduce m).Stuck := by
  rw [reduce]
  split
  · rename_i h; exact h.choose_spec.1
  · rename_i h; exact absurd ht h


theorem multiStepReduction_reduce {m : ModuleExpression} (h : Terminating m) :
    m.MultiStepReduction (reduce m) := by
  rw [reduce, dif_pos h]
  exact h.choose_spec.2

/-- Multi-step reduction refines convertibility. -/
theorem convertible_of_multiStep {a b : ModuleExpression} (h : a.MultiStepReduction b) :
    convertible a b := by
  unfold convertible
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

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

/-- `reduce` is constant on a convertible class of non-terminating expressions.  (Not `private`:
    `ModuleExpression.lean` needs it for `reduce_idempotent`/`confluence`.) -/
theorem reduce_eq_of_convertible_not_term {m n : ModuleExpression}
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
      | unit => exact ⟨⟨⟩, rfl⟩
      | pair x y => obtain ⟨A, B, heq, _, _⟩ := hty.pair_inv;
                    simp [HoleSigs.toModuleTypeRepTuple] at heq
      | proc _ => exact absurd h (by simp [IsProcTuple])
      | procHoles _ _ => exact absurd h (by simp [IsProcTuple])
      | var _ => exact absurd h (by simp [IsProcTuple])
      | app _ _ => exact absurd h (by simp [IsProcTuple])
      | fst _ => exact absurd h (by simp [IsProcTuple])
      | snd _ => exact absurd h (by simp [IsProcTuple])
      | abs _ => exact absurd h (by simp [IsProcTuple])
  | cons sig rest ih =>
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
              cases rest with
              | empty    => exact ⟨p, rfl⟩
              | cons _ _ => exact ⟨(p, instTail), rfl⟩
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
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail (.appL hbc)
  have right : (ModuleExpression.app m1' m2).MultiStepReduction (ModuleExpression.app m1' m2') := by
    induction h2 with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail (.appR hbc)
  exact left.trans right

/-- `fst` is a congruence for multi-step reduction. -/
theorem multiStepReduction_fst_cong {e e' : ModuleExpression} (h : e.MultiStepReduction e') :
    (ModuleExpression.fst e).MultiStepReduction (ModuleExpression.fst e') := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (.fst hbc)

/-- `pair` is a congruence for multi-step reduction. -/
theorem multiStepReduction_pair_cong {a a' b b' : ModuleExpression}
    (h1 : a.MultiStepReduction a') (h2 : b.MultiStepReduction b') :
    (ModuleExpression.pair a b).MultiStepReduction (ModuleExpression.pair a' b') := by
  have left : (ModuleExpression.pair a b).MultiStepReduction (ModuleExpression.pair a' b) := by
    induction h1 with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail (.pairL hbc)
  have right : (ModuleExpression.pair a' b).MultiStepReduction (ModuleExpression.pair a' b') := by
    induction h2 with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail (.pairR hbc)
  exact left.trans right

/-- A pair of stuck expressions is stuck: `pair` can only step via `pairL`/`pairR`. -/
theorem stuck_pair {a b : ModuleExpression} (ha : Stuck a) (hb : Stuck b) :
    Stuck (.pair a b) := by
  rintro ⟨n, hstep⟩
  cases hstep with
  | pairL h => exact ha ⟨_, h⟩
  | pairR h => exact hb ⟨_, h⟩

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


/-! ## `normalmodule` -/

open Lean Elab Tactic Meta in
/-- One step of `normalmodule`'s core script, factored out so `normalmodule` can require it to
    fire at least once while still repeating it leniently afterwards. A `TacticM` function
    rather than a `syntax` extension, so it does not pollute the tactic grammar; it still
    delegates to a `first | …` quotation via `evalTactic`. -/
private def normalmoduleStep : TacticM Unit := do
  evalTactic (← `(tactic| first
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
    | apply ModuleExpression.Normal.neutral))

open Lean Elab Tactic Meta in
/-- `normalmoduleStep` applied the way `repeat' normalmoduleStep` used to: run it on every goal,
    recursively on the subgoals it produces, until it fails on all of them. Always succeeds. -/
private def normalmoduleRepeat : TacticM Unit := do
  let step (g : MVarId) : TacticM (List MVarId) := do
    setGoals [g]; normalmoduleStep; getGoals
  setGoals (← Meta.repeat' step (← getGoals))

open Lean Elab Tactic Meta in
/-- Syntax-directed closer for `Normal m` / `Neutral m`: peels the constructor matching `m`'s
    head, disambiguating `.app`'s two constructors by checking whether the function side is a
    literal `.procHoles` node, and leaves whatever it cannot close open. Fails outright if it
    cannot make even one step of progress (e.g. `Neutral (.pair _ _)`, which no constructor can
    ever produce) rather than silently no-op'ing. See `normalmodule!` for a variant that fails
    loudly with a diagnosed reason on *every* unclosed goal, not just a wholly-stuck one. -/
elab "normalmodule" : tactic => do
  normalmoduleStep
  normalmoduleRepeat

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
  normalmoduleRepeat
  let after ← getGoals
  let leftover := after.take (after.length - numSiblings)
  unless leftover.isEmpty do
    let lines ← leftover.mapM fun g => do
      return m!"Cannot show {origType}: {← describeStuckNormalModuleGoal g}"
    throwError MessageData.joinSep lines "\n\n"


end GaudisCrypt
