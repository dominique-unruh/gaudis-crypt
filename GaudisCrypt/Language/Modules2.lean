import GaudisCrypt.Language.Modules

/-!
# Untyped module expressions (experimental)

The untyped module-expression calculus, split out from `Modules.lean` (whose intrinsic
development now lives in namespace `GaudisCrypt.TM`).  This file lives in `GaudisCrypt.UM`.

This file ports *every* definition and theorem of `TM` (including the `private` ones), rewritten
to the untyped setting: where the intrinsic type index carried information, the untyped statement
takes an explicit `Typed` hypothesis.  Proofs are given where they translate directly and are
`sorry` otherwise.  `reduce` is the `Terminating`/`Classical.choose` definition (not `TM`'s
well-founded-recursion one), so `TM`'s global `WellFoundedRelation ModuleExpression` instance and
WF-recursive `reduce` are *not* ported — on untyped terms that relation is not well-founded, so
porting them would be a `sorry` of a false statement.  STLC helpers that clash with `TM`'s
`private` homonyms on the shared `ModuleTypeRep`/`ProcedureWithHoles`/`ModuleContext` are renamed
(`tyToSTLC`/`pwhToSTLC`/`ctxToSTLC`).
-/

namespace GaudisCrypt.UM

open GaudisCrypt GaudisCrypt.TM

-- Re-expose the foundational (type-level) pieces of the intrinsic `TM` development so that a
-- single `open GaudisCrypt.UM` in dependents brings both these and the untyped calculus.
-- `abbrev` (not `export`) so constructor access like `ModuleTypeRep.proc` resolves.
abbrev ModuleTypeRep := GaudisCrypt.TM.ModuleTypeRep
abbrev ModuleContext := GaudisCrypt.TM.ModuleContext
abbrev ModuleContextIdx := GaudisCrypt.TM.ModuleContextIdx

variable [ProgramSpec]

/-- Untyped module expressions: the raw syntax tree of the module calculus, with no
    context/type indices.  Well-typedness is captured extrinsically by the predicate
    `ModuleExpression.Typed`.  Variables are de Bruijn indices (`Nat`); `abs` carries no
    domain annotation (the domain is recovered by `Typed`). -/
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

/-- `ModuleExpression.Typed m Δ T` holds when the untyped expression `m` is well-typed in
    module context `Δ` with type `T`.  This is the extrinsic counterpart of the indices of
    `TM.ModuleExpression`: every `TM.ModuleExpression Δ T` erases (via
    `TM.ModuleExpression.erase`) to an `m` with `Typed m Δ T`, and conversely. -/
inductive ModuleExpression.Typed : ModuleExpression → ModuleContext → ModuleTypeRep → Prop where
  | proc {Δ sig} (p : Procedure sig) : Typed (.proc p) Δ (.proc sig)
  | procHoles {Δ holes sig} (ne : holes.NonEmpty) (p : ProcedureWithHoles holes sig) :
        Typed (.procHoles ne p) Δ (.arr holes.toModuleTypeRepTuple (.proc sig))
  | var {Δ M} (i : ModuleContextIdx Δ M) : Typed (.var i.toNat) Δ M
  | app {Δ A B m n} : Typed m Δ (.arr A B) → Typed n Δ A → Typed (.app m n) Δ B
  | fst {Δ A B m} : Typed m Δ (.prod A B) → Typed (.fst m) Δ A
  | snd {Δ A B m} : Typed m Δ (.prod A B) → Typed (.snd m) Δ B
  | abs {Δ A B m} : Typed m (Δ.append A) B → Typed (.abs m) Δ (.arr A B)
  | pair {Δ A B m n} : Typed m Δ A → Typed n Δ B → Typed (.pair m n) Δ (.prod A B)
  | unit {Δ} : Typed .unit Δ .unit


namespace ModuleExpression.Typed

theorem proc_inv {Δ T sig} {p : Procedure sig} (h : Typed (.proc p) Δ T) : T = .proc sig := by
  cases h with | proc _ => rfl

theorem procHoles_inv {Δ T holes sig} {ne : holes.NonEmpty} {p : ProcedureWithHoles holes sig}
    (h : Typed (.procHoles ne p) Δ T) : T = .arr holes.toModuleTypeRepTuple (.proc sig) := by
  cases h with | procHoles _ _ => rfl

theorem var_inv {Δ T n} (h : Typed (.var n) Δ T) : ∃ i : ModuleContextIdx Δ T, i.toNat = n := by
  cases h with | var i => exact ⟨i, rfl⟩

theorem app_inv {Δ B m n} (h : Typed (.app m n) Δ B) :
    ∃ A, Typed m Δ (.arr A B) ∧ Typed n Δ A := by
  cases h with | app hm hn => exact ⟨_, hm, hn⟩

theorem fst_inv {Δ A m} (h : Typed (.fst m) Δ A) : ∃ B, Typed m Δ (.prod A B) := by
  cases h with | fst hm => exact ⟨_, hm⟩

theorem snd_inv {Δ B m} (h : Typed (.snd m) Δ B) : ∃ A, Typed m Δ (.prod A B) := by
  cases h with | snd hm => exact ⟨_, hm⟩

theorem abs_inv {Δ T m} (h : Typed (.abs m) Δ T) :
    ∃ A B, T = .arr A B ∧ Typed m (Δ.append A) B := by
  cases h with | abs hm => exact ⟨_, _, rfl, hm⟩

theorem pair_inv {Δ T m n} (h : Typed (.pair m n) Δ T) :
    ∃ A B, T = .prod A B ∧ Typed m Δ A ∧ Typed n Δ B := by
  cases h with | pair hm hn => exact ⟨_, _, rfl, hm, hn⟩

theorem unit_inv {Δ T} (h : Typed .unit Δ T) : T = .unit := by
  cases h with | unit => rfl

end ModuleExpression.Typed
/-! ## De Bruijn renaming and substitution on the untyped tree

The untyped analogues of `TM.ModuleExpression.rename`/`substitute`: since there are no type
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
    Untyped analogue of `TM.ModuleExpression.rename`. -/
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

`ReductionStep` mirrors the intrinsic one but on raw syntax; the payoff is `Typed.preservation`
— what intrinsic typing gave for free must now be proved.  All permanent. -/

/-- The untyped tuple of procedures corresponding to an instantiation (untyped analogue of
    `HoleSigs.Instantiation.toModuleTuple`). -/
def _root_.GaudisCrypt.HoleSigs.Instantiation.toModuleExpr :
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

namespace ModuleExpression.Typed

/-- A de Bruijn renaming `ρ` maps context `Δ` into `Γ` if every `Δ`-index has a `Γ`-index of
    the same type sitting at the renamed position. -/
def IsRenaming (Δ Γ : ModuleContext) (ρ : Nat → Nat) : Prop :=
  ∀ {M} (i : ModuleContextIdx Δ M), ∃ j : ModuleContextIdx Γ M, j.toNat = ρ i.toNat

omit [ProgramSpec] in
/-- Weakening: prepending a binder is the renaming `Nat.succ`. -/
theorem isRenaming_succ {Γ A} : IsRenaming Γ (Γ.append A) Nat.succ :=
  fun i => ⟨.succ i, rfl⟩

omit [ProgramSpec] in
/-- A context renaming lifts under one binder to `liftRen ρ`. -/
theorem IsRenaming.lift {Δ Γ A ρ} (h : IsRenaming Δ Γ ρ) :
    IsRenaming (Δ.append A) (Γ.append A) (ModuleExpression.liftRen ρ) := by
  intro M i
  cases i with
  | zero => exact ⟨.zero, rfl⟩
  | succ i' =>
      obtain ⟨j, hj⟩ := h i'
      exact ⟨.succ j, by simp [ModuleContextIdx.toNat, ModuleExpression.liftRen, hj]⟩

/-- Renaming preserves typing along a context renaming. -/
theorem rename {m Δ T} (h : Typed m Δ T) :
    ∀ {Γ : ModuleContext} {ρ : Nat → Nat}, IsRenaming Δ Γ ρ → Typed (m.rename ρ) Γ T := by
  induction h with
  | proc p => intro Γ ρ _; exact .proc p
  | procHoles ne p => intro Γ ρ _; exact .procHoles ne p
  | var i =>
      intro Γ ρ hρ
      obtain ⟨j, hj⟩ := hρ i
      change Typed (.var (ρ i.toNat)) Γ _
      rw [← hj]; exact .var j
  | app _ _ ihf iha => intro Γ ρ hρ; exact .app (ihf hρ) (iha hρ)
  | fst _ ihe => intro Γ ρ hρ; exact .fst (ihe hρ)
  | snd _ ihe => intro Γ ρ hρ; exact .snd (ihe hρ)
  | abs _ ihb => intro Γ ρ hρ; exact .abs (ihb hρ.lift)
  | pair _ _ iha ihb => intro Γ ρ hρ; exact .pair (iha hρ) (ihb hρ)
  | unit => intro Γ ρ _; exact .unit

/-- A substitution `σ` maps `Δ` into `Γ` if it sends every `Δ`-index to a `Γ`-typed term. -/
def IsSubst (Δ Γ : ModuleContext) (σ : Nat → ModuleExpression) : Prop :=
  ∀ {M} (i : ModuleContextIdx Δ M), Typed (σ i.toNat) Γ M

/-- A well-typed substitution lifts under one binder to `liftSubst σ`. -/
theorem IsSubst.lift {Δ Γ A σ} (h : IsSubst Δ Γ σ) :
    IsSubst (Δ.append A) (Γ.append A) (ModuleExpression.liftSubst σ) := by
  intro M i
  cases i with
  | zero => exact Typed.var (Δ := Γ.append A) (M := A) .zero
  | succ i' =>
      change Typed ((σ i'.toNat).rename Nat.succ) (Γ.append A) _
      exact (h i').rename isRenaming_succ

/-- Simultaneous substitution preserves typing along a well-typed substitution. -/
theorem substituteSimultaneously {m Δ T} (h : Typed m Δ T) :
    ∀ {Γ : ModuleContext} {σ : Nat → ModuleExpression},
      IsSubst Δ Γ σ → Typed (m.substituteSimultaneously σ) Γ T := by
  induction h with
  | proc p => intro Γ σ _; exact .proc p
  | procHoles ne p => intro Γ σ _; exact .procHoles ne p
  | var i => intro Γ σ hσ; exact hσ i
  | app _ _ ihf iha => intro Γ σ hσ; exact .app (ihf hσ) (iha hσ)
  | fst _ ihe => intro Γ σ hσ; exact .fst (ihe hσ)
  | snd _ ihe => intro Γ σ hσ; exact .snd (ihe hσ)
  | abs _ ihb => intro Γ σ hσ; exact .abs (ihb hσ.lift)
  | pair _ _ iha ihb => intro Γ σ hσ; exact .pair (iha hσ) (ihb hσ)
  | unit => intro Γ σ _; exact .unit

/-- Single-variable substitution preserves typing (the β-substitution lemma). -/
theorem substitute {Δ u t body arg}
    (hb : Typed body (Δ.append u) t) (ha : Typed arg Δ u) :
    Typed (body.substitute arg) Δ t := by
  unfold ModuleExpression.substitute
  refine hb.substituteSimultaneously ?_
  intro M i
  cases i with
  | zero => exact ha
  | succ i' => exact .var i'

/-- **Type preservation** (subject reduction): reduction preserves the typing judgment.  This is
    the extrinsic replacement for what the intrinsic `TM.ModuleExpression` guaranteed by
    construction. -/
theorem preservation {m m'} (hstep : m.ReductionStep m') :
    ∀ {Δ T}, Typed m Δ T → Typed m' Δ T := by
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

end ModuleExpression.Typed

/-- `T` is a *procedure-argument type*: a right-nested product of `proc` types (or `unit`).
    Untyped analogue of `TM.IsProcArgType`; lives on the shared `ModuleTypeRep`. -/
def IsProcArgType : ModuleTypeRep → Prop
  | .unit => True
  | .prod (.proc _) rest => IsProcArgType rest
  | _ => False

/-! ## Normal forms on the untyped tree

Untyped analogues of `IsProcHoles`/`IsProcTuple`/`Normal`/`Neutral`/`NormalClosed`.  Permanent;
mirror the intrinsic versions structurally. -/

namespace ModuleExpression

/-- `m` is a procedure-with-holes node. -/
def IsProcHoles : ModuleExpression → Prop
  | .procHoles _ _ => True
  | _              => False

/-- `m` is a right-nested tuple of hole-free procedures (`.unit`, or `.pair (.proc _) rest`
    with `IsProcTuple rest`) — the ground arguments a procedure-with-holes accepts. -/
def IsProcTuple : ModuleExpression → Prop
  | .unit               => True
  | .pair (.proc _) rest => IsProcTuple rest
  | _                   => False

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
  | appProcHoles {f arg} : IsProcHoles f → Normal arg → ¬ IsProcTuple arg → Neutral (.app f arg)
  | fst {e} : Neutral e → Neutral (.fst e)
  | snd {e} : Neutral e → Neutral (.snd e)

end

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


/-! #### Type erasure (untyped analogue)

On the untyped tree `erasedEqual` coincides with equality; the family is kept to mirror `TM`. -/

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

/-- Two erased-equal terms, one of which is normal (resp. neutral), are equal.  (In the untyped
    setting the intrinsic `HEq`/type-equality collapses to plain equality.) -/
theorem erasedEqual_normal_neutral_eq (m m' : ModuleExpression) (_h : erasedEqual m m') :
    (Normal m → m = m') ∧ (Neutral m → m = m') := sorry

theorem erasedEqual_normal_eq {n1 n2 : ModuleExpression} (hn1 : Normal n1)
    (h : erasedEqual n1 n2) : n1 = n2 := (erasedEqual_normal_neutral_eq n1 n2 h).1 hn1

theorem erasedEqual_neutral_eq {e1 e2 : ModuleExpression} (hne1 : Neutral e1)
    (h : erasedEqual e1 e2) : e1 = e2 := (erasedEqual_normal_neutral_eq e1 e2 h).2 hne1

theorem erasedEqual_eq n1 n2 : erasedEqual n1 n2 → n1 = n2 := sorry

/-! #### Embedding into `Metatheory.STLCext` (untyped port of `TM`'s SN machinery)

`TM` proves `reduce` terminating by embedding into simply-typed λ-calculus.  `UM`'s `reduce` is
choice-based and needs none of this, but the development is ported for parity.  Intrinsic type
indices become explicit `Typed` hypotheses (untyped λ-terms are not strongly normalising, so the
SN-flavoured facts genuinely require typing).  Proofs are `sorry` unless they translate directly.

Two `TM` items are deliberately *not* ported: the global `WellFoundedRelation ModuleExpression`
instance and the well-founded-recursion definition of `reduce` — on untyped terms the relation is
not well-founded (e.g. `Ω`), so porting them would be a `sorry` of a false statement.  `UM` uses
the `Terminating`/`Classical.choose` `reduce` instead. -/

private scoped instance instModuleExpressionSTLCspec : Metatheory.STLCext.STLCspec where
  baseTypes := ProcedureSignature
  baseTypeValue := fun sig => { s : ProcedureSignature // s = sig } × Procedure sig
  funcData := Σ holes : HoleSigs, Σ sig : ProcedureSignature, ProcedureWithHoles holes sig

/-- Erase a `ModuleTypeRep` to an STLC type (untyped port of `TM.ModuleTypeRep.toSTLC`; named
    without dot-notation to avoid `TM`'s private homonym on the shared `ModuleTypeRep`). -/
def tyToSTLC : ModuleTypeRep → Metatheory.STLCext.Ty
  | .prod A B => .prod (tyToSTLC A) (tyToSTLC B)
  | .arr A B => .arr (tyToSTLC A) (tyToSTLC B)
  | .proc sig => .base sig
  | .unit => .unit

private theorem toModuleTypeRepTuple_isArrowFree (holes : HoleSigs) :
    (tyToSTLC holes.toModuleTypeRepTuple).isArrowFree := by
  induction holes with
  | empty => simp [HoleSigs.toModuleTypeRepTuple, tyToSTLC, Metatheory.STLCext.Ty.isArrowFree]
  | append _ _ ih =>
      simp [HoleSigs.toModuleTypeRepTuple, tyToSTLC, Metatheory.STLCext.Ty.isArrowFree, ih]

open Metatheory.STLCext in
private def basicTermHoleLookup : (holes : HoleSigs) →
    BasicTerm (tyToSTLC holes.toModuleTypeRepTuple) → holes.Instantiation
  | .empty, _ => fun n => nomatch n
  | .append Γ _, .pair (.value v) rest => fun n =>
      match n with
      | .zero   => v.2
      | .succ m => basicTermHoleLookup Γ rest m

open Metatheory.STLCext in
private noncomputable def pwhToSTLC {holes sig}
    (proc : ProcedureWithHoles holes sig) : Term :=
    let inputType := tyToSTLC holes.toModuleTypeRepTuple
    let outputType := tyToSTLC (ModuleTypeRep.proc sig)
    let inputArrowFree : inputType.isArrowFree := toModuleTypeRepTuple_isArrowFree holes
    let outputArrowFree : outputType.isArrowFree := by
      simp [outputType, tyToSTLC, Metatheory.STLCext.Ty.isArrowFree]
    let substitution : BasicTerm inputType → BasicTerm outputType :=
      fun basicTerm => .value (⟨sig, rfl⟩, proc.instantiate (basicTermHoleLookup holes basicTerm))
    .func (t := inputType) (u := outputType)
      (ht := inputArrowFree) (hu := outputArrowFree) ⟨holes, sig, proc⟩ substitution

/-- Erase an untyped module expression to an STLC term (untyped port of
    `TM.ModuleExpression.toSTLC`; variables map directly since they are already `Nat`). -/
noncomputable def toSTLC : ModuleExpression → Metatheory.STLCext.Term
  | .unit => .unit
  | .proc (sig := sig) p => .value (⟨sig, rfl⟩, p)
  | .procHoles _ p => pwhToSTLC p
  | .var n => .var n
  | .app M N => .app (toSTLC M) (toSTLC N)
  | .fst M => .fst (toSTLC M)
  | .snd M => .snd (toSTLC M)
  | .abs M => .lam (toSTLC M)
  | .pair M N => .pair (toSTLC M) (toSTLC N)

private def ctxToSTLC : ModuleContext → Metatheory.STLCext.Context
  | .empty => []
  | .append Γ T => tyToSTLC T :: ctxToSTLC Γ

private theorem toSTLC_rename_shift (d : Nat) (m : ModuleExpression) :
    ∀ (c : Nat) (ρ : Nat → Nat)
      (_ : ∀ r, r < c → ρ r = r) (_ : ∀ r, r ≥ c → ρ r = r + d),
      toSTLC (m.rename ρ) = Metatheory.STLCext.Term.shift d c (toSTLC m) := sorry

private theorem toSTLC_substAll_level (N_stlc : Metatheory.STLCext.Term) (m : ModuleExpression) :
    ∀ (k : Nat) (σ : Nat → ModuleExpression)
      (_ : ∀ r, toSTLC (σ r) = Metatheory.STLCext.Term.subst k
              (Metatheory.STLCext.Term.shift k 0 N_stlc) (Metatheory.STLCext.Term.var r)),
      toSTLC (m.substituteSimultaneously σ) = Metatheory.STLCext.Term.subst k
        (Metatheory.STLCext.Term.shift k 0 N_stlc) (toSTLC m) := sorry

private theorem toSTLC_subst (body arg : ModuleExpression) :
    toSTLC (body.substitute arg) =
    Metatheory.STLCext.Term.subst0 (toSTLC arg) (toSTLC body) := sorry

private def isBasicType_toModuleTuple {holes : HoleSigs} (inst : holes.Instantiation) :
    Metatheory.STLCext.Term.isBasicType (tyToSTLC holes.toModuleTypeRepTuple)
        (toSTLC (HoleSigs.Instantiation.toModuleExpr inst)) := sorry

private def basicTermHoleLookup_toModuleTuple {holes : HoleSigs} (inst : holes.Instantiation)
    {sig : ProcedureSignature} (n : HoleIndex holes sig) :
    basicTermHoleLookup holes
      (Metatheory.STLCext.Term.toBasicTerm _ _ (isBasicType_toModuleTuple inst)) n = inst n := sorry

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
    = proc.instantiate args := sorry

private theorem toModuleTuple_of_basicType {holes : HoleSigs} (arg : ModuleExpression)
    (h : Metatheory.STLCext.Term.isBasicType (tyToSTLC holes.toModuleTypeRepTuple) (toSTLC arg)) :
    HoleSigs.Instantiation.toModuleExpr
      (basicTermHoleLookup holes (Metatheory.STLCext.Term.toBasicTerm _ _ h)) = arg := sorry

private theorem reductionStep_stlc_compat (m m' : ModuleExpression) (h : m.ReductionStep m') :
    Metatheory.STLCext.Step (toSTLC m) (toSTLC m') := sorry

private theorem toSTLC_hasType {m : ModuleExpression} {Δ T} (h : m.Typed Δ T) :
    Metatheory.STLCext.HasType (ctxToSTLC Δ) (toSTLC m) (tyToSTLC T) := sorry

private theorem reductionStep_stlc_complete (m : ModuleExpression) (M' : Metatheory.STLCext.Term)
    (h : Metatheory.STLCext.Step (toSTLC m) M') :
    ∃ m', m.ReductionStep m' ∧ toSTLC m' = M' := sorry

private theorem multiStepReduction_to_stlc_star {m m' : ModuleExpression}
    (h : m.MultiStepReduction m') :
    Rewriting.Star Metatheory.STLCext.Step (toSTLC m) (toSTLC m') := sorry

private theorem toSTLC_Normal_iff {m : ModuleExpression} :
    Normal m ↔ Rewriting.IsNormalForm Metatheory.STLCext.Step (toSTLC m) := sorry

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

private theorem toSTLC_injective (m m' : ModuleExpression) :
    toSTLC m = toSTLC m' → erasedEqual m m' := sorry

private theorem toSTLC_injective_normal {n1 n2 : ModuleExpression} (hn1 : Normal n1)
    (h : toSTLC n1 = toSTLC n2) : n1 = n2 :=
  erasedEqual_normal_eq hn1 (toSTLC_injective n1 n2 h)

/-- Accessibility of the (reverse) reduction relation for a well-typed term — the strong
    normalisation fact, obtained via the STLC embedding.  Requires typing (untyped terms are not
    SN).  Untyped port of `TM.reduce_acc`. -/
private theorem reduce_acc {Δ T} (m : ModuleExpression) (hty : m.Typed Δ T) :
    Acc (fun p q : ModuleExpression =>
      Metatheory.STLCext.Step (toSTLC q) (toSTLC p)) m := sorry

/-! ### Shape predicates for call-by-value reduction (untyped analogues) -/

/-- `m` is a lambda-abstraction. -/
def IsAbs : ModuleExpression → Prop
  | .abs _ => True
  | _      => False

instance : (m : ModuleExpression) → Decidable (IsAbs m)
  | .abs _ => isTrue trivial
  | .proc _ | .procHoles _ _ | .var _ | .app _ _ | .fst _ | .snd _ | .pair _ _ | .unit =>
      isFalse (by simp [IsAbs])

/-- The body of an abstraction. -/
def IsAbs.body {m : ModuleExpression} (h : IsAbs m) : ModuleExpression := by
  cases m with
  | abs body => exact body
  | _ => simp [IsAbs] at h

/-- `m` is a pair. -/
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

instance : (m : ModuleExpression) → Decidable (ModuleExpression.IsProcHoles m)
  | .procHoles _ _ => isTrue trivial
  | .proc _ | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .unit =>
      isFalse (by simp [ModuleExpression.IsProcHoles])

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

theorem NormalClosed.normal {m : ModuleExpression} (h : m.NormalClosed) : m.Normal := by
  induction h with
  | proc => exact .proc
  | procHoles => exact .procHoles
  | abs hb => exact .abs hb
  | pair _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit

/-- Typing is preserved along multi-step reduction. -/
theorem Typed.preservation_multi {m m' : ModuleExpression} {Δ T} (hm : m.Typed Δ T)
    (h : m.MultiStepReduction m') : m'.Typed Δ T := by
  induction h with
  | refl => exact hm
  | tail _ hstep ih => exact ModuleExpression.Typed.preservation hstep ih

/-- `m` terminates: it multi-step reduces to some normal form. -/
def Terminating (m : ModuleExpression) : Prop :=
  ∃ n : ModuleExpression, n.Normal ∧ m.MultiStepReduction n

def reduce_all (m : ModuleExpression) : Set ModuleExpression :=
  { n | n.Normal ∧ m.MultiStepReduction n }

theorem reduce_all_subsingleton {m : ModuleExpression} :
    Set.Subsingleton (reduce_all m) := sorry

open Classical in
/-- β-normal form: a chosen normal form reachable from `m` when it terminates, else `unit`. -/
noncomputable def reduce (m : ModuleExpression) : ModuleExpression :=
  if h : Terminating m then h.choose else .unit

@[simp] theorem reduce_of_normal {m : ModuleExpression} (h : m.Normal) : reduce m = m := sorry

@[simp] theorem reduce_of_normalClosed {m : ModuleExpression} (h : m.NormalClosed) :
    reduce m = m := reduce_of_normal h.normal

/-- The reduct of a well-typed term is normal. -/
theorem reduce_normal_of_typed {m Δ T} (h : m.Typed Δ T) : (reduce m).Normal := sorry

theorem multiStepReduction_reduce {m : ModuleExpression} : m.MultiStepReduction (reduce m) := sorry

/-- Reduction preserves typing. -/
theorem reduce_typed {m Δ T} (h : m.Typed Δ T) : (reduce m).Typed Δ T :=
  h.preservation_multi multiStepReduction_reduce

/-- The reduct of a well-typed closed term is closed-normal. -/
theorem reduce_normalClosed {m T} (h : m.Typed .empty T) : (reduce m).NormalClosed := sorry

theorem reduce_idempotent (m : ModuleExpression) : reduce (reduce m) = reduce m := sorry

@[simp] theorem reduce_proc {sig} (p : Procedure sig) : reduce (.proc p) = .proc p :=
  reduce_of_normal .proc

theorem confluence {m m1 m2 : ModuleExpression}
    (_ : m.MultiStepReduction m1) (_ : m.MultiStepReduction m2) : reduce m1 = reduce m2 := sorry

@[simp] theorem reduce_pair (m1 m2 : ModuleExpression) :
    reduce (.pair m1 m2) = .pair (reduce m1) (reduce m2) := sorry

theorem reduce_beta (body arg : ModuleExpression) :
    reduce (.app (.abs body) arg) = reduce (body.substitute arg) := sorry

/-! ### Further untyped ports from the intrinsic `TM` development

Shape decomposition, decidability of `Normal`/`Neutral`, closed-term progress, multi-step
congruences, the call-by-value step, type erasure, and the remaining `reduce` specification
lemmas.  Statements that relied on the intrinsic type index now carry an explicit `Typed`
hypothesis.  Proofs are `sorry` unless they translate directly. -/

/-- A `procHoles` node decomposed into its holes/signature/procedure (untyped analogue of
    `TM.IsProcHoles.destruct`; no type-index equation is produced). -/
def IsProcHoles.destruct {m : ModuleExpression} (h : m.IsProcHoles) :
    Σ holes : HoleSigs, Σ sig : ProcedureSignature,
      holes.NonEmpty ×' ProcedureWithHoles holes sig := by
  cases m with
  | procHoles ne p => exact ⟨_, _, ne, p⟩
  | _ => simp [IsProcHoles] at h

/-- The domain of a (well-typed) procedure-with-holes is a procedure-argument type. -/
theorem IsProcHoles.isProcArgType {m : ModuleExpression} {Δ A B}
    (_hty : m.Typed Δ (.arr A B)) (_h : m.IsProcHoles) : IsProcArgType A := sorry

/-- Joint decidability of `Normal`/`Neutral`, sharing one structural recursion (untyped port of
    `TM.decidableNormalNeutral`). -/
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
            if hph : IsProcHoles f then
              match instDecidableIsProcTuple arg with
              | .isFalse hpt => exact .isTrue (.appProcHoles hph na hpt)
              | .isTrue hpt =>
                  exact .isFalse fun h => by
                    cases h with
                    | app nf' _ => exact nf nf'
                    | appProcHoles _ _ hpt' => exact hpt' hpt
            else
              exact .isFalse fun h => by
                cases h with
                | app nf' _ => exact nf nf'
                | appProcHoles hph' _ _ => exact hph hph'
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

/-- Progress for the closed fragment (untyped analogue of `TM.closed_progress`); typing pins the
    empty context. -/
private theorem closed_progress {m : ModuleExpression} {T} (_h : m.Typed .empty T) :
    (¬ Neutral m) ∧ (IsProcArgType T → Normal m → IsProcTuple m) := sorry

/-- A well-typed closed term is never neutral. -/
theorem empty_context_not_neutral {m : ModuleExpression} {T} (h : m.Typed .empty T) :
    ¬ Neutral m := (closed_progress h).1

/-- A normal well-typed closed term is closed-normal. -/
theorem Normal.normalClosed {m : ModuleExpression} {T} (_hty : m.Typed .empty T)
    (_h : Normal m) : NormalClosed m := sorry

/-- `app` is a congruence for multi-step reduction. -/
theorem multiStepReduction_app {m1 m1' m2 m2' : ModuleExpression}
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
theorem multiStepReduction_fst {e e' : ModuleExpression} (h : e.MultiStepReduction e') :
    (ModuleExpression.fst e).MultiStepReduction (ModuleExpression.fst e') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (.fst hbc)

/-- `pair` is a congruence for multi-step reduction. -/
theorem multiStepReduction_pair {a a' b b' : ModuleExpression}
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

/-- `toModuleExpr inst` is always a proc-tuple (untyped analogue of
    `TM.toModuleTuple_isProcTuple`). -/
theorem toModuleExpr_isProcTuple {holes : HoleSigs} (inst : holes.Instantiation) :
    (HoleSigs.Instantiation.toModuleExpr inst).IsProcTuple := by
  induction holes with
  | empty => simp [HoleSigs.Instantiation.toModuleExpr, IsProcTuple]
  | append holeTail sig ih =>
      simp only [HoleSigs.Instantiation.toModuleExpr]
      exact ih (fun idx => inst (.succ idx))

/-- Extract an instantiation from a (well-typed) proc-tuple expression for a hole signature
    (untyped analogue of `TM.procTupleLookup`; the shape match is guaranteed by typing). -/
noncomputable def procTupleLookup {Δ : ModuleContext} (holes : HoleSigs) (m : ModuleExpression)
    (_hty : m.Typed Δ holes.toModuleTypeRepTuple) (_h : m.IsProcTuple) : holes.Instantiation :=
  sorry

/-- Round-trip: recovering an instantiation from a proc-tuple and converting back is the identity
    (untyped analogue of `TM.procTupleLookup_toModuleTuple`). -/
theorem procTupleLookup_toModuleTuple {Δ : ModuleContext} (holes : HoleSigs)
    (m : ModuleExpression) (hty : m.Typed Δ holes.toModuleTypeRepTuple) (h : m.IsProcTuple) :
    HoleSigs.Instantiation.toModuleExpr (procTupleLookup holes m hty h) = m := sorry

/-- One call-by-value reduction step of a non-normal term (untyped analogue of
    `TM.cbvReductionStep`).  Unlike `TM`, `UM`'s `reduce` does not use this, so it is left as a
    stub. -/
noncomputable def cbvReductionStep (m : ModuleExpression) (_nn : ¬ Normal m) :
    ModuleExpression := sorry

/-- The call-by-value step is a reduction step. -/
theorem cbvReductionStep_is_reductionStep (m : ModuleExpression) (nn : ¬ Normal m) :
    m.ReductionStep (cbvReductionStep m nn) := sorry

/-! #### Remaining `reduce` specification lemmas -/

@[simp] theorem reduce_fst_pair (m1 m2 : ModuleExpression) :
    reduce (.fst (.pair m1 m2)) = reduce m1 := sorry

@[simp] theorem reduce_fst (m m' : ModuleExpression) :
    reduce (.fst (.pair m m')) = reduce m := sorry

@[simp] theorem reduce_snd (m m' : ModuleExpression) :
    reduce (.snd (.pair m m')) = reduce m' := sorry

theorem reduce_app (m m' : ModuleExpression) :
    reduce (.app m m') = reduce (.app (reduce m) (reduce m')) := sorry

theorem reduce_fst_cong (m m' : ModuleExpression) :
    reduce m = reduce m' → reduce (.fst m) = reduce (.fst m') := sorry

/-- A well-typed closed normal term of product type is a pair (untyped analogue of
    `TM.pair_type_is_pair`). -/
theorem pair_type_is_pair {m : ModuleExpression} {t1 t2}
    (_hty : m.Typed .empty (.prod t1 t2)) (_h : NormalClosed m) :
    ∃ m1 m2, m = .pair m1 m2 := sorry

/-- The reduct is always normal (holds unconditionally for the choice-based `reduce`: on a
    non-terminating term it is `.unit`).  Untyped counterpart of `TM.reduce_normal`. -/
theorem reduce_normal (m : ModuleExpression) : Normal (reduce m) := by
  unfold reduce
  split
  · rename_i h; exact h.choose_spec.1
  · exact Normal.unit

end ModuleExpression

/- # Modules (untyped-based) -/
/- # Modules -/

structure Module (T : ModuleTypeRep) where
  expression : ModuleExpression
  typed : expression.Typed .empty T
  normal : expression.NormalClosed

/-- Build a `Module` from a well-typed closed expression by normalising it. -/
noncomputable def ModuleExpression.toModule {T : ModuleTypeRep}
    (m : ModuleExpression) (h : m.Typed .empty T) : Module T :=
  ⟨m.reduce, m.reduce_typed h, m.reduce_normalClosed h⟩

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
theorem Module.toModule_expression {T} (m : ModuleExpression) (h : m.Typed .empty T) :
    (m.toModule h).expression = m.reduce := rfl

@[simp]
theorem Module.reduce_expression {T} (m : Module T) : m.expression.reduce = m.expression :=
  ModuleExpression.reduce_of_normalClosed m.normal

@[simp]
theorem Module.fst_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).fst' = m1 := by
  sorry

@[simp]
theorem Module.snd_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).snd' = m2 := by
  sorry


theorem Module.pair_fst_snd' : (Module.fst' m).pair' (Module.snd' m) = m := by
  sorry


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

end GaudisCrypt.UM
