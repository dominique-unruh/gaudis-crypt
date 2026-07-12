import GaudisCrypt.Examples.Pedersen.Commitment
import GaudisCrypt.WeakestPreconditions

/-!
# The Pedersen commitment scheme

A transliteration of EasyCrypt's `examples/Pedersen.ec`:

* EC's `clone DLog` (cyclic group `group` with generator `g`, prime exponent field `exp`)
  becomes the class `PedersenGroup` — for now only the *operations* the programs mention;
  the algebraic laws will be added as hypotheses when the proofs need them.
* EC's `PedersenTypes` + the `Commitment` clone become the `CommitmentTypes` instance
  (value/commitment = group, message/openingkey = exponent).
* `module Pedersen : CommitmentScheme` becomes a `CommitmentScheme` module built from the
  three closed procedures.
* Correctness is stated as EC states it (`hoare[Correctness(Pedersen).main : true ==> res]`):
  the output distribution puts no mass on `res = false`.  No proof yet.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt
open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Syntax

-- the scheme is deliberately named like the enclosing example namespace (EC: `module Pedersen`)
set_option linter.dupNamespace false

/-! ## The group setup (EC's `DLog` clone) -/

/-- A cyclic group `G` with generator `g` and exponent type `F` (EC's `group`/`exp`).
    Only the operations for now: multiplication, exponentiation, and what programs need of
    the types (defaults, decidable equality, uniform sampling on `F`). -/
class PedersenGroup where
  G : Type
  F : Type
  g : G
  gmul : G → G → G
  gpow : G → F → G
  g_inhabited : Inhabited G
  g_deceq : DecidableEq G
  f_inhabited : Inhabited F
  f_deceq : DecidableEq F
  f_fintype : Fintype F

namespace PedersenGroup
variable [PedersenGroup]
instance : Inhabited G := g_inhabited
instance : DecidableEq G := g_deceq
instance : Inhabited F := f_inhabited
instance : DecidableEq F := f_deceq
instance : Fintype F := f_fintype
instance : Mul G := ⟨gmul⟩
instance : Pow G F := ⟨gpow⟩
end PedersenGroup

open PedersenGroup (G F g)

/-- EC's `PedersenTypes` + `clone Commitment with …`: value/commitment are group elements,
    message/openingkey are exponents. -/
instance pedersenTypes [PedersenGroup] : CommitmentTypes where
  Value := G
  Message := F
  Commitment := G
  OpeningKey := F
  value_inhabited := inferInstance
  message_inhabited := inferInstance
  commitment_inhabited := inferInstance
  openingKey_inhabited := inferInstance
  message_deceq := inferInstance

variable [ProgramSpec] [PedersenGroup]

/-! ## The scheme

```
module Pedersen : CommitmentScheme = {
  proc gen() : value                = { x <$ dt; h <- g ^ x; return h; }
  proc commit(h, m)                 = { d <$ dt; c <- (g ^ d) * (h ^ m); return (c, d); }
  proc verify(h, m, c, d)           = { c' <- (g ^ d) * (h ^ m); return (c = c'); }
}.
``` -/

/-- Sample a secret exponent, publish `h = g ^ x`. -/
noncomputable def Pedersen.gen := proc () : G {
  var x : F;
  var h : G;
  x <$ SubProbability.uniform;
  h <- g ^ $x;
  return $h
}

/-- Commit to `m` under `h`: sample the opening key `d`, output `g ^ d * h ^ m`. -/
noncomputable def Pedersen.commit := proc (h : G, m : F) : (G × F) {
  var c : G;
  var d : F;
  d <$ SubProbability.uniform;
  c <- g ^ $d * $h ^ $m;
  return ($c, $d)
}

/-- Recompute the commitment and compare. -/
noncomputable def Pedersen.verify := proc (h : G, m : F, c : G, d : F) : Bool {
  var c' : G;
  c' <- g ^ $d * $h ^ $m;
  return $c == $c'
}

/-- EC's `module Pedersen : CommitmentScheme`. -/
noncomputable def Pedersen : CommitmentScheme :=
  CommitmentScheme.mk
    { gen := (ModuleExpression.proc Pedersen.gen).toModule
      commit := (ModuleExpression.proc Pedersen.commit).toModule
      verify := (ModuleExpression.proc Pedersen.verify).toModule }

/-! ## Correctness (statement only)

To *run* an applied functor module we extract its procedure: a normal closed module
expression of procedure type is a `.proc` node.  (`proc_type_is_proc`/`Module.procedure`
are generic module-calculus material — candidates for `Language/Modules.lean`.) -/

omit [PedersenGroup] in
theorem proc_type_is_proc {sig : ProcedureSignature}
    {m : ModuleExpression .empty (.proc sig)} (h : NormalClosed m) :
    ∃ p : Procedure sig, m = .proc p := by
  cases h with
  | const => exact ⟨_, rfl⟩

/-- The procedure of a proc-typed module.  (`Classical.choose` only escapes the
    Prop-to-data restriction; the witness is unique — see `Module.procedure_spec` and
    `Module.procedure_proc`.) -/
noncomputable def _root_.GaudisCrypt.Language.Modules.Module.procedure
    {sig : ProcedureSignature} (m : Module (.proc sig)) : Procedure sig :=
  (proc_type_is_proc m.normal).choose

omit [PedersenGroup] in
/-- `Module.procedure` is characterized by its defining equation (the witness of
    `proc_type_is_proc` is unique by constructor injectivity). -/
theorem _root_.GaudisCrypt.Language.Modules.Module.procedure_spec
    {sig : ProcedureSignature} (m : Module (.proc sig)) :
    m.expression = .proc m.procedure :=
  (proc_type_is_proc m.normal).choose_spec

omit [PedersenGroup] in
/-- Round-trip: wrapping a procedure as a module and extracting recovers it. -/
@[simp] theorem _root_.GaudisCrypt.Language.Modules.Module.procedure_proc
    {sig : ProcedureSignature} (p : Procedure sig) :
    ((ModuleExpression.proc p).toModule).procedure = p := by
  have h1 : ((ModuleExpression.proc p).toModule).expression = .proc p :=
    Module.reduce_expression ⟨.proc p, .const⟩
  have h2 := Module.procedure_spec ((ModuleExpression.proc p).toModule)
  rw [h1] at h2
  injection h2 with hΔ hsig h
  exact h.symm

/-! ## The computation bridge

`Correctness Pedersen` β/δ-normalizes to `Correctness.main` with Pedersen's procedures in the
holes.  (`reduce_of_normal`/`reduce_proc` are generic — Modules.lean candidates.) -/

omit [PedersenGroup] in
theorem reduce_of_normal {Γ : ModuleContext} {t : ModuleTypeRep} {m : ModuleExpression Γ t}
    (h : Normal m) : reduce m = m := by
  unfold reduce
  rw [dif_pos h]

omit [PedersenGroup] in
@[simp] theorem reduce_proc {Γ : ModuleContext} {sig : ProcedureSignature} (p : Procedure sig) :
    reduce (ModuleExpression.proc p : ModuleExpression Γ _) = .proc p :=
  reduce_of_normal .const

/-- The instantiation of `Correctness.main`'s holes by Pedersen's procedures.
    (`HoleIndex` counts from the *last-declared* hole: `.zero` is `verify`.) -/
noncomputable def pedersenInst :
    (((HoleSigs.empty.append (procsig () -> G)).append
        (procsig (G, F) -> (G × F))).append
      (procsig (G, F, G, F) -> Bool)).Instantiation
  | _, .zero => Pedersen.verify
  | _, .succ .zero => Pedersen.commit
  | _, .succ (.succ .zero) => Pedersen.gen

@[simp] theorem pedersenInst_zero : pedersenInst HoleIndex.zero = Pedersen.verify := rfl
@[simp] theorem pedersenInst_one :
    pedersenInst (HoleIndex.succ HoleIndex.zero) = Pedersen.commit := rfl
@[simp] theorem pedersenInst_two :
    pedersenInst (HoleIndex.succ (HoleIndex.succ HoleIndex.zero)) = Pedersen.gen := rfl

/-- **The bridge**: the procedure of the applied functor module is the instantiated body. -/
theorem Correctness_Pedersen_procedure :
    (Correctness Pedersen).procedure = Correctness.main.instantiate pedersenInst := by
  have hexp : (Correctness Pedersen).expression
      = .proc (Correctness.main.instantiate pedersenInst) := by
    change (ModuleExpression.toModule
        (.app Correctness.expression Pedersen.expression)).expression = _
    rw [Module.toModule_expression]
    -- Pedersen's expression is the ground pair of its three procedures
    have hP : Pedersen.expression
        = .pair (.proc Pedersen.gen)
            (.pair (.proc Pedersen.commit) (.proc Pedersen.verify)) := by
      simp [Pedersen, CommitmentScheme.mk, Module.pair, reduce_pair]
    -- Correctness's expression is literally its λ-term (the body is normal)
    have hC : Correctness.expression
        = .abs (.app (.procHoles (by trivial) Correctness.main)
            (.pair (.snd (.snd (.var .zero)))
              (.pair (.fst (.snd (.var .zero)))
                (.pair (.fst (.var .zero)) .unit)))) := by
      refine reduce_of_normal (.abs (.neutral (.appProcHoles trivial ?_ ?_)))
      · exact .pair (.neutral (.snd (.snd .var)))
          (.pair (.neutral (.fst (.snd .var)))
            (.pair (.neutral (.fst .var)) .unit))
      · simp [IsProcTuple]
    rw [hC, hP, reduce_beta]
    -- the substitution computes by whnf; one explicit reduction chain into `confluence`
    refine Eq.trans (confluence (Rewriting.Star.refl _) ?_) (reduce_proc _)
    refine Rewriting.Star.head (.appR (.pairL (.snd .sndPair))) ?_
    refine Rewriting.Star.head (.appR (.pairL .sndPair)) ?_
    refine Rewriting.Star.head (.appR (.pairR (.pairL (.fst .sndPair)))) ?_
    refine Rewriting.Star.head (.appR (.pairR (.pairL .fstPair))) ?_
    refine Rewriting.Star.head (.appR (.pairR (.pairR (.pairL .fstPair)))) ?_
    exact Rewriting.Star.head (.delta pedersenInst) (Rewriting.Star.refl _)
  have h2 := Module.procedure_spec (Correctness Pedersen)
  rw [hexp] at h2
  injection h2 with hΔ hsig h
  exact h.symm

/-! ### Per-procedure wp lemmas (EC's `inline`+`auto` steps, done once per procedure) -/


/-- The wp of each Pedersen procedure, stated at the `CommitmentTypes`-spelled signature the
    instantiated game carries (definitionally `G`/`F`; the spelling makes the simp keys match). -/
theorem wp_gen (f : ProgramDenotation.Post State CommitmentTypes.Value) :
    (procedureDenotation (sig := procsig () -> CommitmentTypes.Value) Pedersen.gen ()).wp f
      = fun st => ∑ x : F, f (g ^ x, st) / Fintype.card F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.gen, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g, wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, LocalVariableState.varsL]

theorem wp_commit (args : G × F)
    (f : ProgramDenotation.Post State
      (CommitmentTypes.Commitment × CommitmentTypes.OpeningKey)) :
    (procedureDenotation
        (sig := procsig (CommitmentTypes.Value, CommitmentTypes.Message) ->
          (CommitmentTypes.Commitment × CommitmentTypes.OpeningKey)) Pedersen.commit args).wp f
      = fun st => ∑ x : F, f ((g ^ x * args.1 ^ args.2, x), st) / Fintype.card F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.commit, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g, wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL,
    LocalVariableState.paramsL, LocalVariableState.varsL]
  rfl

theorem wp_verify (args : G × F × G × F) (f : ProgramDenotation.Post State Bool) :
    (procedureDenotation
        (sig := procsig (CommitmentTypes.Value, CommitmentTypes.Message,
          CommitmentTypes.Commitment, CommitmentTypes.OpeningKey) -> Bool)
        Pedersen.verify args).wp f
      = fun st => f (args.2.2.1 == g ^ args.2.2.2 * args.1 ^ args.2.1, st) := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.verify, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g, wp_set_g,
    wp_lift, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL,
    LocalVariableState.paramsL, LocalVariableState.varsL]

set_option linter.flexible false in
/-- **Correctness of Pedersen** — EC's
    `hoare[Correctness(Pedersen).main : true ==> res]`: from any initial state, the
    correctness game never returns `false`. -/
theorem pedersen_correctness (m : F) (σ : State) :
    (procedureDenotation (Correctness Pedersen).procedure m σ).ofEvent
      {r : Bool × State | r.1 = false} = 0 := by
  rw [Correctness_Pedersen_procedure]
  -- reduce `ofEvent` to a `wp` with the indicator postcondition
  suffices h : (procedureDenotation (Correctness.main.instantiate pedersenInst) m).wp
      (({r : Bool × State | r.1 = false}).indicator fun _ => 1) σ = 0 by
    have hi := expectation_indicator
      (procedureDenotation (Correctness.main.instantiate pedersenInst) m σ)
      {r : Bool × State | r.1 = false} 1
    rw [one_mul] at hi
    have h' : (↑((procedureDenotation (Correctness.main.instantiate pedersenInst) m σ).ofEvent
        {r : Bool × State | r.1 = false}) : ENNReal) = 0 := by
      rw [← hi]; exact h
    exact_mod_cast h'
  -- unfold the game and push `wp` through
  rw [procedureDenotation_eq_procWrap_gen, wp_procWrap]
  simp [Correctness.main, StmtWithHoles.instantiate, programDenotation, StmtWithHoles.call,
    wp_bind, wp_get_g, wp_set_g, wp_zoom,
    ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, ProcedureState.globalL,
    LocalVariableState.paramsL, LocalVariableState.varsL,
    Set.indicator, Set.mem_setOf_eq]
  -- descend through the two samplings with `rw` (full-defeq unification), summand by summand
  rw [wp_gen]
  refine Finset.sum_eq_zero fun x _ => ?_
  refine ENNReal.div_eq_zero_iff.mpr (Or.inl ?_)
  rw [wp_commit]
  refine Finset.sum_eq_zero fun d _ => ?_
  refine ENNReal.div_eq_zero_iff.mpr (Or.inl ?_)
  rw [wp_verify]
  simp

end GaudisCrypt.Examples.Pedersen
