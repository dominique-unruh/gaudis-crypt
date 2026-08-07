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
* `module Pedersen : CommitmentScheme` becomes a `module Pedersen : CommitmentScheme { … }`
  declaration — EC's own syntax, near enough, now that the `module` command exists.
* Correctness is stated as EC states it (`hoare[Correctness(Pedersen).main : true ==> res]`):
  the output distribution puts no mass on `res = false`.  No proof yet.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt
open GaudisCrypt

-- the scheme is deliberately named like the enclosing example namespace (EC: `module Pedersen`)
set_option linter.dupNamespace false

/-! ## The group setup (EC's `DLog` clone) -/

/-- A cyclic group `G` with generator `g` and exponent type `F` (EC's `group`/`exp`).
    Only the operations for now: multiplication, exponentiation, and what programs genuinely need
    of the types — a default element (`Inhabited`, so local variables can be declared) and
    `Fintype F` (real content: `SubProbability.uniform` samples it, and the wp lemmas sum over it).

    Decidable equality is *not* a field.  `verify` does compare (`$c == $c'`), and `==` is `BEq`
    derived from `DecidableEq` — but these programs are never executed: every `proc` is
    `noncomputable` and the semantics is a measure, so the comparison only ever has to *denote* a
    `Bool`, not compute one.  `Classical.decEq` supplies that for free, which is why the instances
    below are classical and the class is two fields shorter.  Nothing in the proofs cares: they
    reason about `=`, and `beq_self_eq_true` and friends hold for any `DecidableEq` witness. -/
class PedersenGroup where
  G : Type
  F : Type
  g : G
  gmul : G → G → G
  gpow : G → F → G
  g_inhabited : Inhabited G
  f_inhabited : Inhabited F
  f_fintype : Fintype F

namespace PedersenGroup
variable [PedersenGroup]
instance : Inhabited G := g_inhabited
noncomputable instance : DecidableEq G := Classical.decEq G
instance : Inhabited F := f_inhabited
noncomputable instance : DecidableEq F := Classical.decEq F
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

variable [ProgramSpec] [PedersenGroup]

/-! ## The scheme

EC's
```
module Pedersen : CommitmentScheme = {
  proc gen() : value                = { x <$ dt; h <- g ^ x; return h; }
  proc commit(h, m)                 = { d <$ dt; c <- (g ^ d) * (h ^ m); return (c, d); }
  proc verify(h, m, c, d)           = { c' <- (g ^ d) * (h ^ m); return (c = c'); }
}.
```
transcribes directly with the `module` command.  It declares, per procedure `f`, both the body
`Pedersen.f.procedure` and the module `Pedersen.f : Module.Proc …`, and assembles them into
`Pedersen : CommitmentScheme` with `CommitmentScheme.mk` (the field names match the moduletype's,
so the record constructor is used rather than a nest of `Module.pair`s).  `Pedersen` has no
module parameters, so it *is* the scheme — there is nothing to apply it to, and hence no
`Pedersen.apply_simp`. -/

module Pedersen : CommitmentScheme {
  /- Sample a secret exponent, publish `h = g ^ x`. -/
  proc gen() : G {
    var x : F;
    var h : G;
    x <$ SubProbability.uniform;
    h <- g ^ $x;
    return $h
  };
  /- Commit to `m` under `h`: sample the opening key `d`, output `g ^ d * h ^ m`. -/
  proc commit(h : G, m : F) : (G × F) {
    var c : G;
    var d : F;
    d <$ SubProbability.uniform;
    c <- g ^ $d * $h ^ $m;
    return ($c, $d)
  };
  /- Recompute the commitment and compare. -/
  proc verify(h : G, m : F, c : G, d : F) : Bool {
    var c' : G;
    c' <- g ^ $d * $h ^ $m;
    return $c == $c'
  };
}

/-! ## Correctness (statement only)

To *run* an applied functor module we extract its procedure: a normal closed module
expression of procedure type is a `.proc` node (`proc_type_is_proc` / `Module.procedure`,
now in `Language/Modules.lean`). -/

/-! ## The computation bridge

`Correctness Pedersen` β/δ-normalizes to `Correctness.main` with Pedersen's procedures in the
holes.  (`reduce_of_normal`/`reduce_proc` are generic — Modules.lean candidates.) -/

omit [PedersenGroup] in
theorem reduce_of_normal {m : ModuleExpression} (h : m.Normal) : m.reduce = m :=
  ModuleExpression.reduce_of_normal h

omit [PedersenGroup] in
@[simp] theorem reduce_proc {sig : ProcedureSignature} (p : Procedure sig) :
    (ModuleExpression.proc p).reduce = .proc p :=
  ModuleExpression.reduce_proc p

/-- The instantiation of `Correctness.main`'s holes by Pedersen's procedures.
    (`HoleIndex` counts from the *last-declared* hole: `.zero` is `verify`.) -/
noncomputable def pedersenInst :
    (((HoleSigs.empty.append (procsig () -> G)).append
        (procsig (G, F) -> (G × F))).append
      (procsig (G, F, G, F) -> Bool)).Instantiation
  | _, .zero => Pedersen.verify.procedure
  | _, .succ .zero => Pedersen.commit.procedure
  | _, .succ (.succ .zero) => Pedersen.gen.procedure

@[simp] theorem pedersenInst_zero : pedersenInst HoleIndex.zero = Pedersen.verify.procedure := rfl
@[simp] theorem pedersenInst_one :
    pedersenInst (HoleIndex.succ HoleIndex.zero) = Pedersen.commit.procedure := rfl
@[simp] theorem pedersenInst_two :
    pedersenInst (HoleIndex.succ (HoleIndex.succ HoleIndex.zero)) = Pedersen.gen.procedure := rfl

omit [PedersenGroup] in
/-- `Module.procedure` read off a known expression: the witness of `proc_type_is_proc` is unique
    by constructor injectivity, so exhibiting `m.expression` as a `.proc` node determines it. -/
theorem procedure_eq {sig : ProcedureSignature} {m : Module (.proc sig)} {p : Procedure sig}
    (h : m.expression = .proc p) : m.procedure = p := by
  have h2 := Module.procedure_spec m
  rw [h] at h2
  injection h2 with hsig hp
  exact hp.symm

omit [PedersenGroup] in
/-- `Module.procWithHoles` at a non-empty hole list is just the `.procHoles` node.  The `module`
command emits its functors through `Module.procWithHoles`, so this is what lets a generated
functor match `functorApp_procedure`'s pattern. -/
@[simp] theorem procWithHoles_expression {holes : HoleSigs} {s : ProcedureSignature}
    {sig : ProcedureSignature} (p : ProcedureWithHoles (HoleSigs.append holes s) sig) :
    (Module.procWithHoles p).expression = .procHoles (by trivial) p := by
  simp only [Module.procWithHoles, ModuleExpression.toModule]
  exact ModuleExpression.reduce_of_normal .procHoles

omit [PedersenGroup] in
/-- **Generic functor-application bridge.**  Applying a one-parameter functor module — anything
of the shape `(.abs (.app (.procHoles ne main) r)).toModule`, which is exactly what both a
hand-written functor and the `module X (A) { … }` command produce — to an argument `S` yields
`main` with its holes instantiated.

Everything reduction-theoretic is done here, once: `reduce_app_left` strips `toModule`'s
`.reduce`, `reduce_beta` fires the β-redex, the substitution computes, and `.delta` fires.  The
caller is left with `hSr` alone — "the rearrangement `r`, with `S` substituted in, reduces to the
instantiation's argument tuple" — which is the only genuinely per-functor content, since how a
parameter's fields map onto `main`'s holes is what makes one functor differ from another.  It is
also mechanical to discharge: `reduce_simp` normalises it given the parameter's record equation. -/
theorem functorApp_procedure {A : ModuleTypeRep} {holes : HoleSigs} {sig : ProcedureSignature}
    {ne : holes.NonEmpty} {main : ProcedureWithHoles holes sig} {r : ModuleExpression}
    {S : Module A} {inst : holes.Instantiation}
    {hF : ModuleExpression.HasType (.abs (.app (.procHoles ne main) r)) [] (.arr A (.proc sig))}
    (hSr : (r.substitute S.expression).reduce
      = HoleSigs.Instantiation.toModuleExpr inst) :
    (Module.app' ((ModuleExpression.abs (.app (.procHoles ne main) r)).toModule hF) S).procedure
      = main.instantiate inst := by
  apply procedure_eq
  simp only [Module.app', ModuleExpression.toModule]
  rw [ModuleExpression.reduce_app_left, ModuleExpression.reduce_beta]
  change ((ModuleExpression.procHoles ne main).app (r.substitute S.expression)).reduce = _
  rw [← ModuleExpression.reduce_app_right, hSr,
    ModuleExpression.reduce_step (.delta ne main inst)]
  exact ModuleExpression.reduce_proc _

/-- Proves `(Module.app F S).procedure = main.instantiate inst` for a one-parameter functor `F`
(given by name) whose argument `S` has the record equation `hS : S.expression = …` (also by
name).  Everything is generic: unfold `F` to expose the `.abs`, hand the β/δ reduction to
`functorApp_procedure`, compute the substitution, rewrite by `hS`, and let `reduce_simp`
normalise the rearrangement.  The closing `rfl` is the last defeq step onto
`inst.toModuleExpr` — `toModuleExpr` computes, so it never needs a proof.

The companion of Dominique's `module_apply`: that one applies a `module`-declared functor to its
parameters (stopping at the record of applied procedures); this one takes the extra δ-step to the
procedure with its holes filled in. -/
macro "functor_procedure" f:ident hS:ident : tactic =>
  `(tactic|
      (simp only [GaudisCrypt.Module.app, GaudisCrypt.Module.moduleTypeRep, $f:ident,
         procWithHoles_expression]
       apply functorApp_procedure
       simp only [GaudisCrypt.ModuleExpression.substitute,
         GaudisCrypt.ModuleExpression.substituteSimultaneously,
         GaudisCrypt.ModuleExpression.variableSubstitution]
       rw [$hS:ident]
       reduce_simp
       try rfl))

/-- `Pedersen`'s expression is the ground record of its three procedures.  This is the only fact
about *the scheme* any bridge lemma needs; everything else is generic. -/
theorem Pedersen_expression : Pedersen.expression
    = .pair (.proc Pedersen.gen.procedure)
        (.pair (.proc Pedersen.commit.procedure) (.proc Pedersen.verify.procedure)) := by
  simp only [Pedersen, CommitmentScheme.mk, Module.pair', Module.proc,
    ModuleExpression.toModule, Pedersen.gen, Pedersen.commit, Pedersen.verify,
    ModuleExpression.reduce_proc]
  rw [ModuleExpression.reduce_of_normal (ModuleExpression.Normal.pair .proc .proc)]
  exact ModuleExpression.reduce_of_normal (.pair .proc (.pair .proc .proc))

/-- **The bridge**: the procedure of the applied functor module is the instantiated body.  All
the reduction work lives in `functorApp_procedure`; what is left here is only `Correctness`'s own
rearrangement — its `gen`/`commit`/`verify` projections, in the order its holes expect — which
`reduce_simp` normalises from `Pedersen_expression`. -/
theorem Correctness_Pedersen_procedure :
    (Module.app Correctness Pedersen).procedure
      = Correctness.main.procedure.instantiate pedersenInst := by
  rw [Correctness.apply_simp]
  functor_procedure Correctness.main Pedersen_expression

/-! ### Per-procedure wp lemmas (EC's `inline`+`auto` steps, done once per procedure) -/


/-- The wp of each Pedersen procedure, stated at the `CommitmentTypes`-spelled signature the
    instantiated game carries (definitionally `G`/`F`; the spelling makes the simp keys match). -/
theorem wp_gen (f : ProgramDenotation.Post State CommitmentTypes.Value) :
    (procedureDenotation (sig := procsig () -> CommitmentTypes.Value)
        Pedersen.gen.procedure ()).wp f
      = fun st => ∑ x : F, f (g ^ x, st) / Fintype.card F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.gen.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, LocalVariableState.varsL]

theorem wp_commit (args : G × F)
    (f : ProgramDenotation.Post State
      (CommitmentTypes.Commitment × CommitmentTypes.OpeningKey)) :
    (procedureDenotation
        (sig := procsig (CommitmentTypes.Value, CommitmentTypes.Message) ->
          (CommitmentTypes.Commitment × CommitmentTypes.OpeningKey))
        Pedersen.commit.procedure args).wp f
      = fun st => ∑ x : F, f ((g ^ x * args.1 ^ args.2, x), st) / Fintype.card F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.commit.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
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
        Pedersen.verify.procedure args).wp f
      = fun st => f (args.2.2.1 == g ^ args.2.2.2 * args.1 ^ args.2.1, st) := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.verify.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
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
    (procedureDenotation (Module.app Correctness Pedersen).procedure m σ).ofEvent
      {r : Bool × State | r.1 = false} = 0 := by
  rw [Correctness_Pedersen_procedure]
  -- reduce `ofEvent` to a `wp` with the indicator postcondition
  suffices h : (procedureDenotation (Correctness.main.procedure.instantiate pedersenInst) m).wp
      (({r : Bool × State | r.1 = false}).indicator fun _ => 1) σ = 0 by
    have hi := expectation_indicator
      (procedureDenotation (Correctness.main.procedure.instantiate pedersenInst) m σ)
      {r : Bool × State | r.1 = false} 1
    rw [one_mul] at hi
    have h' : (↑((procedureDenotation
        (Correctness.main.procedure.instantiate pedersenInst) m σ).ofEvent
        {r : Bool × State | r.1 = false}) : ENNReal) = 0 := by
      rw [← hi]; exact h
    exact_mod_cast h'
  -- unfold the game and push `wp` through
  rw [procedureDenotation_eq_procWrap_gen, wp_procWrap]
  simp [Correctness.main.procedure, StmtWithHoles.instantiate, programDenotation,
    StmtWithHoles.call, wp_bind, wp_get_g, wp_set_g, wp_zoom,
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
