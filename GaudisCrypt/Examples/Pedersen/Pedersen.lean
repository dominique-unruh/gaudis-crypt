import GaudisCrypt.Examples.Pedersen.Commitment
import GaudisCrypt.WeakestPreconditions
import GaudisCrypt.Logic.Hoare
import GaudisCrypt.Logic.Inline
import GaudisCrypt.Logic.HoareSplit
import GaudisCrypt.Logic.HoareWp

/-!
# The Pedersen commitment scheme

A transliteration of EasyCrypt's `examples/Pedersen.ec`:

* EC's `clone DLog` (cyclic group `group` with generator `g`, prime exponent field `exp`)
  becomes the structure `PedersenGroup`: the operations the programs mention, plus the laws the
  proofs turned out to need (`f_commring`, `gpow_add`, `gpow_mul` — the last two are EC's
  `expD`/`expM`).  It is a section `variable (group : PedersenGroup)`, and hence a Lean parameter
  of everything below that mentions it.
* EC's `PedersenTypes` + the `Commitment` clone become the `CommitmentTypes` record
  `group.types` (value/commitment = group, message/openingkey = exponent), which every
  `CommitmentScheme`-shaped name here is applied to.
* `module Pedersen : CommitmentScheme` becomes a
  `module Pedersen : (CommitmentScheme group.types) { … }` declaration — EC's own syntax, near
  enough, now that the `module` command exists.
* Correctness is stated as EC states it (`hoare[Correctness(Pedersen).main : true ==> res]`):
  the output distribution puts no mass on `res = false`.  Proven (`pedersen_correctness`), on
  standard axioms only, entirely on the `module` command's generated lemmas — this file declares
  nothing of its own for it beyond the per-procedure `wp_*` lemmas.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt

-- the scheme is deliberately named like the enclosing example namespace (EC: `module Pedersen`)
set_option linter.dupNamespace false

/-! ## The group setup (EC's `DLog` clone) -/

/-- A cyclic group `G` with generator `g` and exponent type `F` (EC's `group`/`exp`).
    Multiplication and exponentiation, what the programs genuinely need of the types — a default
    element (`Inhabited`, so local variables can be declared) and `Fintype F` (real content:
    `SubProbability.uniform` samples it, and the wp lemmas sum over it) — and the algebraic laws
    the proofs need, which are the three fields documented individually below.  Correctness needs
    none of the laws; they are all for `Hiding.lean`.

    Decidable equality is *not* a field.  `verify` does compare (`$c == $c'`), and `==` is `BEq`
    derived from `DecidableEq` — but these programs are never executed: every `proc` is
    `noncomputable` and the semantics is a measure, so the comparison only ever has to *denote* a
    `Bool`, not compute one.  `Classical.decEq` supplies that for free, which is why the instances
    below are classical and the class is two fields shorter.  Nothing in the proofs cares: they
    reason about `=`, and `beq_self_eq_true` and friends hold for any `DecidableEq` witness. -/
structure PedersenGroup where
  G : Type
  F : Type
  g : G
  -- TODO: Change to `[Mul G]`
  gmul : G → G → G
  -- TODO: Change to `[Pow G F]`
  gpow : G → F → G
  [g_inhabited : Inhabited G]
  -- TODO: Remove. Implied by CommRing F.
  [f_inhabited : Inhabited F]
  [f_fintype : Fintype F]
  /-- EC's exponent type is the prime field `DL.GP.ZModE`; the hiding proof forms `d + x * m`
      and its inverse `d - x * m`, so the additive group and the multiplication are both needed.
      (Only the ring structure is required — nothing here uses inverses.) -/
  [f_commring : CommRing F]
  /-- EC's `expD`: exponentiation turns addition into multiplication. -/
  gpow_add : ∀ (h : G) (a b : F), gpow h (a + b) = gmul (gpow h a) (gpow h b)
  /-- EC's `expM`: iterated exponentiation multiplies the exponents. -/
  gpow_mul : ∀ (h : G) (a b : F), gpow (gpow h a) b = gpow h (a * b)

-- namespace PedersenGroup

variable (group : PedersenGroup)

@[reducible] instance : Inhabited group.G := group.g_inhabited
@[reducible] noncomputable instance : DecidableEq group.G := Classical.decEq _
@[reducible] instance : Inhabited group.F := group.f_inhabited
@[reducible] instance : CommRing group.F := group.f_commring
@[reducible] noncomputable instance : DecidableEq group.F := Classical.decEq _
@[reducible] instance : Fintype group.F := group.f_fintype
@[reducible] instance : Mul group.G := ⟨group.gmul⟩
@[reducible] instance : Pow group.G group.F := ⟨group.gpow⟩

/-- `gpow_add` at the `^`/`*` notation.  The class fields have to be stated with the raw
    `gmul`/`gpow` (the instances below them do not exist yet), but every use site sees the
    notation, and `rw` matches on the notation's head — not the raw field. -/
theorem pow_add (h : group.G) (a b : group.F) : h ^ (a + b) = h ^ a * h ^ b := group.gpow_add h a b

/-- `gpow_mul` at the `^` notation. -/
theorem pow_mul (h : group.G) (a b : group.F) : (h ^ a) ^ b = h ^ (a * b) := group.gpow_mul h a b

-- end PedersenGroup

-- open PedersenGroup (G F g)


/-- EC's `PedersenTypes` + `clone Commitment with …`: value/commitment are group elements,
    message/openingkey are exponents. -/
/- Reducible on purpose. It used to be an `instance`, which carries `@[reducible]` implicitly, and
the `wp_*` proofs below rely on it: they are stated at `group.types.Commitment` and worked on at
`group.G`, and every `simp` that has to see through that spelling needs the record to unfold at
`reducible` transparency. A plain `def` leaves `programDenotation` stuck on the `.seq` of the
procedure's body. -/
@[reducible] def PedersenGroup.types : CommitmentTypes where
  Value := group.G
  Message := group.F
  Commitment := group.G
  OpeningKey := group.F
  value_inhabited := inferInstance
  message_inhabited := inferInstance
  commitment_inhabited := inferInstance
  openingKey_inhabited := inferInstance

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

module Pedersen : (CommitmentScheme group.types) {
  /- Sample a secret exponent, publish `h = g ^ x`. -/
  proc gen() : group.G {
    var x : group.F;
    var h : group.G;
    x <$ SubProbability.uniform;
    h <- group.g ^ $x;
    return $h
  };
  /- Commit to `m` under `h`: sample the opening key `d`, output `g ^ d * h ^ m`. -/
  proc commit(h : group.G, m : group.F) : (group.G × group.F) {
    var c : group.G;
    var d : group.F;
    d <$ SubProbability.uniform;
    c <- group.g ^ $d * $h ^ $m;
    return ($c, $d)
  };
  /- Recompute the commitment and compare. -/
  proc verify(h : group.G, m : group.F, c : group.G, d : group.F) : Bool {
    var c' : group.G;
    c' <- group.g ^ $d * $h ^ $m;
    return $c == $c'
  };
}

-- Still used by Hiding
theorem wp_gen (f : ProgramDenotation.Post VariableAssignment group.types.Value) :
    (procedureDenotation (sig := procsig () -> group.types.Value)
        (Pedersen.gen.procedure group) ()).wp f
      = fun st => ∑ x : group.F, f (group.g ^ x, st) / Fintype.card group.F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.gen.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    localVarLens, Lens.intoLocal, Lens.chain, varLens_set, ProgramState.localL]

-- Still used by Hiding
theorem wp_commit (args : group.G × group.F)
    (f : ProgramDenotation.Post VariableAssignment
      (group.types.Commitment × group.types.OpeningKey)) :
    (procedureDenotation
        (sig := procsig (group.types.Value, group.types.Message) ->
          (group.types.Commitment × group.types.OpeningKey))
        (Pedersen.commit.procedure group) args).wp f
      = fun st => ∑ x : group.F, f ((group.g ^ x * args.1 ^ args.2, x), st)
          / Fintype.card group.F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  -- write the arguments into the parameter slots first: in the full simp set below, the
  -- equation lemmas of `setParams` loop
  obtain ⟨a, b⟩ := args
  simp only [Pedersen.commit.procedure, ProcedureWithHoles.initLocals,
    VariableAssignment.setParams]
  simp [programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g, wp_set_g,
    wp_lift, uniform_expected, expected_pure,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    localVarLens, Lens.intoLocal, Lens.chain, varLens_set, ProgramState.localL]

-- TODO: Concrete syntax for Module.app. Either a special infix symbol, or a coercion that allows M(A,B).

theorem pedersen_correctness2 :
    hoare[
      ((Module.app (Correctness group.types) (Pedersen group)).main) :
      True
      ==>
      $res = true
    ] := by
  hoare_proc_to_stmt
  hoare_inline 0
  hoare_wp 1
  hoare_inline 2
  hoare_wp 4
  hoare_inline 1
  hoare_wp 5
  hoare_inline 0
  hoare_wp 6
  hoare_skip
  simp

end GaudisCrypt.Examples.Pedersen
