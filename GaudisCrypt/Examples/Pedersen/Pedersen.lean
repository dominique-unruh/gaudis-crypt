import GaudisCrypt.Examples.Pedersen.Commitment

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

/-- The procedure of a proc-typed module. -/
noncomputable def _root_.GaudisCrypt.Language.Modules.Module.procedure
    {sig : ProcedureSignature} (m : Module (.proc sig)) : Procedure sig :=
  (proc_type_is_proc m.normal).choose

/-- **Correctness of Pedersen** — EC's
    `hoare[Correctness(Pedersen).main : true ==> res]`: from any initial state, the
    correctness game never returns `false`. -/
theorem pedersen_correctness (m : F) (σ : State) :
    (procedureDenotation (Correctness Pedersen).procedure m σ).ofEvent
      {r : Bool × State | r.1 = false} = 0 := by
  sorry

end GaudisCrypt.Examples.Pedersen
