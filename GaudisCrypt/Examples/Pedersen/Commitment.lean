import GaudisCrypt.Language.Syntax2

/-!
# Generic commitment schemes

A transliteration of EasyCrypt's `theories/crypto/Commitment.ec` (theory
`CommitmentProtocol`) into the Gaudí module/procedure syntax.

* EC's abstract theory types `value`, `message`, `commitment`, `openingkey` become the
  type class `CommitmentTypes` (instance-implicit section parameters, so the
  `moduletype`-generated definitions elaborate — the same pattern as `[ProgramSpec]`).
* EC `module type`s become `moduletype`s.
* EC's parameterized modules (`Correctness(S)`, `HidingExperiment(S,U)`,
  `BindingExperiment(S,B)`) become procedures with holes (`proc … uses (…)`): the holes
  are the procedures of the module parameters, flattened.
-/

namespace GaudisCrypt.Examples.Pedersen

/-

Dominique's TODOs:

- [X] rename ModuleTypeRep -> ModuleTypeRepRep
- [X] class IsModule
- [X] instances for that class (see below)
- [ ] →ₘ should be `Type -> Type -> Type` (using the instance)
-     (For ModuleTypeRepRep: no pretty syntax)
- [ ] extend `moduletype X` command
  - [X] also define X.moduleTypeRep (Is: X.typeRep)
  - [ ] do: `instance IsModule X`


In a different iteration:
- `module A(params) : X { ... }` syntax (does def A : X := lambda-expression).
  `(params)` optional.
- Maybe also support `let A := module ...` or `def A := module ...` etc

DoesnotUse A X.op (in proof, do induction, proof ⊥ from X.op use)

-/

open GaudisCrypt


/-- The abstract types of EC's `theory CommitmentProtocol`: the public value (key), the
    message space, commitments, and opening keys.  `Inhabited` is needed for program
    local variables of these types; `DecidableEq Message` for the binding experiment's
    `m ≠ m'` test. -/
class CommitmentTypes where
  Value : Type
  Message : Type
  Commitment : Type
  OpeningKey : Type
  /-- TODO: change Nonempty -/
  -- NOTE: required because local variables need to be inhabited
  -- TODO  Use individual [Nonempty types.Value] etc. instead of NonEmptyCommitmentTypes
  value_inhabited : Inhabited Value
  message_inhabited : Inhabited Message
  commitment_inhabited : Inhabited Commitment
  openingKey_inhabited : Inhabited OpeningKey
  -- TODO: remove this and use classical
  message_deceq : DecidableEq Message



-- TODO Make CommitmentTypes into a structure
-- variable (types : CommitmentTypes) in the section

/- DON'T DO:

class NonEmptyCommitmentTypes (types : CommitmentTypes) where
  nonempty_value : Nonempty types.Value
  nonempty_message : Nonempty types.Message
  nonempty_commitment : Nonempty types.Commitment
  nonempty_openingKey : Nonempty types.OpeningKey

  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Value := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Message := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Commitment := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.OpeningKey := sorry

instance (t : CommitmentTypes) [Nonempty t.Value] [Nonempty t.Message] [Nonempty t.Commitment]
[Nonempty t.OpeningKey] : NonEmptyCommitmentTypes t :=
sorry

  variable (types : CommitmentTypes)
  variable [NonEmptyCommitmentTypes types]
-/


instance [CommitmentTypes] : Inhabited CommitmentTypes.Value :=
  CommitmentTypes.value_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.Message :=
  CommitmentTypes.message_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.Commitment :=
  CommitmentTypes.commitment_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.OpeningKey :=
  CommitmentTypes.openingKey_inhabited
instance [CommitmentTypes] : DecidableEq CommitmentTypes.Message :=
  CommitmentTypes.message_deceq

-- TODO: move to the proper place (unless already exist)
/-! ### Disjointness of tuple-projection lenses

The `proc` macro binds each local variable to a `Lens.id.ofst/.osnd` projection chain into
the local-state tuple; tuple *assignment* (`c, d <- …`) pairs those lenses via `Lens.pair`,
which needs them `disjoint`.  Distinct projection paths are always disjoint — the instances
below derive that.  (Candidates for `Language/Lens.lean`.)

⚠ They do **not** yet make tuple assignment of *locals* work: the macro binds locals as
`let`-variables, and instance search does not unfold local `let`s, so `disjoint c d` is
searched at the opaque variables and never reaches these instances.  Until the macro binds
locals differently (or registers the disjointness facts itself), the experiments below use
pair-typed locals and `$`-projections instead of tuple assignment. -/

-- TODO: changes to named variable if CommitmentTypes becomes a structure
variable [ProgramSpec] [CommitmentTypes]

-- With structure, replace by `local(?) abbrev Value := CommitmentTypes.Value types` etc. and remove the `open` below
open CommitmentTypes (Value Message Commitment OpeningKey)

/-! ## Module types

```
module type CommitmentScheme = {
  proc gen() : value
  proc commit(x: value, m: message) : commitment * openingkey
  proc verify(x: value, m: message, c: commitment, d: openingkey) : bool
}.
``` -/

moduletype CommitmentScheme {
  proc gen () -> Value;
  proc commit (Value, Message) -> Commitment × OpeningKey;
  proc verify (Value, Message, Commitment, OpeningKey) -> Bool;
}

-- EC's `Unhider`: the hiding-game adversary.
moduletype Unhider {
  proc choose (Value) -> Message × Message;
  proc guess (Commitment) -> Bool;
}

-- EC's `Binder`: the binding-game adversary.
moduletype Binder {
  proc bind (Value) -> Commitment × Message × OpeningKey × Message × OpeningKey;
}

/- /-- The `ModuleTypeRep` underlying `CommitmentScheme` (the right-nested product the
    `moduletype` command generates), named so that functor types over it can be written. -/
def CommitmentSchemeT : ModuleTypeRep :=
  procmod () -> Value ×
  procmod (Value, Message) -> (Commitment × OpeningKey) ×
  procmod (Value, Message, Commitment, OpeningKey) -> Bool
 -/

/-
Need: CommitmentSchemeM = Module CommitmentSchemeT

Currently: CommitmentScheme, not-provided
Could: CommitmentScheme, CommitmentScheme.ModuleT
Could: CommitmentScheme.Module, CommitmentScheme
Could: `Module CommitmentScheme`, CommitmentScheme

-/
example : CommitmentScheme = Module CommitmentScheme.typeRep := rfl

/-! ## Experiments (parameterized modules)

Each EC functor becomes a *module of arrow type* over `CommitmentSchemeT` (& co.): the body
is a procedure with holes — the holes are the parameter modules' procedures — wrapped by
`ModuleExpression.abs` into a closed functor module.  The lambda repackages the scheme
product (declaration order, no unit) into the holes tuple (reverse order, `.unit`-terminated)
with `fst`/`snd`/`pair`. -/

/-- The body of `Correctness(S)`: commit and verify honestly. -/
noncomputable def Correctness.main := proc (m : Message) uses
    (gen : () → Value,
     commit : (Value, Message) → Commitment × OpeningKey,
     verify : (Value, Message, Commitment, OpeningKey) → Bool) : Bool {
  var x : Value;
  var cd : Commitment × OpeningKey;
  var b : Bool;
  x <- call gen ();
  cd <- call commit ($x, $m);
  b <- call verify ($x, $m, ($cd).1, ($cd).2);
  return $b
}


-- def Module.Arr {A B : ModuleTypeRep} (M : Module A) (f : Module (A →ₘ B)) : Module B :=
--   ⟨fun _ => f.toProc⟩

-- If `X := Module A` and `Y := Module B`, want to write `X --> Y` for `Module (A →ₘ B)`.



instance : IsModule CommitmentScheme where
  moduleTypeRep := CommitmentScheme.typeRep
  isModule := rfl

/-- EC's `module Correctness (S : CommitmentScheme)`, as a functor module: apply it to a
    scheme with `Correctness S` (module application). -/
noncomputable def Correctness :
  Module.Arr CommitmentScheme (Module (procmod (Message) -> Bool)) :=
  -- Module (CommitmentSchemeT →ₘ CorrectnessGameT (which has named procedures)) :=
  -- Module.Arr  CommitmentScheme (Module (procmod (Message) -> Bool)) :=
  (ModuleExpression.abs
    (.app (.procHoles (by trivial) Correctness.main)
      (.pair (.snd (.snd (.var .zero)))       -- verify
        (.pair (.fst (.snd (.var .zero)))     -- commit
          (.pair (.fst (.var .zero))          -- gen
            .unit))))).toModule

/-- `Correctness(S)` elaborates: the functor applies to any `S : CommitmentScheme`. -/
noncomputable example (S : CommitmentScheme) : Module (procmod (Message) -> Bool) :=
  Module.app Correctness S


end GaudisCrypt.Examples.Pedersen
