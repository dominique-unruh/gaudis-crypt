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

open GaudisCrypt
open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Syntax

/-- The abstract types of EC's `theory CommitmentProtocol`: the public value (key), the
    message space, commitments, and opening keys.  `Inhabited` is needed for program
    local variables of these types; `DecidableEq Message` for the binding experiment's
    `m ≠ m'` test. -/
class CommitmentTypes where
  Value : Type
  Message : Type
  Commitment : Type
  OpeningKey : Type
  value_inhabited : Inhabited Value
  message_inhabited : Inhabited Message
  commitment_inhabited : Inhabited Commitment
  openingKey_inhabited : Inhabited OpeningKey
  message_deceq : DecidableEq Message

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

instance Lens.disjoint_ofst_osnd {a b m m' : Type*} (x : Lens a m) (y : Lens b m') :
    disjoint (Lens.ofst (m' := m') x) (Lens.osnd (m' := m) y) :=
  ⟨fun _ _ _ => rfl⟩

instance Lens.disjoint_osnd_ofst {a b m m' : Type*} (x : Lens a m') (y : Lens b m) :
    disjoint (Lens.osnd (m' := m) x) (Lens.ofst (m' := m') y) :=
  ⟨fun _ _ _ => rfl⟩

instance Lens.disjoint_chain {a₁ a₂ b c : Type*} (L : Lens b c) (x : Lens a₁ b) (y : Lens a₂ b)
    [d : disjoint x y] : disjoint (L.chain x) (L.chain y) :=
  ⟨fun s v w => by
    change L.set (x.set v (L.get (L.set (y.set w (L.get s)) s))) (L.set (y.set w (L.get s)) s)
       = L.set (y.set w (L.get (L.set (x.set v (L.get s)) s))) (L.set (x.set v (L.get s)) s)
    rw [L.set_get, L.set_get, L.set_set, L.set_set, d.commute]⟩

instance Lens.disjoint_ofst_ofst {a b m m' : Type*} (x : Lens a m) (y : Lens b m)
    [disjoint x y] : disjoint (Lens.ofst (m' := m') x) (Lens.ofst (m' := m') y) :=
  Lens.disjoint_chain Lens.fst x y

instance Lens.disjoint_osnd_osnd {a b m m' : Type*} (x : Lens a m) (y : Lens b m)
    [disjoint x y] : disjoint (Lens.osnd (m' := m') x) (Lens.osnd (m' := m') y) :=
  Lens.disjoint_chain Lens.snd x y

variable [ProgramSpec] [CommitmentTypes]

/-- Local program variables are `Lens.intoVars` of their slot projections; distinct slots
    are disjoint, and `intoVars` (two `chain` layers) preserves that. -/
instance Lens.disjoint_intoVars {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple (locals.map (·.fst)))}
    {y : Lens b (paramListToTuple (locals.map (·.fst)))} [disjoint x y] :
    disjoint (Lens.intoVars (paramTypes := paramTypes) x) (Lens.intoVars y) :=
  Lens.disjoint_chain ProcedureState.localL _ _

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

/-- The `ModuleType` underlying `CommitmentScheme` (the right-nested product the
    `moduletype` command generates), named so that functor types over it can be written. -/
def CommitmentSchemeT : ModuleType :=
  procmod () -> Value ×
  procmod (Value, Message) -> (Commitment × OpeningKey) ×
  procmod (Value, Message, Commitment, OpeningKey) -> Bool

example : CommitmentScheme = Module CommitmentSchemeT := rfl

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

/-- EC's `module Correctness (S : CommitmentScheme)`, as a functor module: apply it to a
    scheme with `Correctness S` (module application). -/
noncomputable def Correctness : Module (CommitmentSchemeT →ₘ procmod (Message) -> Bool) :=
  (ModuleExpression.abs
    (.app (.procHoles (by trivial) Correctness.main)
      (.pair (.snd (.snd (.var .zero)))       -- verify
        (.pair (.fst (.snd (.var .zero)))     -- commit
          (.pair (.fst (.var .zero))          -- gen
            .unit))))).toModule

/-- `Correctness(S)` elaborates: the functor applies to any `S : CommitmentScheme`. -/
noncomputable example (S : CommitmentScheme) : Module (procmod (Message) -> Bool) :=
  Correctness S


end GaudisCrypt.Examples.Pedersen
