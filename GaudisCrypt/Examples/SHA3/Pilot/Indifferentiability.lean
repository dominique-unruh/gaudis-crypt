import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Logic.Granular

/-!
# Indifferentiability (EasyCrypt `proof/Indifferentiability.eca`) — EC-fidelity port

A construction `C` of a functionality from a primitive is indifferentiable from an ideal
functionality `F` when some simulator `S` makes `Indif(C(P), P, D)` and `Indif(F, S(F), D)`
indistinguishable to every distinguisher `D`.

The theory's types are `outParam`s of the (field-less) class `Params p f_in f_out`: a clone is
`clone Indifferentiability as Indiff0 with type p <- …` (`Syntax/Clone.lean`), and inside the
theory nothing is written.  EC's subtyping of module types (`FUNCTIONALITY <: DFUNCTIONALITY`) is
`module_subtype`.  EC's call restrictions (`{ P.f }`) are not part of a module type (exception
E2 of the port): they are the `ext` of `declare module`'s representability.
-/

namespace GaudisCrypt.SHA3.Pilot.Indifferentiability

open GaudisCrypt

/-- EC's `type p.`, `type f_in, f_out.`: the theory's types (a clone fixes them). -/
class Params (p f_in f_out : outParam Type) : Prop

variable {p f_in f_out : Type} [Params p f_in f_out]

/-! A primitive: the building block we assume ideal. -/

moduletype PRIMITIVE {
  proc init () -> Unit;
  proc f (x : p) -> p;
  proc fi (x : p) -> p;
}

moduletype DPRIMITIVE {
  proc f (x : p) -> p;
  proc fi (x : p) -> p;
}

/-! A functionality: the target construction. -/

moduletype FUNCTIONALITY {
  proc init () -> Unit;
  proc f (x : f_in) -> f_out;
}

moduletype DFUNCTIONALITY {
  proc f (x : f_in) -> f_out;
}

/-- A `PRIMITIVE` is a `DPRIMITIVE` (its `f`, `fi`). -/
module_subtype PRIMITIVE <: DPRIMITIVE

/-- A `FUNCTIONALITY` is a `DFUNCTIONALITY` (its `f`). -/
module_subtype FUNCTIONALITY <: DFUNCTIONALITY

/-- EC's `module type CONSTRUCTION (P : DPRIMITIVE) = { proc init() : unit {}
proc f(x : f_in): f_out { P.f } }`. -/
abbrev CONSTRUCTION := DPRIMITIVE →ₘ FUNCTIONALITY

/-- EC's `module type SIMULATOR (F : DFUNCTIONALITY) = { proc init() : unit { }
proc f(x : p) : p { F.f } proc fi(x : p) : p { F.f } }`. -/
abbrev SIMULATOR := DFUNCTIONALITY →ₘ PRIMITIVE

/-- EC's `module type DISTINGUISHER (F : DFUNCTIONALITY, P : DPRIMITIVE) =
{ proc distinguish(): bool }`. -/
abbrev DISTINGUISHER := DFUNCTIONALITY ×ₘ DPRIMITIVE →ₘ procmod () → Bool

module Indif using (F : FUNCTIONALITY, P : PRIMITIVE, D : DISTINGUISHER) {
  proc main () : Bool {
    var b : Bool;
    _ <- call P.init ();
    _ <- call F.init ();
    b <- call D(F, P).distinguish ();
    return $b
  };
}

/-- `module GReal(C : CONSTRUCTION, P : PRIMITIVE) = Indif(C(P), P)`. -/
noncomputable abbrev GReal (C : CONSTRUCTION) (P : PRIMITIVE) (D : DISTINGUISHER) :
    procmod () → Bool :=
  Module.app Indif (Module.pair (Module.app C P) (Module.pair P D))

/-- `module GIdeal(F : FUNCTIONALITY, S : SIMULATOR) = Indif(F, S(F))`. -/
noncomputable abbrev GIdeal (F : FUNCTIONALITY) (S : SIMULATOR) (D : DISTINGUISHER) :
    procmod () → Bool :=
  Module.app Indif (Module.pair F (Module.pair (Module.app S F) D))

end GaudisCrypt.SHA3.Pilot.Indifferentiability
