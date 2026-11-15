import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Logic.Granular

/-!
# Indifferentiability with failing oracles (EasyCrypt `proof/OptionIndifferentiability.eca`) —
EC-fidelity port

`Indifferentiability.eca` with procedures that may fail: the primitive and the functionality
return `option`s, and every name gets an `O` prefix.  The translation is that of
`Indifferentiability.lean`: the theory's types are `outParam`s of the (field-less) class
`Params p f_in f_out`, so a clone is `clone OptionIndifferentiability as OIndif with type p <- …`
(`Syntax/Clone.lean`); EC's subtyping of module types is `module_subtype`; EC's call
restrictions (`{ P.f }`) are not part of a module type (exception E2 of the port), they are the
`ext` of `declare module`'s representability.
-/

section FirstPort

/-!
## Declarations of the first port

Definitions and plain lemmas of the first port of this file (2026-10/11) that the proofs below
use; its program-logic proofs are gone.
-/

namespace GaudisCrypt.SHA3.OptionIndifferentiability

open GaudisCrypt

variable (p f_in f_out : Type)

-- A primitive: the building block we assume ideal.
moduletype OPRIMITIVE {
  proc init () -> Unit;
  proc f (x : p) -> (Option p);
  proc fi (x : p) -> (Option p);
}

moduletype ODPRIMITIVE {
  proc f (x : p) -> (Option p);
  proc fi (x : p) -> (Option p);
}

-- A functionality: the target construction.
moduletype OFUNCTIONALITY {
  proc init () -> Unit;
  proc f (x : f_in) -> (Option f_out);
}

moduletype ODFUNCTIONALITY {
  proc f (x : f_in) -> (Option f_out);
}

/-- EasyCrypt's `module type OCONSTRUCTION (P : ODPRIMITIVE) = { proc init() : unit {}
proc f(x : f_in): f_out option { P.f } }`: a construction takes a primitive and builds a
functionality. -/
abbrev OCONSTRUCTION := ODPRIMITIVE p f_in f_out →ₘ OFUNCTIONALITY p f_in f_out

/-- EasyCrypt's `module type OSIMULATOR (F : ODFUNCTIONALITY) = { proc init() : unit { }
proc f(x : p) : p option { F.f } proc fi(x : p) : p option { F.f } }`: a simulator takes a
functionality and simulates the primitive. -/
abbrev OSIMULATOR := ODFUNCTIONALITY p f_in f_out →ₘ OPRIMITIVE p f_in f_out

/-- EasyCrypt's `module type ODISTINGUISHER (F : ODFUNCTIONALITY, P : ODPRIMITIVE) =
{ proc distinguish(): bool }`: a distinguisher gets oracle access to a primitive and a
functionality and returns its guess. -/
abbrev ODISTINGUISHER :=
  ODFUNCTIONALITY p f_in f_out ×ₘ ODPRIMITIVE p f_in f_out →ₘ procmod () → Bool

/-- The distinguisher's view of a functionality (EasyCrypt's subtyping `OFUNCTIONALITY <:
ODFUNCTIONALITY`). -/
noncomputable def OFUNCTIONALITY.view (F : OFUNCTIONALITY p f_in f_out) :
    ODFUNCTIONALITY p f_in f_out :=
  ODFUNCTIONALITY.mk p f_in f_out { f := OFUNCTIONALITY.f p f_in f_out F }

/-- The distinguisher's view of a primitive (EasyCrypt's subtyping `OPRIMITIVE <: ODPRIMITIVE`). -/
noncomputable def OPRIMITIVE.view (P : OPRIMITIVE p f_in f_out) : ODPRIMITIVE p f_in f_out :=
  ODPRIMITIVE.mk p f_in f_out
    { f := OPRIMITIVE.f p f_in f_out P, fi := OPRIMITIVE.fi p f_in f_out P }

module OIndif using (F : OFUNCTIONALITY p f_in f_out, P : OPRIMITIVE p f_in f_out,
    D : ODISTINGUISHER p f_in f_out) {
  proc main () : Bool {
    var b : Bool;
    _ <- call P.init ();
    _ <- call F.init ();
    b <- call (Module.app D
      (Module.pair (ODFUNCTIONALITY.mk p f_in f_out { f := OFUNCTIONALITY.f p f_in f_out F })
        (ODPRIMITIVE.mk p f_in f_out
          { f := OPRIMITIVE.f p f_in f_out P, fi := OPRIMITIVE.fi p f_in f_out P }))) ();
    return $b
  };
}

/-- `module OGReal(C : OCONSTRUCTION, P : OPRIMITIVE) = OIndif(C(P), P)`. -/
noncomputable def OGReal (C : OCONSTRUCTION p f_in f_out) (P : OPRIMITIVE p f_in f_out)
    (D : ODISTINGUISHER p f_in f_out) : procmod () → Bool :=
  Module.app (OIndif p f_in f_out)
    (Module.pair (Module.app C (OPRIMITIVE.view p f_in f_out P)) (Module.pair P D))

/-- `module OGIdeal(F : OFUNCTIONALITY, S : OSIMULATOR) = OIndif(F, S(F))`. -/
noncomputable def OGIdeal (F : OFUNCTIONALITY p f_in f_out) (S : OSIMULATOR p f_in f_out)
    (D : ODISTINGUISHER p f_in f_out) : procmod () → Bool :=
  Module.app (OIndif p f_in f_out)
    (Module.pair F (Module.pair (Module.app S (OFUNCTIONALITY.view p f_in f_out F)) D))

end GaudisCrypt.SHA3.OptionIndifferentiability

end FirstPort

namespace GaudisCrypt.SHA3.Pilot.OptionIndifferentiability

open GaudisCrypt

/-- EC's `type p.`, `type f_in, f_out.`: the theory's types (a clone fixes them). -/
class Params (p f_in f_out : outParam Type) : Prop

variable {p f_in f_out : Type} [Params p f_in f_out]

/-! A primitive: the building block we assume ideal. -/

moduletype OPRIMITIVE {
  proc init () -> Unit;
  proc f (x : p) -> (Option p);
  proc fi (x : p) -> (Option p);
}

moduletype ODPRIMITIVE {
  proc f (x : p) -> (Option p);
  proc fi (x : p) -> (Option p);
}

/-! A functionality: the target construction. -/

moduletype OFUNCTIONALITY {
  proc init () -> Unit;
  proc f (x : f_in) -> (Option f_out);
}

moduletype ODFUNCTIONALITY {
  proc f (x : f_in) -> (Option f_out);
}

/-- An `OPRIMITIVE` is an `ODPRIMITIVE` (its `f`, `fi`). -/
module_subtype OPRIMITIVE <: ODPRIMITIVE

/-- An `OFUNCTIONALITY` is an `ODFUNCTIONALITY` (its `f`). -/
module_subtype OFUNCTIONALITY <: ODFUNCTIONALITY

/-- EC's `module type OCONSTRUCTION (P : ODPRIMITIVE) = { proc init() : unit {}
proc f(x : f_in): f_out option { P.f } }`. -/
abbrev OCONSTRUCTION := ODPRIMITIVE →ₘ OFUNCTIONALITY

/-- EC's `module type OSIMULATOR (F : ODFUNCTIONALITY) = { proc init() : unit { }
proc f(x : p) : p option { F.f } proc fi(x : p) : p option { F.f } }`. -/
abbrev OSIMULATOR := ODFUNCTIONALITY →ₘ OPRIMITIVE

/-- EC's `module type ODISTINGUISHER (F : ODFUNCTIONALITY, P : ODPRIMITIVE) =
{ proc distinguish(): bool }`. -/
abbrev ODISTINGUISHER := ODFUNCTIONALITY ×ₘ ODPRIMITIVE →ₘ procmod () → Bool

module OIndif using (F : OFUNCTIONALITY, P : OPRIMITIVE, D : ODISTINGUISHER) {
  proc main () : Bool {
    var b : Bool;
    _ <- call P.init ();
    _ <- call F.init ();
    b <- call D(F, P).distinguish ();
    return $b
  };
}

/-- `module OGReal(C : OCONSTRUCTION, P : OPRIMITIVE) = OIndif(C(P), P)`. -/
noncomputable abbrev OGReal (C : OCONSTRUCTION) (P : OPRIMITIVE) (D : ODISTINGUISHER) :
    procmod () → Bool :=
  Module.app OIndif (Module.pair (Module.app C P) (Module.pair P D))

/-- `module OGIdeal(F : OFUNCTIONALITY, S : OSIMULATOR) = OIndif(F, S(F))`. -/
noncomputable abbrev OGIdeal (F : OFUNCTIONALITY) (S : OSIMULATOR) (D : ODISTINGUISHER) :
    procmod () → Bool :=
  Module.app OIndif (Module.pair F (Module.pair (Module.app S F) D))

end GaudisCrypt.SHA3.Pilot.OptionIndifferentiability
