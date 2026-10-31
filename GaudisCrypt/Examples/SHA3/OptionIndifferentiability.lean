import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.AbstractCall

/-!
# Indifferentiability with failing oracles (EasyCrypt `proof/OptionIndifferentiability.eca`)

`Indifferentiability.eca` with procedures that may fail: the primitive and the functionality return
`option`s, and every name gets an `O` prefix.  The translation is that of
`GaudisCrypt/Examples/SHA3/Indifferentiability.lean`.

The abstract theory's types `p`, `f_in`, `f_out` are section variables, so a `clone` is an
application.  The module types translate as follows.
* EasyCrypt's `module type X (P : T) = { … }` is the functor type `T →ₘ X'`.
* EasyCrypt's restriction of which oracle procedures a procedure may call (`{ P.f }`) is not part
  of a Gaudí module type.  It is expressed where it matters, by the `ext` of a
  `Module.Representable` hypothesis (`Logic/AbstractCall.lean`, exception E2 of the port).
* `OGReal`/`OGIdeal` are EasyCrypt module aliases (`OIndif(C(P), P)`), so here they are definitions
  that apply `OIndif`.
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

/-- The oracle procedures an `ODISTINGUISHER` may call (EasyCrypt's `OI.allowed`): `F.f`, `P.f`,
`P.fi`.  The holes of its representation (`Module.Representable`, exception E2). -/
abbrev distHoles : HoleSigs :=
  .cons (procsig (f_in) -> (Option f_out))
    (.cons (procsig (p) -> (Option p)) (.cons (procsig (p) -> (Option p)) .empty))

/-- `F.f`, `P.f`, `P.fi` out of the oracles `(F, P)`. -/
noncomputable def distExt (FP : ODFUNCTIONALITY p f_in f_out ×ₘ ODPRIMITIVE p f_in f_out) :
    (distHoles p f_in f_out).Instantiation :=
  ((ODFUNCTIONALITY.f p f_in f_out (Module.fst FP)).procedure,
   (ODPRIMITIVE.f p f_in f_out (Module.snd FP)).procedure,
   (ODPRIMITIVE.fi p f_in f_out (Module.snd FP)).procedure)

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
