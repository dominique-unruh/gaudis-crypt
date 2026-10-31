import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.AbstractCall

/-!
# Indifferentiability (EasyCrypt `proof/Indifferentiability.eca`)

A construction `C` of a functionality from a primitive is indifferentiable from an ideal
functionality `F` when some simulator `S` makes `Indif(C(P), P, D)` and `Indif(F, S(F), D)`
indistinguishable to every distinguisher `D`.

The abstract theory's types `p`, `f_in`, `f_out` are section variables, so a `clone` is an
application.  The module types translate as follows.
* EasyCrypt's `module type X (P : T) = { … }` is the functor type `T →ₘ X'`.
* EasyCrypt's restriction of which oracle procedures a procedure may call (`{ P.f }`) is not part
  of a Gaudí module type.  It is expressed where it matters, by the `ext` of a
  `Module.Representable` hypothesis (`Logic/AbstractCall.lean`, exception E2 of the port).
* `GReal`/`GIdeal` are EasyCrypt module aliases (`Indif(C(P), P)`), so here they are definitions
  that apply `Indif`.
-/

namespace GaudisCrypt.SHA3.Indifferentiability

open GaudisCrypt

variable (p f_in f_out : Type)

-- A primitive: the building block we assume ideal.
moduletype PRIMITIVE {
  proc init () -> Unit;
  proc f (x : p) -> p;
  proc fi (x : p) -> p;
}

moduletype DPRIMITIVE {
  proc f (x : p) -> p;
  proc fi (x : p) -> p;
}

-- A functionality: the target construction.
moduletype FUNCTIONALITY {
  proc init () -> Unit;
  proc f (x : f_in) -> f_out;
}

moduletype DFUNCTIONALITY {
  proc f (x : f_in) -> f_out;
}

/-- EasyCrypt's `module type CONSTRUCTION (P : DPRIMITIVE) = { proc init() : unit {}
proc f(x : f_in): f_out { P.f } }`: a construction takes a primitive and builds a functionality. -/
abbrev CONSTRUCTION := DPRIMITIVE p f_in f_out →ₘ FUNCTIONALITY p f_in f_out

/-- EasyCrypt's `module type SIMULATOR (F : DFUNCTIONALITY) = { proc init() : unit { }
proc f(x : p) : p { F.f } proc fi(x : p) : p { F.f } }`: a simulator takes a functionality and
simulates the primitive. -/
abbrev SIMULATOR := DFUNCTIONALITY p f_in f_out →ₘ PRIMITIVE p f_in f_out

/-- EasyCrypt's `module type DISTINGUISHER (F : DFUNCTIONALITY, P : DPRIMITIVE) =
{ proc distinguish(): bool }`: a distinguisher gets oracle access to a primitive and a
functionality and returns its guess. -/
abbrev DISTINGUISHER :=
  DFUNCTIONALITY p f_in f_out ×ₘ DPRIMITIVE p f_in f_out →ₘ procmod () → Bool

/-- The distinguisher's view of a functionality (EasyCrypt's subtyping `FUNCTIONALITY <:
DFUNCTIONALITY`). -/
noncomputable def FUNCTIONALITY.view (F : FUNCTIONALITY p f_in f_out) :
    DFUNCTIONALITY p f_in f_out :=
  DFUNCTIONALITY.mk p f_in f_out { f := FUNCTIONALITY.f p f_in f_out F }

/-- The distinguisher's view of a primitive (EasyCrypt's subtyping `PRIMITIVE <: DPRIMITIVE`). -/
noncomputable def PRIMITIVE.view (P : PRIMITIVE p f_in f_out) : DPRIMITIVE p f_in f_out :=
  DPRIMITIVE.mk p f_in f_out { f := PRIMITIVE.f p f_in f_out P, fi := PRIMITIVE.fi p f_in f_out P }

/-- The oracle procedures a `DISTINGUISHER` may call (EasyCrypt's `OI.allowed`): `F.f`, `P.f`,
`P.fi`.  The holes of its representation (`Module.Representable`, exception E2). -/
abbrev distHoles : HoleSigs :=
  .cons (procsig (f_in) -> f_out) (.cons (procsig (p) -> p) (.cons (procsig (p) -> p) .empty))

/-- `F.f`, `P.f`, `P.fi` out of the oracles `(F, P)`. -/
noncomputable def distExt (FP : DFUNCTIONALITY p f_in f_out ×ₘ DPRIMITIVE p f_in f_out) :
    (distHoles p f_in f_out).Instantiation :=
  ((DFUNCTIONALITY.f p f_in f_out (Module.fst FP)).procedure,
   (DPRIMITIVE.f p f_in f_out (Module.snd FP)).procedure,
   (DPRIMITIVE.fi p f_in f_out (Module.snd FP)).procedure)

/-- The oracle procedure a `SIMULATOR`'s `f` and `fi` may call (EasyCrypt's `{ F.f }`): `F.f`.  Its
`init` may call none (`{ }`). -/
abbrev simHoles : HoleSigs := .cons (procsig (f_in) -> f_out) .empty

/-- `F.f` out of the oracle `F`. -/
noncomputable def simExt (F : DFUNCTIONALITY p f_in f_out) : (simHoles f_in f_out).Instantiation :=
  (DFUNCTIONALITY.f p f_in f_out F).procedure

/-- `S` applied to an oracle `F` behaves, procedure by procedure, like `pinit`, and like `pf`, `pfi`
filled with `F.f`, and these touch nothing that `S` does not.  `Module.RepresentedBy` for a
simulator, whose result has three procedures (exception E2). -/
structure SIMULATOR.RepresentedBy (S : SIMULATOR p f_in f_out)
    (pinit : ProcedureWithHoles .empty (procsig () -> Unit))
    (pf pfi : ProcedureWithHoles (simHoles f_in f_out) (procsig (p) -> p)) : Prop where
  init : ∀ F a, procedureDenotation (PRIMITIVE.init p f_in f_out (Module.app S F)).procedure a =
    procedureDenotation (pinit.instantiate PUnit.unit) a
  f : ∀ F a, procedureDenotation (PRIMITIVE.f p f_in f_out (Module.app S F)).procedure a =
    procedureDenotation (pf.instantiate (simExt p f_in f_out F)) a
  fi : ∀ F a, procedureDenotation (PRIMITIVE.fi p f_in f_out (Module.app S F)).procedure a =
    procedureDenotation (pfi.instantiate (simExt p f_in f_out F)) a
  fvP_le : FVP.fvP_proc pinit ⊔ FVP.fvP_proc pf ⊔ FVP.fvP_proc pfi ≤ FVP.fvP S

/-- EasyCrypt's call restrictions of `SIMULATOR` for an abstract simulator `S` (exception E2). -/
def SIMULATOR.Representable (S : SIMULATOR p f_in f_out) : Prop :=
  ∃ pinit pf pfi, SIMULATOR.RepresentedBy p f_in f_out S pinit pf pfi

module Indif using (F : FUNCTIONALITY p f_in f_out, P : PRIMITIVE p f_in f_out,
    D : DISTINGUISHER p f_in f_out) {
  proc main () : Bool {
    var b : Bool;
    _ <- call P.init ();
    _ <- call F.init ();
    b <- call (Module.app D
      (Module.pair (DFUNCTIONALITY.mk p f_in f_out { f := FUNCTIONALITY.f p f_in f_out F })
        (DPRIMITIVE.mk p f_in f_out
          { f := PRIMITIVE.f p f_in f_out P, fi := PRIMITIVE.fi p f_in f_out P }))) ();
    return $b
  };
}

/-- `module GReal(C : CONSTRUCTION, P : PRIMITIVE) = Indif(C(P), P)`. -/
noncomputable def GReal (C : CONSTRUCTION p f_in f_out) (P : PRIMITIVE p f_in f_out)
    (D : DISTINGUISHER p f_in f_out) : procmod () → Bool :=
  Module.app (Indif p f_in f_out)
    (Module.pair (Module.app C (PRIMITIVE.view p f_in f_out P)) (Module.pair P D))

/-- `module GIdeal(F : FUNCTIONALITY, S : SIMULATOR) = Indif(F, S(F))`. -/
noncomputable def GIdeal (F : FUNCTIONALITY p f_in f_out) (S : SIMULATOR p f_in f_out)
    (D : DISTINGUISHER p f_in f_out) : procmod () → Bool :=
  Module.app (Indif p f_in f_out)
    (Module.pair F (Module.pair (Module.app S (FUNCTIONALITY.view p f_in f_out F)) D))

end GaudisCrypt.SHA3.Indifferentiability
