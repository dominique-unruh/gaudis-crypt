import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.ExpectationCall
import GaudisCrypt.Logic.EqualOutside

/-!
# Random oracles with failing queries are preimage, second-preimage and collision resistant
(EasyCrypt `proof/SecureORO.eca`)

`SecureRO` for oracles returning `option`s: `Bounder` answers `None` once its `bound` queries are
spent, and the games compare `Some` hashes.

Translation notes (see `notes/SHA3/README.md` and `SecureRO.lean`, whose translation this follows):
* EasyCrypt's module type `RF` and module `RF` share a name; the module type is `RF_T`
  (exception E3).
* `RF(R)` (`proc init = R.init`, `proc sample = R.sample`) and `Bounder(F)` (`proc sample =
  F.sample`) are used as functors, so their aliased procedures call the aliased ones (exception E5).
* The module variables (`Bounder.bounder`, the clone's `RO.m`, `FRO.m`, and the sections' local
  `Preimage2.hash`, `SecondPreimage2.m2`, `D1.m1`) are lens parameters (exception E6 for the local
  ones).
* The proofs are `SecureRO`'s, step for step; the potentials of EC's `fel` and the lemmas on them
  are `SecureRO`'s (their counter component `0`: there is no `Counter` here).
-/

-- the clone `RO` contains the module `RO` (`RO.RO`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.SecureORO

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM

variable («from» «to» : Type) [DecidableEq «from»] [Inhabited «from»] [Inhabited «to»]
variable (sampleto : SubProbability «to»)

/-! `clone import PROM.FullRO as RO with type in_t <- from, type out_t <- to,
op dout _ <- sampleto, type d_in_t <- unit, type d_out_t <- bool`; its module variable `RO.m` is
the lens parameter `RO_m`. -/

-- one binder each: a `module` takes a whole binder group when it mentions one of its names
variable (RO_m : Lens (FMap «from» «to») VariableAssignment)

namespace RO
/-- EasyCrypt's module type `RO` of the clone. -/
abbrev RO_T := PROM.FullRO.RO_T «from» «to»
noncomputable abbrev RO := PROM.FullRO.RO.asRO «from» «to» (fun _ => sampleto) RO_m
noncomputable abbrev LRO := PROM.FullRO.LRO «from» «to» (fun _ => sampleto) RO_m
end RO

/-! The footprints of the theory's modules (EasyCrypt reads them off the code; `fp_disjoint` uses
them). -/

@[fp_bound] theorem fvP_RO :
    FVP.fvP (RO.RO «from» «to» sampleto RO_m) ≤ RO_m.footprint := by
  fp_module RO_m

@[fp_bound] theorem fvP_LRO :
    FVP.fvP (RO.LRO «from» «to» sampleto RO_m) ≤ RO_m.footprint := by
  fp_module RO_m

/-- The oracle procedure an adversary with an `Oracle` may call: `F.get` (E2). -/
abbrev Oracle.holes : HoleSigs := .cons (procsig («from») -> (Option «to»)) .empty

/-! ### The section `Collision`, with `declare module A <: AdvCollision {-RO, -FRO, -Bounder}` (its
local modules in the namespace `Collision`) -/

/-- The section's `op collision (m : ('a, 'b) fmap)`: two distinct keys with the same value. -/
def collision {α β : Type} [DecidableEq α] (m : FMap α β) : Prop :=
  ∃ m1 m2, m1 ≠ m2 ∧ FMap.dom m m1 ∧ FMap.dom m m2 ∧ FMap.get m m1 = FMap.get m m2

end GaudisCrypt.SHA3.SecureORO
