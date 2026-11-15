import GaudisCrypt.Lib.EC.Distr

/-!
# Cyclic groups of prime order (EasyCrypt `theories/algebra/Group.ec`)

What a development gets by

    clone CyclicGroup as G.
    axiom prime_p : IntDiv.prime G.order.
    clone G.PowZMod as GP with lemma prime_order <- prime_p.
    clone GP.FDistr as FD.

a cyclic group `group` with generator `g`, its exponents `exp` (the field `Z/pZ` of `PowZMod`),
exponentiation `x ^ k`, the discrete logarithm `loge`, and the uniform distribution `dt` on the
exponents (`FDistr`).  Only what ported developments use is here.  Names are EasyCrypt's.

The operations of the group and of the field are Mathlib's (`CommGroup group`, `Field exp`):
EC's `e`, `*`, `inv`, `/` are `1`, `*`, `⁻¹`, `/`; the lemmas of EC's `ZModpField` on `exp` are
those of a field (`ring`).  The class `Params group exp` holds what Mathlib does not: the
generator, the exponentiation by a field element, the logarithm and their laws.  Its types are
`outParam`s, as for every theory: inside a development that clones it nothing is written.
-/

namespace GaudisCrypt.EC.CyclicGroup

/-- EC's `op g`, `op ( ^ ) : group -> exp -> group`, `op loge` and their laws (`expD`, `expM`,
`expgK`, `loggK` of `PowZMod`). -/
class Params (group exp : outParam Type) [CommGroup group] [Field exp] where
  g : group
  pow : group → exp → group
  loge : group → exp
  expD : ∀ (x : group) (a b : exp), pow x (a + b) = pow x a * pow x b
  expM : ∀ (x : group) (a b : exp), pow x (a * b) = pow (pow x a) b
  expgK : ∀ x : group, pow g (loge x) = x
  loggK : ∀ k : exp, loge (pow g k) = k

export Params (g loge)

variable {group exp : Type} [CommGroup group] [Field exp] [Params group exp]

/-- EC's types are inhabited (`witness`): `group` by its unit. -/
instance (priority := low) : Inhabited group := ⟨1⟩

/-- `exp` is inhabited, by its zero. -/
instance (priority := low) : Inhabited exp := ⟨0⟩

/-- EC's `x ^ k` for an exponent `k : exp`. -/
instance : HPow group exp group := ⟨Params.pow⟩

/-- `lemma expD (x : group) (a b : exp) : x ^ (a + b) = x ^ a * x ^ b`. -/
theorem expD (x : group) (a b : exp) : x ^ (a + b) = x ^ a * x ^ b := Params.expD x a b

/-- `lemma expM (x : group) (a b : exp) : x ^ (a * b) = x ^ a ^ b`. -/
theorem expM (x : group) (a b : exp) : x ^ (a * b) = (x ^ a) ^ b := Params.expM x a b

/-- `lemma expgK x : g ^ (loge x) = x`. -/
theorem expgK (x : group) : (g : group) ^ (loge x : exp) = x := Params.expgK x

/-- `lemma loggK (k : exp) : loge (g ^ k) = k`. -/
theorem loggK (k : exp) : loge ((g : group) ^ k) = k := Params.loggK k

/-! ## `FDistr` -/

variable [Fintype exp]

/-- EC's `op dt : exp distr = dunifin`: the uniform distribution on the exponents (an
abbreviation: EC's provers see through an operator's body, and so do the closers here). -/
noncomputable abbrev dt : SubProbability exp := SubProbability.uniform

omit [CommGroup group] [Params group exp] in
/-- `lemma dt_ll : is_lossless dt`. -/
theorem dt_ll : is_lossless (dt : SubProbability exp) := uniform_ll

omit [CommGroup group] [Params group exp] in
/-- `lemma dt_fu : is_full dt`. -/
theorem dt_fu : is_full (dt : SubProbability exp) := uniform_fu

omit [CommGroup group] [Params group exp] in
/-- `lemma dt_funi : is_funiform dt`. -/
theorem dt_funi : is_funiform (dt : SubProbability exp) := uniform_funi

end GaudisCrypt.EC.CyclicGroup
