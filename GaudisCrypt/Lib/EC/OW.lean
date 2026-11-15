import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.Distr
import GaudisCrypt.Lib.EC.IsUniform

/-!
# One-way trapdoor permutations (EasyCrypt `theories/crypto/OW.ec`)

The theory's types `D`, `R`, `pkey`, `skey` are `outParam`s of the class `Params`; its
operators (`dkeys`, `challenge`, `f`, `finv`) and axioms are the class's fields: a clone is
`clone import GaudisCrypt.EC.OW as OW_rand with type D <- …, op dkeys <- … proof * by …`.
-/

-- EasyCrypt names the experiment after the theory (`OW.OW`); kept (exception E1)
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt.EC.OW

open GaudisCrypt GaudisCrypt.EC

/-- EC's `pred valid_keys (ks:pkey * skey) = support dkeys ks`. -/
def valid_keys' {pkey skey : Type} (dkeys : SubProbability (pkey × skey))
    (ks : pkey × skey) : Prop := ks ∈ dkeys.support

/-- EC's `pred valid_pkey (pk:pkey) = exists sk, valid_keys (pk,sk)`. -/
def valid_pkey' {pkey skey : Type} (dkeys : SubProbability (pkey × skey)) (pk : pkey) : Prop :=
  ∃ sk, valid_keys' dkeys (pk, sk)

/-- EC's `pred f_dom (pk:pkey) (x:D) = valid_pkey pk => x \in (challenge pk)`. -/
def f_dom' {D pkey skey : Type} (dkeys : SubProbability (pkey × skey))
    (challenge : pkey → SubProbability D) (pk : pkey) (x : D) : Prop :=
  valid_pkey' dkeys pk → x ∈ (challenge pk).support

/-- EC's `pred f_rng (pk:pkey) (y:R) = valid_pkey pk => exists x, f_dom pk x /\ y = f pk x`. -/
def f_rng' {D R pkey skey : Type} (dkeys : SubProbability (pkey × skey))
    (challenge : pkey → SubProbability D) (f : pkey → D → R) (pk : pkey) (y : R) : Prop :=
  valid_pkey' dkeys pk → ∃ x, f_dom' dkeys challenge pk x ∧ y = f pk x

/-- EC's abstract declarations of the theory: the domain and range `D`, `R`, the keys, the
distribution of the keys and of the challenge, the permutation `f` and its inverse `finv`, and
the axioms `dkeys_ll`, `challenge_ll`, `challenge_uni`, `finv_correct`, `finvof`, `fofinv`. -/
class Params (D R pkey skey : outParam Type) where
  dkeys : SubProbability (pkey × skey)
  dkeys_ll : is_lossless dkeys
  challenge : pkey → SubProbability D
  challenge_ll : ∀ pk, valid_pkey' dkeys pk → is_lossless (challenge pk)
  challenge_uni : ∀ pk, valid_pkey' dkeys pk → is_uniform (challenge pk)
  f : pkey → D → R
  finv : skey → R → D
  finv_correct : ∀ (pk : pkey) (sk : skey) (y : R), valid_keys' dkeys (pk, sk) →
    f_rng' dkeys challenge f pk y → f_dom' dkeys challenge pk (finv sk y)
  finvof : ∀ (pk : pkey) (sk : skey) (x : D), valid_keys' dkeys (pk, sk) →
    f_dom' dkeys challenge pk x → finv sk (f pk x) = x
  fofinv : ∀ (pk : pkey) (sk : skey) (x : R), valid_keys' dkeys (pk, sk) →
    f_rng' dkeys challenge f pk x → f pk (finv sk x) = x

export Params (dkeys dkeys_ll challenge challenge_ll challenge_uni f finv finv_correct finvof
  fofinv)

variable {D R pkey skey : Type} [Inhabited D] [Inhabited R] [Inhabited pkey] [Inhabited skey]
  [Params D R pkey skey]

/-- EC's `pred valid_keys`. -/
abbrev valid_keys (ks : pkey × skey) : Prop := valid_keys' dkeys ks

/-- EC's `pred valid_pkey`. -/
abbrev valid_pkey (pk : pkey) : Prop := valid_pkey' (skey := skey) dkeys pk

/-- EC's `pred f_dom`. -/
abbrev f_dom (pk : pkey) (x : D) : Prop := f_dom' (skey := skey) dkeys challenge pk x

/-- EC's `pred f_rng`. -/
abbrev f_rng (pk : pkey) (y : R) : Prop := f_rng' (skey := skey) dkeys challenge f pk y

/-- This is often useful to extract plaintexts: EC's `lemma f_pk_inj`. -/
theorem f_pk_inj (x y : D) (pk : pkey) (sk : skey) :
    valid_keys (pk, sk) → f_dom pk x → f_dom pk y → f pk x = f pk y → x = y := by
  -- EC: by move=> Hsupp Hdom_x Hdom_y Heqf;
  --        rewrite -(finvof pk sk) // -(finvof pk sk y) // Heqf.
  intro Hsupp Hdom_x Hdom_y Heqf
  rw [← finvof pk sk x Hsupp Hdom_x, ← finvof pk sk y Hsupp Hdom_y, Heqf]

/-! We can now define the module types and modules that define security -/

variable [DecidableEq D]

moduletype Inverter {
  proc invert (pk : pkey, y : R) -> D;
}

module OW using (I : Inverter) {
  proc main () : Bool {
    var x : D, x' : D, pk : pkey, sk : skey;
    pk, sk <$ dkeys;
    x <$ challenge $pk;
    x' <- call I.invert ($pk, f $pk $x);
    return decide ($x = $x')
  };
}

end GaudisCrypt.EC.OW
