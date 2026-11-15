import GaudisCrypt.Lib.EC.Logic

/-!
# EasyCrypt's `Bigop` (`theories/algebra/Bigop.eca`)

The big operator of a commutative monoid over a list: `big P F r` is the monoid's sum of `F x`
over the `x` of `r` that satisfy `P`.  The theory's type `t` with EC's `Monoid` cloned as
`Support` (`idm`, `+`, `addmA`, `addmC`, `add0m`) is the class `Params t`; a clone gives the
monoid (`clone import GaudisCrypt.EC.Bigop as BBS with type t <- word, op idm <- zerow,
op add <- xorw`).  Only what ported developments use is here.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC.Bigop

/-- The theory's parameters: a commutative monoid on `t` (EC's `clone export Monoid as
Support`). -/
class Params (t : outParam Type) where
  /-- `Support.idm`: the neutral element. -/
  idm : t
  /-- `Support.(+)`: the monoid's operation. -/
  add : t → t → t
  /-- `axiom addmA : associative (+)`. -/
  addmA : ∀ x y z : t, add x (add y z) = add (add x y) z
  /-- `axiom addmC : commutative (+)`. -/
  addmC : ∀ x y : t, add x y = add y x
  /-- `axiom add0m : left_id idm (+)`. -/
  add0m : ∀ x : t, add idm x = x

export Params (idm addmA addmC add0m)

variable {t : Type} [Params t]

/-- `lemma addm0 : right_id idm (+)`. -/
theorem addm0 (x : t) : Params.add x idm = x := by rw [addmC, add0m]

/-- `op big (P : 'a -> bool) (F : 'a -> t) (r : 'a list) =
foldr Support.(+) idm (map F (filter P r))`. -/
def big {α : Type} (P : α → Prop) [DecidablePred P] (F : α → t) (r : List α) : t :=
  List.foldr Params.add idm (List.map F (List.filter (fun x => decide (P x)) r))

/-- `lemma big_nil`. -/
theorem big_nil {α : Type} (P : α → Prop) [DecidablePred P] (F : α → t) : big P F [] = idm := rfl

/-- `lemma big_cons`. -/
theorem big_cons {α : Type} (P : α → Prop) [DecidablePred P] (F : α → t) (x : α) (s : List α) :
    big P F (x :: s) = if P x then Params.add (F x) (big P F s) else big P F s := by
  unfold big
  by_cases h : P x <;> simp [h]

/-- `lemma big_consT`. -/
theorem big_consT {α : Type} (F : α → t) (x : α) (s : List α) :
    big predT F (x :: s) = Params.add (F x) (big predT F s) := by
  rw [big_cons, if_pos (predT_apply x)]

/-- `lemma big_cat`. -/
theorem big_cat {α : Type} (P : α → Prop) [DecidablePred P] (F : α → t) (s1 s2 : List α) :
    big P F (s1 ++ s2) = Params.add (big P F s1) (big P F s2) := by
  induction s1 with
  | nil => rw [List.nil_append, big_nil, add0m]
  | cons x s ih =>
    rw [List.cons_append, big_cons, big_cons, ih]
    by_cases h : P x
    · rw [if_pos h, if_pos h, addmA]
    · rw [if_neg h, if_neg h]

end GaudisCrypt.EC.Bigop
