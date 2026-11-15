/-!
# EasyCrypt's `Logic` (`theories/prelude/Logic.ec`): predicates

Only what ported developments use is here.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

/-- `op pred1 ['a] (c x : 'a) = x = c`: the predicate "equal to `c`". -/
def pred1 {α : Type} (c : α) : α → Prop := fun x => x = c

/-- `lemma pred1E (c x : 'a) : pred1 c x <=> x = c`. -/
theorem pred1E {α : Type} (c x : α) : pred1 c x ↔ x = c := Iff.rfl

/-- `op predC ['a] (p : 'a -> bool) = fun x => !(p x)`: the complement of a test (a `Bool`
function, as the guards of programs are; the complement of `pred1 c` is `predC1 c`). -/
def predC {α : Type} (p : α → Bool) : α → Prop := fun x => p x = false

/-- `lemma predCE`: `predC p x <=> !(p x)`. -/
theorem predCE {α : Type} (p : α → Bool) (x : α) : predC p x ↔ p x = false := Iff.rfl

/-- `op predC1 ['a] (c x : 'a) = x <> c`. -/
def predC1 {α : Type} (c : α) : α → Prop := fun x => x ≠ c

end GaudisCrypt.EC
