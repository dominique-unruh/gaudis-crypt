/-!
# EasyCrypt's `Logic` (`theories/prelude/Logic.ec`): predicates

Only what ported developments use is here.  Names are EasyCrypt's.
-/

namespace GaudisCrypt.EC

/-- `op pred1 ['a] (c x : 'a) = x = c`: the predicate "equal to `c`". -/
def pred1 {α : Type} (c : α) : α → Prop := fun x => x = c

/-- `lemma pred1E (c x : 'a) : pred1 c x <=> x = c`. -/
theorem pred1E {α : Type} (c x : α) : pred1 c x ↔ x = c := Iff.rfl

end GaudisCrypt.EC
