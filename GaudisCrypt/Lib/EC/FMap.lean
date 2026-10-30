import Mathlib.Data.Finmap

/-!
# EasyCrypt's finite maps (`theories/datatypes/FMap.ec`)

`('a, 'b) fmap` is a finite map, here Mathlib's `Finmap`.  Only what ported developments use is
here.  Names are EasyCrypt's, with function names for its mixfix operators:

| EasyCrypt | here |
|---|---|
| `empty` | `FMap.empty` |
| `m.[x]` | `FMap.get m x` |
| `m.[x <- y]` | `FMap.set m x y` |
| `x \in m` (`dom m x`) | `FMap.dom m x` |
| `rng m y` | `FMap.rng m y` |
| `fdom m`, `frng m` | `FMap.fdom m`, `FMap.frng m` |
-/

namespace GaudisCrypt.EC

/-- `('a, 'b) fmap`. -/
abbrev FMap (α β : Type*) := Finmap fun _ : α => β

namespace FMap

variable {α β : Type*} [DecidableEq α]

/-- `empty`: the map with no bindings. -/
def empty : FMap α β := ∅

/-- `m.[x]`. -/
def get (m : FMap α β) (x : α) : Option β := m.lookup x

/-- `m.[x <- y]`. -/
def set (m : FMap α β) (x : α) (y : β) : FMap α β := m.insert x y

/-- `rem m x`: `m` without a binding for `x`. -/
def rem (m : FMap α β) (x : α) : FMap α β := m.erase x

/-- `x \in m`: `x` is bound in `m`. -/
def dom (m : FMap α β) (x : α) : Prop := x ∈ m.keys

instance (m : FMap α β) : DecidablePred (dom m) := fun x =>
  inferInstanceAs (Decidable (x ∈ m.keys))

/-- `rng m y`: some key is bound to `y`. -/
def rng (m : FMap α β) (y : β) : Prop := ∃ x, m.lookup x = some y

/-- `fdom m`: the keys of `m`. -/
def fdom (m : FMap α β) : Finset α := m.keys

/-- `frng m`: the values of `m`. -/
def frng [DecidableEq β] (m : FMap α β) : Finset β :=
  (m.entries.map Sigma.snd).toFinset

end FMap

end GaudisCrypt.EC
