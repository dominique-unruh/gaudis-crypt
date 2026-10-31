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
| `restr f m` | `FMap.restr f m` |
| `find p m` | `FMap.find p m` |
| `map f m` | `FMap.map f m` |
| `m1 + m2` | `FMap.add m1 m2` |
| `in_dom_with m x f` | `FMap.in_dom_with m x f` |
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

open Classical in
noncomputable instance (m : FMap α β) : DecidablePred (rng m) := fun _ => Classical.dec _

/-- `fdom m`: the keys of `m`. -/
def fdom (m : FMap α β) : Finset α := m.keys

/-- `frng m`: the values of `m`. -/
def frng [DecidableEq β] (m : FMap α β) : Finset β :=
  (m.entries.map Sigma.snd).toFinset

open Classical in
/-- `find p m`: some key `x` bound to `y` with `p x y` (EasyCrypt leaves which one unspecified),
`None` if there is none. -/
noncomputable def find (p : α → β → Bool) (m : FMap α β) : Option α :=
  if h : ∃ x y, m.lookup x = some y ∧ p x y = true then some h.choose else none

/-- `restr f m` (for `m : ('a, 'b * 'f) fmap`): the bindings of `m` whose tag is `f`, without
the tag. -/
noncomputable def restr {φ : Type*} [DecidableEq φ] (f : φ) (m : FMap α (β × φ)) : FMap α β :=
  m.keys.toList.foldl (fun acc x => match m.lookup x with
    | some (y, f') => if f' = f then acc.insert x y else acc
    | none => acc) ∅

/-- `map f m`: `m` with each binding `x ↦ y` replaced by `x ↦ f x y`. -/
noncomputable def map {γ : Type*} (f : α → β → γ) (m : FMap α β) : FMap α γ :=
  m.keys.toList.foldl (fun acc x => match m.lookup x with
    | some y => acc.insert x (f x y)
    | none => acc) ∅

/-- `m1 + m2`: the bindings of both, `m2`'s winning where both bind a key. -/
def add (m1 m2 : FMap α β) : FMap α β := m2 ∪ m1

/-- `in_dom_with m x f`: `x` is bound in `m`, with tag `f`. -/
def in_dom_with {φ : Type*} [Inhabited β] [Inhabited φ] (m : FMap α (β × φ)) (x : α) (f : φ) :
    Prop :=
  dom m x ∧ ((get m x).getD default).2 = f

instance {φ : Type*} [Inhabited β] [Inhabited φ] [DecidableEq φ] (m : FMap α (β × φ)) (x : α)
    (f : φ) : Decidable (in_dom_with m x f) :=
  inferInstanceAs (Decidable (dom m x ∧ _))

end FMap

end GaudisCrypt.EC
