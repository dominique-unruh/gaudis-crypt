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
| `noflags m` | `FMap.noflags m` |
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

/-- The map binding each `x ∈ s` with `h x = some y` to `y` (how `restr` and `map` are built). -/
noncomputable def ofOpt (s : Finset α) (h : α → Option β) : FMap α β :=
  s.toList.foldl (fun acc x => match h x with
    | some y => acc.insert x y
    | none => acc) ∅

theorem lookup_foldl_ofOpt (h : α → Option β) (x : α) :
    ∀ (l : List α) (acc : FMap α β),
      (l.foldl (fun acc x => match h x with
        | some y => acc.insert x y
        | none => acc) acc).lookup x = if x ∈ l ∧ (h x).isSome then h x else acc.lookup x
  | [], acc => by simp
  | k :: l, acc => by
    rw [List.foldl_cons, lookup_foldl_ofOpt h x l]
    by_cases hk : k = x
    · subst hk
      cases hx : h k <;> simp
    · have : (match h k with | some y => acc.insert k y | none => acc).lookup x = acc.lookup x := by
        cases h k <;> simp [Finmap.lookup_insert_of_ne _ (Ne.symm hk)]
      rw [this]; simp [Ne.symm hk]

theorem get_ofOpt (s : Finset α) (h : α → Option β) (x : α) :
    get (ofOpt s h) x = if x ∈ s then h x else none := by
  unfold get ofOpt
  rw [lookup_foldl_ofOpt]
  by_cases hx : x ∈ s <;> cases hh : h x <;> simp [hx]

/-- `restr f m` (for `m : ('a, 'b * 'f) fmap`): the bindings of `m` whose tag is `f`, without
the tag. -/
noncomputable def restr {φ : Type*} [DecidableEq φ] (f : φ) (m : FMap α (β × φ)) : FMap α β :=
  ofOpt m.keys fun x => (m.lookup x).bind fun p => if p.2 = f then some p.1 else none

/-- `map f m`: `m` with each binding `x ↦ y` replaced by `x ↦ f x y`. -/
noncomputable def map {γ : Type*} (f : α → β → γ) (m : FMap α β) : FMap α γ :=
  ofOpt m.keys fun x => (m.lookup x).map (f x)

/-- `noflags m` (for `m : ('a, 'b * 'f) fmap`): `m` without its tags. -/
noncomputable def noflags {φ : Type*} (m : FMap α (β × φ)) : FMap α β := map (fun _ p => p.1) m

/-- `m1 + m2`: the bindings of both, `m2`'s winning where both bind a key. -/
def add (m1 m2 : FMap α β) : FMap α β := m2 ∪ m1

/-- `in_dom_with m x f`: `x` is bound in `m`, with tag `f`. -/
def in_dom_with {φ : Type*} [Inhabited β] [Inhabited φ] (m : FMap α (β × φ)) (x : α) (f : φ) :
    Prop :=
  dom m x ∧ ((get m x).getD default).2 = f

instance {φ : Type*} [Inhabited β] [Inhabited φ] [DecidableEq φ] (m : FMap α (β × φ)) (x : α)
    (f : φ) : Decidable (in_dom_with m x f) :=
  inferInstanceAs (Decidable (dom m x ∧ _))

/-! ## Lemmas (EasyCrypt's names) -/

/-- `domE`. -/
theorem domE (m : FMap α β) (x : α) : dom m x ↔ get m x ≠ none := by
  simp [dom, get, Finmap.lookup_eq_none, Finmap.mem_keys]

/-- `fmap_eqP`. -/
theorem fmap_eqP (m₁ m₂ : FMap α β) : (∀ x, get m₁ x = get m₂ x) ↔ m₁ = m₂ :=
  ⟨fun h => Finmap.ext_lookup h, fun h _ => h ▸ rfl⟩

/-- `emptyE`. -/
@[simp] theorem emptyE (x : α) : get (empty : FMap α β) x = none := by
  simp [get, empty]

omit [DecidableEq α] in
/-- `fdom0`. -/
@[simp] theorem fdom0 : fdom (empty : FMap α β) = ∅ := by simp [fdom, empty]

omit [DecidableEq α] in
/-- `mem_fdom`. -/
theorem mem_fdom (m : FMap α β) (x : α) : x ∈ fdom m ↔ dom m x := Iff.rfl

omit [DecidableEq α] in
/-- `mem_empty`. -/
theorem mem_empty (x : α) : ¬ dom (empty : FMap α β) x := by simp [dom, empty]

/-- `get_setE`. -/
theorem get_setE (m : FMap α β) (x y : α) (b : β) :
    get (set m x b) y = if y = x then some b else get m y := by
  by_cases h : y = x
  · subst h; simp [get, set]
  · simp [get, set, h, Finmap.lookup_insert_of_ne _ h]

/-- `get_set_sameE`. -/
@[simp] theorem get_set_sameE (m : FMap α β) (x : α) (b : β) : get (set m x b) x = some b := by
  simp [get_setE]

/-- `get_set_neqE`. -/
theorem get_set_neqE (m : FMap α β) (x y : α) (b : β) (h : y ≠ x) :
    get (set m x b) y = get m y := by
  simp [get_setE, h]

/-- `get_set_id`. -/
theorem get_set_id (m : FMap α β) (x : α) (y : β) (h : get m x = some y) : set m x y = m := by
  refine (fmap_eqP _ _).mp fun z => ?_
  rw [get_setE]; by_cases hz : z = x
  · subst hz; simp [h]
  · simp [hz]

/-- `mem_set`. -/
theorem mem_set (m : FMap α β) (x : α) (b : β) (y : α) : dom (set m x b) y ↔ dom m y ∨ y = x := by
  rw [domE, domE, get_setE]; by_cases h : y = x <;> simp [h]

/-- `remE`. -/
theorem remE (m : FMap α β) (x y : α) : get (rem m x) y = if y = x then none else get m y := by
  by_cases h : y = x
  · subst h; simp [get, rem]
  · simp [get, rem, h, Finmap.lookup_erase_ne h]

/-- `rem_id`. -/
theorem rem_id (m : FMap α β) (x : α) (h : ¬ dom m x) : rem m x = m := by
  refine (fmap_eqP _ _).mp fun y => ?_
  rw [remE]; by_cases hy : y = x
  · subst hy; simpa [domE, eq_comm] using h
  · simp [hy]

/-- `mapE`. -/
theorem mapE {γ : Type*} (f : α → β → γ) (m : FMap α β) (x : α) :
    get (map f m) x = (get m x).map (f x) := by
  unfold map; rw [get_ofOpt]
  by_cases hx : x ∈ m.keys
  · simp [hx, get]
  · simp [hx, get, Finmap.lookup_eq_none.mpr (by simpa [Finmap.mem_keys] using hx)]

/-- `mem_map`. -/
theorem mem_map {γ : Type*} (f : α → β → γ) (m : FMap α β) (x : α) :
    dom (map f m) x ↔ dom m x := by
  simp [domE, mapE]

/-- `map_set`. -/
theorem map_set {γ : Type*} (f : α → β → γ) (m : FMap α β) (x : α) (b : β) :
    map f (set m x b) = set (map f m) x (f x b) := by
  refine (fmap_eqP _ _).mp fun y => ?_
  rw [mapE, get_setE, get_setE, mapE]; by_cases h : y = x
  · subst h; simp
  · simp [h]

/-- `map_comp`. -/
theorem map_comp {γ δ : Type*} (f : α → β → γ) (g : α → γ → δ) (m : FMap α β) :
    map g (map f m) = map (fun a b => g a (f a b)) m := by
  refine (fmap_eqP _ _).mp fun y => ?_
  simp only [mapE, Option.map_map]; rfl

/-- `map_id`. -/
theorem map_id (m : FMap α β) : map (fun _ b => b) m = m := by
  refine (fmap_eqP _ _).mp fun y => ?_
  simp [mapE]

/-- `map_empty`. -/
theorem map_empty {γ : Type*} (f : α → β → γ) : map f (empty : FMap α β) = empty := by
  refine (fmap_eqP _ _).mp fun y => ?_
  simp [mapE]

/-- `map_rem`. -/
theorem map_rem {γ : Type*} (f : α → β → γ) (m : FMap α β) (x : α) :
    map f (rem m x) = rem (map f m) x := by
  refine (fmap_eqP _ _).mp fun y => ?_
  rw [mapE, remE, remE, mapE]; by_cases h : y = x <;> simp [h]

section restr
variable {φ : Type*} [DecidableEq φ]

/-- `restrP`. -/
theorem restrP (m : FMap α (β × φ)) (f : φ) (x : α) :
    get (restr f m) x = (get m x).bind fun p => if p.2 = f then some p.1 else none := by
  unfold restr; rw [get_ofOpt]
  by_cases hx : x ∈ m.keys
  · simp [hx, get]
  · simp [hx, get, Finmap.lookup_eq_none.mpr (by simpa [Finmap.mem_keys] using hx)]

/-- `dom_restr`. -/
theorem dom_restr [Inhabited β] [Inhabited φ] (m : FMap α (β × φ)) (f : φ) (x : α) :
    dom (restr f m) x ↔ in_dom_with m x f := by
  rw [in_dom_with, domE, domE, restrP]
  cases get m x with
  | none => simp
  | some p => by_cases h : p.2 = f <;> simp [h]

/-- `in_dom_with` after a write. -/
theorem in_dom_with_set [Inhabited β] [Inhabited φ] (m : FMap α (β × φ)) (x z : α) (v : β × φ)
    (f : φ) : in_dom_with (set m x v) z f ↔ if z = x then v.2 = f else in_dom_with m z f := by
  unfold in_dom_with
  rw [mem_set, get_setE]
  by_cases h : z = x <;> simp [h]

/-- `restr_set`. -/
theorem restr_set (m : FMap α (β × φ)) (f1 f2 : φ) (x : α) (y : β) :
    restr f1 (set m x (y, f2)) = if f1 = f2 then set (restr f1 m) x y else rem (restr f1 m) x := by
  refine (fmap_eqP _ _).mp fun z => ?_
  by_cases hf : f1 = f2
  · subst hf; rw [if_pos rfl, restrP, get_setE, get_setE, restrP]
    by_cases h : z = x <;> simp [h]
  · rw [if_neg hf, restrP, get_setE, remE, restrP]
    by_cases h : z = x <;> simp [h, Ne.symm hf]

/-- `restr_set_eq`. -/
theorem restr_set_eq (m : FMap α (β × φ)) (f : φ) (x : α) (y : β) :
    restr f (set m x (y, f)) = set (restr f m) x y := by
  rw [restr_set, if_pos rfl]

/-- `restr0`. -/
theorem restr0 (f : φ) : restr f (empty : FMap α (β × φ)) = empty := by
  refine (fmap_eqP _ _).mp fun z => ?_
  simp [restrP]

/-- `restr_rem`. -/
theorem restr_rem [Inhabited β] [Inhabited φ] (m : FMap α (β × φ)) (x : α) (f : φ) :
    restr f (rem m x) = if in_dom_with m x f then rem (restr f m) x else restr f m := by
  split_ifs with h
  · refine (fmap_eqP _ _).mp fun z => ?_
    rw [restrP, remE, remE, restrP]; by_cases hz : z = x <;> simp [hz]
  · rw [← rem_id (restr f m) x (by rwa [dom_restr])]
    refine (fmap_eqP _ _).mp fun z => ?_
    rw [restrP, remE, remE, restrP]; by_cases hz : z = x <;> simp [hz]

end restr

end FMap

end GaudisCrypt.EC
