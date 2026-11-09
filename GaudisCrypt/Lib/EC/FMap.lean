import Mathlib.Data.Finmap
import GaudisCrypt.Lib.EC.List

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

/-- `eq_except X m1 m2`: `m1` and `m2` agree outside `X` (EC's `eq_exceptP` is the definition). -/
def eq_except (X : α → Prop) (m1 m2 : FMap α β) : Prop := ∀ y, ¬ X y → get m1 y = get m2 y

/-! ## Lemmas (EasyCrypt's names) -/

/-- `domE`. -/
theorem domE (m : FMap α β) (x : α) : dom m x ↔ get m x ≠ none := by
  simp [dom, get, Finmap.lookup_eq_none, Finmap.mem_keys]

/-- `get_some`: `x \in m => m.[x] = Some (oget m.[x])`. -/
theorem get_some [Inhabited β] (m : FMap α β) (x : α) (h : dom m x) :
    get m x = some (oget (get m x)) := by
  rw [domE] at h
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp h
  rw [hy]; rfl

/-- `rngE`. -/
theorem rngE (m : FMap α β) (y : β) : rng m y ↔ ∃ x, get m x = some y := Iff.rfl

/-- `mem_frng`. -/
theorem mem_frng [DecidableEq β] (m : FMap α β) (y : β) : y ∈ frng m ↔ rng m y := by
  simp only [frng, Multiset.mem_toFinset, Multiset.mem_map, rng]
  constructor
  · rintro ⟨⟨x, b⟩, hs, rfl⟩
    exact ⟨x, Finmap.mem_lookup_iff.mpr hs⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, y⟩, Finmap.mem_lookup_iff.mp hx, rfl⟩


/-- `findP`, with bindings `get m x = some y` for EasyCrypt's `x \in m` and `oget m.[x]`: either
`find` fails and no binding satisfies `p`, or it returns a key whose binding satisfies `p`. -/
theorem findP (p : α → β → Bool) (m : FMap α β) :
    (find p m = none ∧ ∀ x y, get m x = some y → p x y = false) ∨
    (∃ x y, find p m = some x ∧ get m x = some y ∧ p x y = true) := by
  unfold find
  split_ifs with h
  · right
    obtain ⟨y, hy, hp⟩ := h.choose_spec
    exact ⟨_, y, rfl, hy, hp⟩
  · left
    refine ⟨rfl, fun x y hy => ?_⟩
    simpa using fun hp => h ⟨x, y, hy, hp⟩

/-- `fmap_eqP`. -/
theorem fmap_eqP (m₁ m₂ : FMap α β) : (∀ x, get m₁ x = get m₂ x) ↔ m₁ = m₂ :=
  ⟨fun h => Finmap.ext_lookup h, fun h _ => h ▸ rfl⟩

/-- `emptyE`. -/
@[simp] theorem emptyE (x : α) : get (empty : FMap α β) x = none := by
  simp [get, empty]

omit [DecidableEq α] in
/-- `frng0`: the empty map's range is empty. -/
@[simp] theorem frng0 [DecidableEq β] : frng (empty : FMap α β) = ∅ := by
  simp [frng, empty]; rfl

omit [DecidableEq α] in
/-- `fdom0`. -/
@[simp] theorem fdom0 : fdom (empty : FMap α β) = ∅ := by simp [fdom, empty]

omit [DecidableEq α] in
/-- `mem_fdom`. -/
theorem mem_fdom (m : FMap α β) (x : α) : x ∈ fdom m ↔ dom m x := Iff.rfl

/-- `leq_card_rng_dom`: a map has at most as many values as keys. -/
theorem leq_card_rng_dom [DecidableEq β] [Inhabited β] (m : FMap α β) :
    (frng m).card ≤ (fdom m).card := by
  classical
  refine (Finset.card_le_card fun y hy => ?_).trans (Finset.card_image_le (s := fdom m)
    (f := fun k => (get m k).getD default))
  obtain ⟨k, hk⟩ := (mem_frng m y).mp hy
  refine Finset.mem_image.mpr ⟨k, (mem_fdom _ _).mpr ((domE _ _).mpr (by
    rw [show get m k = some y from hk]; simp)), ?_⟩
  simp [show get m k = some y from hk]

/-- `endo_dom_rng`: a map from a type to itself that misses a key misses a value. -/
theorem endo_dom_rng [Inhabited α] (m : FMap α α) (h : ∃ x, ¬ dom m x) : ∃ y, ¬ rng m y := by
  classical
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨x, hx⟩ := h
  letI : Fintype α := ⟨frng m, fun y => (mem_frng m y).mpr (hall y)⟩
  have h1 : Finset.univ ⊆ frng m := fun y _ => (mem_frng m y).mpr (hall y)
  have h2 : fdom m ⊂ Finset.univ := (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr
    ⟨x, Finset.mem_univ x, fun h => hx ((mem_fdom m x).mp h)⟩
  have := (Finset.card_le_card h1).trans (leq_card_rng_dom m)
  exact absurd this (not_le.mpr (Finset.card_lt_card h2))

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

/-- `set_setE`. -/
theorem set_setE (m : FMap α β) (x y : α) (b c : β) :
    set (set m x b) y c = if x = y then set m y c else set (set m y c) x b := by
  refine (fmap_eqP _ _).mp fun z => ?_
  split_ifs with h
  · subst h; simp only [get_setE]; split_ifs <;> rfl
  · simp only [get_setE]
    split_ifs with h1 h2 <;> first | rfl | (subst h1; subst h2; exact absurd rfl h)

/-- `fdom_set`. -/
theorem fdom_set (m : FMap α β) (x : α) (b : β) : fdom (set m x b) = insert x (fdom m) := by
  ext z; simp [fdom, set, Finmap.mem_keys]

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

/-- `eq_except_setlr`-style: writing the same key on both sides keeps `eq_except`. -/
theorem eq_except_set (X : α → Prop) {m1 m2 : FMap α β} (h : eq_except X m1 m2) (x : α)
    (b c : β) (hbc : ¬ X x → b = c) : eq_except X (set m1 x b) (set m2 x c) := by
  intro y hy
  rw [get_setE, get_setE]
  split_ifs with hyx
  · subst hyx; rw [hbc hy]
  · exact h y hy

/-- `eq_except_setl`: a write inside `X` on the left keeps `eq_except`. -/
theorem eq_except_setl (X : α → Prop) {m1 m2 : FMap α β} (h : eq_except X m1 m2) (x : α)
    (hx : X x) (b : β) : eq_except X (set m1 x b) m2 := by
  intro y hy
  rw [get_setE, if_neg (fun (e : y = x) => hy (e ▸ hx))]
  exact h y hy

/-- `eq_except_setr`: a write inside `X` on the right keeps `eq_except`. -/
theorem eq_except_setr (X : α → Prop) {m1 m2 : FMap α β} (h : eq_except X m1 m2) (x : α)
    (hx : X x) (b : β) : eq_except X m1 (set m2 x b) := by
  intro y hy
  rw [get_setE, if_neg (fun (e : y = x) => hy (e ▸ hx))]
  exact h y hy

/-- `eq_except_remr`: a removal inside `X` on the right keeps `eq_except`. -/
theorem eq_except_remr (X : α → Prop) {m1 m2 : FMap α β} (h : eq_except X m1 m2) (x : α)
    (hx : X x) : eq_except X m1 (rem m2 x) := by
  intro y hy
  rw [remE, if_neg (fun (e : y = x) => hy (e ▸ hx))]
  exact h y hy

/-- Equal outside `x`, and unbound at `x` on the right: the left without `x` is the right. -/
theorem rem_eq_of_eq_except {m1 m2 : FMap α β} {x : α} (h : eq_except (· = x) m1 m2)
    (h2 : get m2 x = none) : rem m1 x = m2 := by
  refine (fmap_eqP _ _).mp fun z => ?_
  rw [remE]
  split_ifs with hz
  · subst hz; exact h2.symm
  · exact h z hz

/-- Equal outside `x`, and bound to `b` at `x` on the right: the left with `x ↦ b` is the right. -/
theorem set_eq_of_eq_except {m1 m2 : FMap α β} {x : α} {b : β} (h : eq_except (· = x) m1 m2)
    (h2 : get m2 x = some b) : set m1 x b = m2 := by
  refine (fmap_eqP _ _).mp fun z => ?_
  rw [get_setE]
  split_ifs with hz
  · subst hz; exact h2.symm
  · exact h z hz

/-- `eq_except_refl`. -/
theorem eq_except_refl (X : α → Prop) (m : FMap α β) : eq_except X m m := fun _ _ => rfl

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

/-- `in_dom_with` reads only the binding. -/
theorem in_dom_with_congr [Inhabited β] [Inhabited φ] {m1 m2 : FMap α (β × φ)} {z : α}
    (h : get m1 z = get m2 z) (f : φ) : in_dom_with m1 z f ↔ in_dom_with m2 z f := by
  unfold in_dom_with; rw [domE, domE, h]

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

/-- `restrP` at a map tagging every binding with `f`: the bindings themselves. -/
theorem restr_map_tag (m : FMap α β) (f : φ) : restr f (map (fun _ c => (c, f)) m) = m := by
  refine (fmap_eqP _ _).mp fun z => ?_
  rw [restrP, mapE]; cases get m z <;> simp

/-- A map tagging every binding with `f` has no binding tagged `f' ≠ f`. -/
theorem restr_map_tag_ne (m : FMap α β) {f f' : φ} (h : f' ≠ f) :
    restr f' (map (fun _ c => (c, f)) m) = empty := by
  refine (fmap_eqP _ _).mp fun z => ?_
  rw [restrP, mapE, emptyE]; cases get m z <;> simp [Ne.symm h]

end restr

/-- EC's `map_comp`/`map_id` at `noflags`: tagging every binding, then dropping the tags. -/
theorem noflags_map_tag {φ : Type*} (m : FMap α β) (f : φ) :
    noflags (map (fun _ c => (c, f)) m) = m := by
  rw [noflags, map_comp]; exact map_id m

/-! ### Facts EC's `smt()` finds on `rng`, `fdom` and fresh bindings

Not in EC's `FMap.ec`: the facts its proofs leave to `smt()` (with `mem_set`, `get_setE`, `remE`,
`fcardUI_indep`).  `collision` is `SecureRO`'s `op collision`, generic as there. -/

/-- A binding of a fresh key keeps the range. -/
theorem rng_set_of_rng {m : FMap α β} {x : α} (hx : ¬ dom m x) {h : β} (hr : rng m h) (a : β) :
    rng (set m x a) h := by
  obtain ⟨k, hk⟩ := hr
  have hkx : k ≠ x := by
    rintro rfl
    exact hx (Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hk))
  exact ⟨k, by simp only [set, Finmap.lookup_insert_of_ne _ hkx, hk]⟩

/-- A value new in the range of `m.[x <- a]` is `a`. -/
theorem eq_of_rng_set {m : FMap α β} {x : α} {h a : β} (hr : ¬ rng m h)
    (hs : rng (set m x a) h) : a = h := by
  obtain ⟨k, hk⟩ := hs
  by_cases hkx : k = x
  · subst hkx
    simpa [set] using hk
  · exact absurd ⟨k, by simpa [set, Finmap.lookup_insert_of_ne _ hkx] using hk⟩ hr

/-- `empty` has an empty range. -/
theorem rng_empty (h : β) : ¬ rng (empty : FMap α β) h := by
  rintro ⟨k, hk⟩
  simp [empty] at hk

/-- A binding of a fresh key keeps the range of the map without `m1`. -/
theorem rng_rem_set_of_rng {m : FMap α β} {x m1 : α} (hx : ¬ dom m x) {v : β}
    (hr : rng (rem m m1) v) (a : β) : rng (rem (set m x a) m1) v := by
  obtain ⟨k, hk⟩ := hr
  have hk1 : k ≠ m1 := by rintro rfl; simp [rem] at hk
  have hk' : m.lookup k = some v := by simpa [rem, Finmap.lookup_erase_ne hk1] using hk
  have hkx : k ≠ x := by
    rintro rfl
    exact hx (Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hk'))
  exact ⟨k, by simp [rem, set, Finmap.lookup_erase_ne hk1, Finmap.lookup_insert_of_ne _ hkx, hk']⟩

/-- A value new in the range of `rem m.[x <- a] m1` is `a`. -/
theorem eq_of_rng_rem_set {m : FMap α β} {x m1 : α} {v a : β}
    (hr : ¬ rng (rem m m1) v) (hs : rng (rem (set m x a) m1) v) : a = v := by
  obtain ⟨k, hk⟩ := hs
  have hk1 : k ≠ m1 := by rintro rfl; simp [rem] at hk
  by_cases hkx : k = x
  · subst hkx
    simpa [rem, set, Finmap.lookup_erase_ne hk1] using hk
  · exact absurd ⟨k, by simpa [rem, set, Finmap.lookup_erase_ne hk1,
      Finmap.lookup_insert_of_ne _ hkx] using hk⟩ hr

/-- `fcardUI_indep` at a fresh key: `card (fdom m.[x <- r]) = card (fdom m) + 1`. -/
theorem fcard_set {m : FMap α β} {x : α} (hx : ¬ dom m x) (r : β) :
    (fdom (set m x r)).card = (fdom m).card + 1 := by
  rw [fdom_set]
  exact Finset.card_insert_of_notMem hx

/-- `SecureRO`'s `op collision (m : ('a, 'b) fmap)`: two distinct keys with the same value. -/
def collision (m : FMap α β) : Prop :=
  ∃ m1 m2, m1 ≠ m2 ∧ dom m m1 ∧ dom m m2 ∧ get m m1 = get m m2

/-- A binding of a fresh key keeps a collision. -/
theorem collision_set {m : FMap α β} {x : α} (hx : ¬ dom m x) (hc : collision m) (r : β) :
    collision (set m x r) := by
  obtain ⟨k₁, k₂, hne, hd₁, hd₂, heq⟩ := hc
  have h₁ : k₁ ≠ x := fun h => hx (h ▸ hd₁)
  have h₂ : k₂ ≠ x := fun h => hx (h ▸ hd₂)
  refine ⟨k₁, k₂, hne, (mem_set _ _ _ _).mpr (Or.inl hd₁), (mem_set _ _ _ _).mpr (Or.inl hd₂), ?_⟩
  rw [get_set_neqE _ _ _ _ h₁, get_set_neqE _ _ _ _ h₂]
  exact heq

/-- A collision new in `m.[x <- r]`, `x` fresh: `r` is already a value of `m`. -/
theorem rng_of_collision_set {m : FMap α β} {x : α} (hx : ¬ dom m x) (hc : ¬ collision m) {r : β}
    (hcs : collision (set m x r)) : ∃ k, dom m k ∧ get m k = some r := by
  obtain ⟨k₁, k₂, hne, hd₁, hd₂, heq⟩ := hcs
  rw [mem_set] at hd₁ hd₂
  rw [get_setE, get_setE] at heq
  by_cases h₁ : k₁ = x
  · subst h₁
    have h₂ : k₂ ≠ k₁ := fun h => hne h.symm
    simp only [if_neg h₂] at heq
    exact ⟨k₂, hd₂.resolve_right h₂, heq.symm⟩
  by_cases h₂ : k₂ = x
  · subst h₂
    simp only [if_neg h₁] at heq
    exact ⟨k₁, hd₁.resolve_right h₁, heq⟩
  · simp only [if_neg h₁, if_neg h₂] at heq
    exact absurd ⟨k₁, k₂, hne, hd₁.resolve_right h₁, hd₂.resolve_right h₂, heq⟩ hc

/-- `empty` has no collision. -/
theorem collision_empty : ¬ collision (empty : FMap α β) := by
  rintro ⟨k₁, -, -, hd, -⟩
  simp [dom, empty] at hd

end FMap

end GaudisCrypt.EC
