import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Submonoid.Centralizer
import PlonkLean.Misc

/-- A read-only projection. Forgetting the setter of a `Lens` gives a `Getter`. -/
@[ext]
structure Getter (a : Type u) (b : Type v) where
  get : b -> a

structure Lens (a : Type u) (b : Type v) extends Getter a b where
  set : a -> b -> b
  set_get : ∀ s x, get (set x s) = x
  set_set : ∀ s x y, set y (set x s) = set y s
  get_set : ∀ s, set (get s) s = s

open Classical in
noncomputable def Lens.get_from_set {a m : Type*} [ne : Nonempty a] (set : a → m → m) : m → a :=
  fun mem ↦
    if h : ∃ x : a, set x mem = mem
    then choose h else choice ne

def Lens.get_from_set_correct [Nonempty a] (lens : Lens a m) :
    Lens.get_from_set lens.set = lens.get := by
  funext mem
  simp only [Lens.get_from_set]
  have hex : ∃ x : a, lens.set x mem = mem := ⟨lens.get mem, lens.get_set mem⟩
  rw [dif_pos hex]
  have h1 := Classical.choose_spec hex
  have h2 := lens.set_get mem (Classical.choose hex)
  rw [h1] at h2
  exact h2.symm

@[ext]
theorem Lens.ext (l r : Lens a m) (h : (∀ x y, l.set x y = r.set x y)) : l = r := by
  have hset : l.set = r.set := funext₂ h
  have hget : l.get = r.get := by
    funext s
    have h1 : r.set (l.get s) s = s := hset ▸ l.get_set s
    have h2 := r.set_get s (l.get s)
    rw [h1] at h2
    exact h2.symm
  cases l; cases r; simp_all [Getter.ext_iff]

/-- Lenses `x` and `y` are disjoint, i.e., refer to different parts of the memory -/
class disjoint (x : Lens a m) (y : Lens b m) where
  commute : ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s)

theorem disjoint.iff : disjoint x y ↔ ∀ s v w, x.set v (y.set w s) = y.set w (x.set v s) :=
  ⟨fun h => h.commute, fun h => ⟨h⟩⟩

def pair (x : Lens a m) (y : Lens b m) [disj : disjoint x y] : Lens (a × b) m :=
  { get := fun s => (x.get s, y.get s)
    set := fun (u,v) s => x.set u (y.set v s)
    set_get := by
      simp [x.set_get]
      simp [disj.commute, y.set_get]
    set_set := by
     simp [disj.commute, y.set_set, x.set_set]
    get_set := by
      simp [y.get_set, x.get_set] }

def chain {a b c} (x : Lens b c) (y : Lens a b) : Lens a c := {
  get s := y.get (x.get s)
  set a s := x.set (y.set a (x.get s)) s
  set_get := by simp [x.set_get, y.set_get]
  set_set := by simp [x.set_get, y.set_set, x.set_set]
  get_set := by simp [x.get_set, y.get_set]
}

def fst : Lens a (a×b) := {
  get := fun (x,y) => x
  set := fun x' (x,y) => (x',y)
  set_get := by simp
  set_set := by simp
  get_set := by simp
}

def snd : Lens b (a×b) := {
  get := fun (x,y) => y
  set := fun y' (x,y) => (x,y')
  set_get := by simp
  set_set := by simp
  get_set := by simp
}

theorem pair_fst (x : Lens a m) (y : Lens b m) [disj : disjoint x y] :
  chain (pair x y) fst = x := by
    simp [chain, pair, fst, y.get_set]

theorem pair_snd (x : Lens a m) (y : Lens b m) [disj : disjoint x y] :
  chain (@pair _ _ _ x y disj) snd = y :=
    by simp [chain, pair, snd, disj.commute, x.get_set]

instance disjoint3 [xy : disjoint x y] [xz : disjoint x z] [yz : disjoint y z] :
  disjoint x (pair y z) :=
  by
    simp only [pair, disjoint.iff]
    intros
    simp [xy.commute, xz.commute]

instance disjoint3' [xy : disjoint x y] [xz : disjoint x z] [yz : disjoint y z] :
    disjoint (pair x y) z := by
  simp only [pair, disjoint.iff]
  intros
  simp [yz.commute, xz.commute]

def Lens.bijection (e : a ≃ b) : Lens a b where
  get := e.symm
  set x _ := e x
  set_get _ x := e.symm_apply_apply x
  set_set _ _ _ := rfl
  get_set s := e.apply_symm_apply s

structure LensIn.{u,v} (m : Type u) : Type _ where
  content : Type v
  lens : Lens content m

def LensIn.mk' (lens : Lens a m) : LensIn m := ⟨a, lens⟩

def IsoLens (lens : Lens a b) := Function.Bijective lens.get

instance : Preorder (LensIn m) where
  le x y := exists z : Lens x.content y.content, chain y.lens z = x.lens
  le_refl := fun x => by
    refine ⟨⟨⟨id⟩, fun a _ => a, fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩, ?_⟩
    obtain ⟨_, _, _, _, _⟩ := x.lens
    rfl
  le_trans := fun x y z hxy hyz => by
    obtain ⟨f, hf_chain⟩ := hxy
    obtain ⟨g, hg_chain⟩ := hyz
    refine ⟨chain g f, ?_⟩
    have assoc : chain z.lens (chain g f) = chain (chain z.lens g) f := by
      obtain ⟨_, _, _, _, _⟩ := f
      obtain ⟨_, _, _, _, _⟩ := g
      obtain ⟨_, _, _, _, _⟩ := z.lens
      rfl
    rw [assoc, hg_chain, hf_chain]

abbrev bit := ZMod 2


def Lens.update (lens : Lens a m) (f : a → a) : m → m := fun x => lens.set (f (lens.get x)) x


/-- `s ~ s'` iff they differ only in the part the lens controls:
    `∃ a, lens.set a s = s'`. -/
def Lens.equal_outside (lens : Lens a m) (s s' : m) : Prop :=
  ∃ x, lens.set x s = s'

/-- The relation `equal_outside` is an equivalence.
- refl:  `set (get s) s = s`  (by `get_set`)
- symm:  `set x s = s'`  →  `set (get s) s' = set (get s) (set x s) = set (get s) s = s`
         (first step by `set_set`, second by `get_set`)
- trans: `set x s = s'`, `set y s' = s''`  →  `set y s = set y (set x s) = s''`  (by `set_set`) -/
def Lens.equal_outside_setoid (lens : Lens a m) : Setoid m where
  r := lens.equal_outside
  iseqv := {
    refl  := fun s =>
      ⟨lens.get s, lens.get_set s⟩
    symm  := fun {s s'} ⟨x, hx⟩ =>
      ⟨lens.get s, by rw [← hx, lens.set_set, lens.get_set]⟩
    trans := fun {s _ s''} ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨y, by rw [← hy, ← hx, lens.set_set]⟩
  }

def Lens.compl (lens : Lens a m) : Lens (Quotient lens.equal_outside_setoid) m where
  get mem := Quotient.mk'' mem
  set a mem := Quotient.lift (lens.set (lens.get mem))
    (fun _ _ h => by obtain ⟨x, hx⟩ := h; rw [← hx, lens.set_set]) a
  get_set s := by simp [lens.get_set]
  set_get s a := by
    induction a using Quotient.inductionOn
    rename_i v
    exact Quotient.sound ⟨lens.get v, (lens.set_set v _ _).trans (lens.get_set v)⟩
  set_set s a b := by
    induction a using Quotient.inductionOn
    rename_i v
    simp [lens.set_get]

theorem Lens.empty_eq [IsEmpty m] (lens1 : Lens a m) (lens2 : Lens a m) : lens1 = lens2 := by
  ext x m; exact of_decide_eq_true rfl

def Lens.id : Lens m m where
  get m := m
  set a _ := a
  set_set _ _ _ := rfl
  get_set _ := rfl
  set_get _ _ := rfl



lemma lens_leq_content_leq [Nonempty m] (lens1 : LensIn m) (lens2 : LensIn m)
    (h : lens1 ≤ lens2) : Cardinal.mk lens1.content ≤ Cardinal.mk lens2.content := by
  obtain ⟨z, _⟩ := h
  let s₀ : lens2.content := lens2.lens.get (Classical.choice inferInstance)
  exact Cardinal.mk_le_of_injective (f := fun x => z.set x s₀) fun x₁ x₂ heq => by
    simpa [z.set_get] using congr_arg z.get heq

lemma get_surjective [Nonempty m] (lens : Lens a m) : Function.Surjective lens.get :=
  fun x => ⟨lens.set x (Classical.choice inferInstance), lens.set_get _ _⟩

lemma get_injective_iso_lens [Nonempty m] (lens : Lens a m) (_ : Function.Injective lens.get) :
    IsoLens lens :=
  ⟨‹_›, get_surjective lens⟩

lemma iso_lens_ge (lens1 : Lens a m) (lens2 : Lens b m) (_ : IsoLens z)
    (_ : chain lens2 z = lens1) :
    LensIn.mk' lens1 ≥ LensIn.mk' lens2 := by
  refine ⟨Lens.bijection (Equiv.ofBijective z.get ‹_›), ?_⟩
  apply Lens.ext; intro v s
  simp only [chain, Lens.bijection, Equiv.ofBijective_apply]
  change lens1.set (z.get v) s = lens2.set v s
  have hset : lens2.set (z.set (z.get v) (lens2.get s)) s = lens1.set (z.get v) s := by
    have h := congr_fun₂ (congr_arg Lens.set ‹chain lens2 z = lens1›) (z.get v) s
    simpa [chain] using h
  rw [← hset]; congr 1
  exact ‹IsoLens z›.1 (by simp [z.set_get])

lemma lens_lt_content_lt [Nonempty m] (lens1 : LensIn m) (lens2 : LensIn m)
    [Fintype lens1.content] [Fintype lens2.content] (lt : lens1 < lens2) :
    Fintype.card lens1.content < Fintype.card lens2.content := by
  have hle : lens1 ≤ lens2 := lt.1
  have hnge : ¬ lens2 ≤ lens1 := lt.2
  by_contra hlt; push Not at hlt
  apply hnge
  obtain ⟨z, hchain⟩ := hle
  have s₀ : lens2.content := lens2.lens.get (Classical.choice inferInstance)
  have f_inj : Function.Injective (fun x => z.set x s₀) := fun x₁ x₂ h => by
    simpa [z.set_get] using congr_arg z.get h
  have heq : Fintype.card lens1.content = Fintype.card lens2.content :=
    Nat.le_antisymm (Fintype.card_le_of_injective _ f_inj) hlt
  have f_surj : Function.Surjective (fun x => z.set x s₀) :=
    f_inj.surjective_of_finite (Fintype.equivOfCardEq heq)
  haveI : Nonempty lens2.content := ⟨s₀⟩
  have hinj : Function.Injective z.get := fun y₁ y₂ hy => by
    obtain ⟨a₁, rfl⟩ := f_surj y₁; obtain ⟨a₂, rfl⟩ := f_surj y₂
    simp only [z.set_get] at hy; rw [hy]
  exact iso_lens_ge lens1.lens lens2.lens (get_injective_iso_lens z hinj) hchain

lemma lens_content_div_mem [Fintype a] [Fintype m] (lens : Lens a m) :
    Fintype.card a ∣ Fintype.card m := by
  classical
  let T := Quotient lens.equal_outside_setoid
  haveI : Fintype T := Fintype.ofSurjective
    (Quotient.mk'' (s₁ := lens.equal_outside_setoid))
    (fun q => Quotient.inductionOn q fun s => ⟨s, rfl⟩)
  let e : m ≃ a × T :=
    { toFun := fun s => (lens.get s, Quotient.mk'' s)
      invFun := fun ⟨x, q⟩ => q.liftOn (lens.set x)
        fun r₁ r₂ ⟨v, hv⟩ => by rw [← hv, lens.set_set]
      left_inv := fun s => by simp [lens.get_set]
      right_inv := fun ⟨x, q⟩ => by
        induction q using Quotient.inductionOn
        simp only [Quotient.liftOn_mk]
        exact Prod.ext (lens.set_get _ _)
          (Quotient.sound ⟨lens.get _, by rw [lens.set_set, lens.get_set]⟩) }
  rw [Fintype.card_congr e, Fintype.card_prod]
  exact dvd_mul_right _ _

lemma lens_le_content_div (lens1 : LensIn m) (lens2 : LensIn m)
    [Fintype lens1.content] [Fintype lens2.content] (hle : lens1 ≤ lens2) :
    Fintype.card lens1.content ∣ Fintype.card lens2.content := by
  obtain ⟨w, _⟩ := hle
  exact lens_content_div_mem w