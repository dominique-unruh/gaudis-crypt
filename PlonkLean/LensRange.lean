import PlonkLean.Lens

instance : Monoid (m → m) where
  mul := (· ∘ ·)
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

structure LensRange (m : Type _) where
  updates : Set (m → m)
  id : id ∈ updates
  comp : f ∈ updates → g ∈ updates → (f ∘ g) ∈ updates
  double_commutant : (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates

private lemma centralizer_carrier_eq (S : Set (m → m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

private theorem complement_range (lens : Lens a m) :
  Set.image lens.compl.update ⊤ = (Submonoid.centralizer (Set.image lens.update ⊤)).carrier := by
  rw [centralizer_carrier_eq]
  apply Set.Subset.antisymm
  · -- LHS ⊆ RHS: every complement update commutes with every lens update
    rintro h ⟨g, -, rfl⟩
    simp only [Set.mem_centralizer_iff]
    rintro _ ⟨f, -, rfl⟩
    -- lens.update f does not change the outside equivalence class
    have key : ∀ x, lens.compl.get (lens.update f x) = lens.compl.get x :=
      fun x => Quotient.sound ⟨lens.get x, by rw [Lens.update, lens.set_set, lens.get_set]⟩
    funext x
    show lens.update f (lens.compl.update g x) = lens.compl.update g (lens.update f x)
    have key' : Quotient.mk'' (lens.set (f (lens.get x)) x) = Quotient.mk'' x := key x
    simp only [Lens.update, Lens.compl]
    rw [key']
    refine Quotient.inductionOn (g (Quotient.mk'' x)) fun v => ?_
    simp [lens.set_get, lens.set_set]
  · -- RHS ⊆ LHS: every centralizer element is a complement update
    intro h hcomm
    simp only [Set.mem_centralizer_iff] at hcomm
    -- h preserves lens.get (use commutativity with lens.update (fun _ => lens.get x))
    have hget : ∀ x, lens.get (h x) = lens.get x := fun x => by
      have h1 := congr_fun (hcomm (lens.update (fun _ => lens.get x))
        ⟨fun _ => lens.get x, Set.mem_univ _, rfl⟩) x
      simp only [HMul.hMul, Mul.mul, Function.comp, Lens.update, lens.get_set] at h1
      rw [← h1, lens.set_get]
    -- h maps equal_outside-related inputs to equal_outside-related outputs
    have hwelldef : ∀ x y, lens.equal_outside_setoid.r x y →
        lens.equal_outside_setoid.r (h x) (h y) := fun x y ⟨a, ha⟩ => by
      have h1 := congr_fun (hcomm (lens.update (fun _ => a)) ⟨fun _ => a, Set.mem_univ _, rfl⟩) x
      simp only [HMul.hMul, Mul.mul, Function.comp, Lens.update] at h1
      rw [ha] at h1
      exact ⟨a, h1⟩
    -- define g : Quotient → Quotient by g [x] = [h x]
    let g := Quotient.lift (Quotient.mk'' ∘ h) fun _ _ hr => Quotient.sound (hwelldef _ _ hr)
    refine ⟨g, Set.mem_univ _, ?_⟩
    -- h equals the complement update induced by g (uses hget: h x = lens.set (lens.get x) (h x))
    funext x
    change lens.set (lens.get x) (h x) = h x
    rw [← hget x]
    exact lens.get_set (h x)

instance : Compl (LensRange m) where
  compl range := ⟨(Submonoid.centralizer range.updates).carrier,
    Submonoid.one_mem _,
    fun hf hg => Submonoid.mul_mem _ hf hg,
    by simp only [centralizer_carrier_eq]; exact Set.centralizer_centralizer_centralizer _⟩

private noncomputable def double_complement_iso_lens [Nonempty m] (lens : Lens a m) : Lens (Quotient lens.compl.equal_outside_setoid) a where
  get v :=
    let m0 : m := Classical.choice inferInstance
    Quotient.mk'' (lens.set v m0)
  set x _ := Quotient.lift lens.get (fun a b hab => by
      obtain ⟨q, hq⟩ := hab
      induction q using Quotient.inductionOn with
      | h v => simp only [Lens.compl, Quotient.lift_mk] at hq; rw [← hq]; simp [lens.set_get]) x
  get_set s := by
    change lens.get (lens.set s (Classical.choice inferInstance)) = s
    exact lens.set_get _ _
  set_get s x := by
    induction x using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      exact ⟨Quotient.mk'' v, by simp [Lens.compl, Quotient.lift_mk, lens.set_get, lens.get_set]⟩
  set_set _ _ _ := rfl

private theorem double_complement_iso_lens_iso [Nonempty m] (lens : Lens a m) :
  IsoLens (double_complement_iso_lens lens) := sorry

private theorem double_complement [Nonempty m] (lens : Lens a m) :
  lens.compl.compl = chain lens (double_complement_iso_lens lens)
  := sorry

def Lens.range (lens : Lens a m) : LensRange m where
  updates := Set.image lens.update ⊤
  id := ⟨id, Set.mem_univ _, funext fun x => lens.get_set x⟩
  comp := fun hf hg => by
    obtain ⟨h, -, rfl⟩ := hf
    obtain ⟨k, -, rfl⟩ := hg
    exact ⟨h ∘ k, Set.mem_univ _, funext fun x => by
      simp [Lens.update, lens.set_get, lens.set_set]⟩
  double_commutant := sorry /- Proof sketch:
    First, a case distinction whether Nonempty m or Empty m. For empty m, the theorem is trivial.
    For nonempty m:

    - double_commutant of updates = Set.image lens.complement.complement.update ⊤   BY: complement_range
    - ... = Set.image (chain lens iso_lens).update ⊤  BY: double_complement
    - ... = Set.image lens.update ⊤    BY: the fact that iso_lens is IsoLens
    - ... = updates
  -/

theorem LensRange.complement_range (lens : Lens a m) :
  lens.compl.range = lens.rangeᶜ := sorry

def LensRange.from (generators : Set (m → m)) : LensRange m where
  updates := Submonoid.centralizer (Submonoid.centralizer generators).carrier
  id := Submonoid.one_mem _
  comp := fun hf hg => Submonoid.mul_mem _ hf hg
  double_commutant := by
    simp only [centralizer_carrier_eq]
    exact Set.centralizer_centralizer_centralizer _

instance : PartialOrder (LensRange m) where
  le x y := x.updates ≤ y.updates
  le_refl x := le_refl x.updates
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  le_antisymm := by
    intro x y hxy hyx
    obtain ⟨xu, xid, xcomp, xdc⟩ := x
    obtain ⟨yu, yid, ycomp, ydc⟩ := y
    simp only at hxy hyx
    obtain rfl := le_antisymm hxy hyx
    rfl

instance : Lattice (LensRange m) where
  sup x y := LensRange.from (x.updates ∪ y.updates) -- double commutant of union
  inf x y := ⟨x.updates ∩ y.updates, ⟨x.id, y.id⟩,
    fun hf hg => ⟨x.comp hf.1 hg.1, y.comp hf.2 hg.2⟩, by
      simp only [centralizer_carrier_eq]
      apply Set.Subset.antisymm
      · apply Set.subset_inter
        · have hx := x.double_commutant
          simp only [centralizer_carrier_eq] at hx
          conv_rhs => rw [← hx]
          exact Set.centralizer_subset (Set.centralizer_subset Set.inter_subset_left)
        · have hy := y.double_commutant
          simp only [centralizer_carrier_eq] at hy
          conv_rhs => rw [← hy]
          exact Set.centralizer_subset (Set.centralizer_subset Set.inter_subset_right)
      · exact Set.subset_centralizer_centralizer⟩  -- intersection
  le_sup_left := fun x y => by
    change x.updates ⊆
      (Submonoid.centralizer (Submonoid.centralizer (x.updates ∪ y.updates)).carrier).carrier
    conv_lhs => rw [← x.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le Set.subset_union_left)
  le_sup_right := fun x y => by
    change y.updates ⊆
      (Submonoid.centralizer (Submonoid.centralizer (x.updates ∪ y.updates)).carrier).carrier
    conv_lhs => rw [← y.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le Set.subset_union_right)
  le_inf := fun _ _ _ h1 h2 => Set.subset_inter h1 h2
  sup_le := fun x y z hxz hyz => by
    change (Submonoid.centralizer (Submonoid.centralizer (x.updates ∪ y.updates)).carrier).carrier ⊆
      z.updates
    conv_rhs => rw [← z.double_commutant]
    exact Submonoid.centralizer_le
      (Submonoid.centralizer_le (Set.union_subset hxz hyz))
  inf_le_left := fun _ _ => Set.inter_subset_left
  inf_le_right := fun _ _ => Set.inter_subset_right

instance : BoundedOrder (LensRange m) where
  top := ⟨⊤, Set.mem_univ _, fun _ _ => Set.mem_univ _, by
    simp only [centralizer_carrier_eq, Set.top_eq_univ, Set.centralizer_univ]
    exact Set.centralizer_eq_top_iff_subset.mpr (Set.Subset.refl _)⟩
  bot := LensRange.from ∅
  bot_le := fun x => by
    change (Submonoid.centralizer (Submonoid.centralizer ∅).carrier).carrier ⊆ x.updates
    conv_rhs => rw [← x.double_commutant]
    exact Submonoid.centralizer_le (Submonoid.centralizer_le (Set.empty_subset _))
  le_top := fun x => Set.subset_univ _

theorem LensRange.disjoint_iff (x : LensRange m) (y : LensRange m) :
  Disjoint x y ↔ ∀ u∈x.updates, ∀ v∈y.updates, u ∘ v = v ∘ u :=
  sorry

theorem LensRange.compl_is_compl (x : LensRange a) : IsCompl x (xᶜ) := sorry

theorem LensRange.compl_compl (x : LensRange a) : xᶜᶜ = x := sorry

instance : CompleteSemilatticeSup (LensRange m) where
  sSup s := LensRange.from (⋃ x ∈ s, x.updates)
  isLUB_sSup s := by
    constructor
    · intro a ha
      change a.updates ⊆
        (Submonoid.centralizer (Submonoid.centralizer (⋃ x ∈ s, x.updates)).carrier).carrier
      conv_lhs => rw [← a.double_commutant]
      exact Submonoid.centralizer_le
        (Submonoid.centralizer_le (Set.subset_iUnion₂_of_subset a ha (le_refl _)))
    · intro b hb
      change (Submonoid.centralizer (Submonoid.centralizer (⋃ x ∈ s, x.updates)).carrier).carrier ⊆
        b.updates
      conv_rhs => rw [← b.double_commutant]
      exact Submonoid.centralizer_le
        (Submonoid.centralizer_le (Set.iUnion₂_subset (fun x hx => hb hx)))

instance : CompleteSemilatticeInf (LensRange m) where
  sInf s := ⟨⋂ x ∈ s, x.updates,
    Set.mem_iInter₂.mpr fun x hx => x.id,
    fun hf hg => Set.mem_iInter₂.mpr fun x hx =>
      x.comp (Set.mem_iInter₂.mp hf x hx) (Set.mem_iInter₂.mp hg x hx),
    by
      simp only [centralizer_carrier_eq]
      apply Set.Subset.antisymm
      · apply Set.subset_iInter₂
        intro x hx
        have hx_dc := x.double_commutant
        simp only [centralizer_carrier_eq] at hx_dc
        conv_rhs => rw [← hx_dc]
        exact Set.centralizer_subset (Set.centralizer_subset (Set.iInter₂_subset x hx))
      · exact Set.subset_centralizer_centralizer⟩
  isGLB_sInf s := by
    constructor
    · intro a ha; exact Set.iInter₂_subset a ha
    · intro b hb; exact Set.subset_iInter₂ (fun x hx => hb hx)

instance : CompleteLattice (LensRange m) where

instance : ComplementedLattice (LensRange m) where
  exists_isCompl x := by use xᶜ; apply LensRange.compl_is_compl

theorem Lens.range_defines_preorder (x : Lens a m) (y : Lens b m) :
  x.range ≤ y.range ↔ LensIn.mk' x ≤ LensIn.mk' y := sorry
