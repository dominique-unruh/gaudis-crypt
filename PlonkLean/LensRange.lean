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
  Set.image lens.complement.update ⊤ = (Submonoid.centralizer (Set.image lens.update ⊤)).carrier := by
  rw [centralizer_carrier_eq]
  apply Set.Subset.antisymm
  · -- LHS ⊆ RHS: every complement update commutes with every lens update
    rintro h ⟨g, -, rfl⟩
    simp only [Set.mem_centralizer_iff]
    rintro _ ⟨f, -, rfl⟩
    -- lens.update f does not change the outside equivalence class
    have key : ∀ x, lens.complement.get (lens.update f x) = lens.complement.get x :=
      fun x => Quotient.sound ⟨lens.get x, by rw [Lens.update, lens.set_set, lens.get_set]⟩
    funext x
    show lens.update f (lens.complement.update g x) = lens.complement.update g (lens.update f x)
    have key' : Quotient.mk'' (lens.set (f (lens.get x)) x) = Quotient.mk'' x := key x
    simp only [Lens.update, Lens.complement]
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

def LensRange.complement (range : LensRange m) : LensRange m where
  updates := (Submonoid.centralizer range.updates).carrier
  id := sorry
  comp := sorry
  double_commutant := sorry

private theorem double_complement (lens : Lens a m) :
  let iso_lens := sorry
  lens.complement.complement = chain lens iso_lens ∧ IsoLens iso_lens
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
    - double_commutant of updates = Set.image lens.complement.complement.update ⊤   BY: complement_range
    - ... = Set.image (chain lens iso_lens).update ⊤  BY: double_complement
    - ... = Set.image lens.update ⊤    BY: the fact that iso_lens is IsoLens
    - ... = updates
  -/

theorem LensRange.complement_range (lens : Lens a m) :
  lens.complement.range = lens.range.complement := sorry

def LensRange.from (generators : Set (m → m)) : LensRange m where
  updates := Submonoid.centralizer (Submonoid.centralizer generators).carrier
  id := Submonoid.one_mem _
  comp := fun hf hg => Submonoid.mul_mem _ hf hg
  double_commutant := by
    simp only [centralizer_carrier_eq]
    exact Set.centralizer_centralizer_centralizer _

instance : PartialOrder (LensRange m) where
  le x y := x.updates ≤ y.updates
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

instance : Lattice (LensRange m) where
  sup x y := LensRange.from (x.updates ∪ x.updates) -- double commutant of union
  inf x y := ⟨x.updates ∩ y.updates, sorry, sorry, sorry⟩  -- intersection
  le_sup_left := sorry
  le_sup_right := sorry
  le_inf := sorry
  sup_le := sorry
  inf_le_left := sorry
  inf_le_right := sorry

instance : BoundedOrder (LensRange m) where
  top := ⟨⊤, sorry, sorry, sorry⟩
  bot := ⟨⊥, sorry, sorry, sorry⟩
  bot_le := sorry
  le_top := sorry

instance : CompleteSemilatticeSup (LensRange m) where
  sSup s := sorry -- LensRange.from (union of all .updates in s)   -- double commutant of union
  isLUB_sSup := sorry

instance : CompleteSemilatticeInf (LensRange m) where
  sInf := sorry -- double commutant of intersection
  isGLB_sInf := sorry

instance : CompleteLattice (LensRange m) where


theorem Lens.range_defines_preorder (x : Lens a m) (y : Lens b m) :
  x.range ≤ y.range ↔ LensIn.mk' x ≤ LensIn.mk' y := sorry
