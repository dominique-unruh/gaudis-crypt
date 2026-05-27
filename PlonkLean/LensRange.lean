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
    IsoLens (double_complement_iso_lens lens) := by
  constructor
  · intro v1 v2 h
    have hrel := Quotient.exact h
    obtain ⟨q, hq⟩ := hrel
    induction q using Quotient.inductionOn with
    | h u =>
      simp only [Lens.compl, Quotient.lift_mk] at hq
      have key := congr_arg lens.get hq
      simp only [lens.set_get] at key
      exact key
  · intro q
    induction q using Quotient.inductionOn with
    | h s =>
      exact ⟨lens.get s, Quotient.sound ⟨Quotient.mk'' s,
        by simp [Lens.compl, Quotient.lift_mk, lens.set_get, lens.get_set]⟩⟩

private theorem double_complement [Nonempty m] (lens : Lens a m) :
    lens.compl.compl = chain lens (double_complement_iso_lens lens) := by
  ext
  rename_i q s
  induction q using Quotient.inductionOn with
  | h t => simp [Lens.compl, chain, double_complement_iso_lens, Quotient.lift_mk]

def Lens.range (lens : Lens a m) : LensRange m where
  updates := Set.image lens.update ⊤
  id := ⟨_root_.id, Set.mem_univ _, funext fun x => lens.get_set x⟩
  comp := fun hf hg => by
    obtain ⟨h, -, rfl⟩ := hf
    obtain ⟨k, -, rfl⟩ := hg
    exact ⟨h ∘ k, Set.mem_univ _, funext fun x => by
      simp [Lens.update, lens.set_get, lens.set_set]⟩
  double_commutant := by
    simp only [centralizer_carrier_eq]
    by_cases hm : Nonempty m
    · haveI := hm
      have hiso := double_complement_iso_lens_iso lens
      have h1 : Set.centralizer (Set.image lens.update ⊤) = Set.image lens.compl.update ⊤ := by
        rw [← centralizer_carrier_eq]; exact (complement_range lens).symm
      have h2 : Set.centralizer (Set.image lens.compl.update ⊤) =
          Set.image lens.compl.compl.update ⊤ := by
        rw [← centralizer_carrier_eq]; exact (complement_range lens.compl).symm
      rw [h1, h2, double_complement]
      apply Set.Subset.antisymm
      · rintro _ ⟨f, -, rfl⟩
        exact ⟨fun v => (double_complement_iso_lens lens).set
            (f ((double_complement_iso_lens lens).get v)) v,
          Set.mem_univ _, by funext s; simp [chain, Lens.update]⟩
      · rintro _ ⟨g, -, rfl⟩
        refine ⟨fun q => (double_complement_iso_lens lens).get
            (g (Classical.choose (hiso.2 q))), Set.mem_univ _, ?_⟩
        funext s; simp only [chain, Lens.update]
        have key : ∀ (v w : a), (double_complement_iso_lens lens).set
            ((double_complement_iso_lens lens).get w) v = w :=
          fun v w => hiso.1 ((double_complement_iso_lens lens).set_get v
              ((double_complement_iso_lens lens).get w))
        rw [key]
        exact congr_arg (fun v => lens.set (g v) s)
          (hiso.1 (Classical.choose_spec (hiso.2 _)))
    · rw [not_nonempty_iff] at hm
      have heq : ∀ f g : m → m, f = g := fun f g => funext fun x => IsEmpty.elim hm x
      have h_univ : Set.centralizer (Set.univ : Set (m → m)) = Set.univ := by
        ext f; simp only [Set.mem_centralizer_iff, Set.mem_univ, iff_true]; intro g _; exact heq _ _
      have himg : Set.image lens.update ⊤ = Set.univ :=
        Set.eq_univ_iff_forall.mpr fun f =>
          ⟨Classical.arbitrary _, Set.mem_univ _, heq _ _⟩
      rw [himg, h_univ, h_univ]

theorem LensRange.complement_range (lens : Lens a m) :
    lens.compl.range = lens.rangeᶜ := by
  have key : ∀ {x y : LensRange m}, x.updates = y.updates → x = y := by
    intro x y hxy
    obtain ⟨xu, xi, xc, xd⟩ := x; obtain ⟨yu, yi, yc, yd⟩ := y
    simp only at hxy; subst hxy; rfl
  refine key ?_
  change Set.image lens.compl.update ⊤ =
    (Submonoid.centralizer (Set.image lens.update ⊤)).carrier
  exact _root_.complement_range lens

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

theorem LensRange.compl_compl (x : LensRange a) : xᶜᶜ = x := by
  have key : ∀ {p q : LensRange a}, p.updates = q.updates → p = q := by
    intro p q h; obtain ⟨_,_,_,_⟩ := p; obtain ⟨_,_,_,_⟩ := q
    simp only at h; subst h; rfl
  apply key; simp only [Compl.compl]; exact x.double_commutant

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

theorem Lens.range_defines_preorder [Nonempty m] (x : Lens a m) (y : Lens b m) :
    x.range ≤ y.range ↔ LensIn.mk' x ≤ LensIn.mk' y := by
  /-
  Direction →  (∃ z, chain y z = x  →  x.range ≤ y.range):
    Given z with chain y z = x, for any f : a → a,
    x.update f = (chain y z).update f = y.update (fun v => z.set (f (z.get v)) v),
    so every x-update is a y-update, i.e., x.range.updates ⊆ y.range.updates.

  Direction ←  (x.range ≤ y.range  →  ∃ z, chain y z = x):
    (1) Centralizer antitonicity: x.range.updates ⊆ y.range.updates implies
        centralizer(y.range.updates) ⊆ centralizer(x.range.updates), i.e.,
        y.compl.range.updates ⊆ x.compl.range.updates (by complement_range).
        So every y.compl-update commutes with every x-update.
    (2) From this commutativity, x.get factors through y.get:
        y.get s = y.get t  →  x.get s = x.get t.
        (Proof: apply commutativity of x.update (fun _ => x.get t) with a
        y.compl-update that maps s to a point with the same y.get as t.)
    (3) Fix m₀ : m and define z : Lens a b by
          z.get v  := x.get (y.set v m₀)
          z.set c v := y.get (x.set c (y.set v m₀))
        These are well-defined (z.get independent of m₀ by step 2,
        z.set independent of m₀ since x.set c s depends on y.get s only).
    (4) Verify chain y z = x:
        get: (chain y z).get s = z.get (y.get s) = x.get (y.set (y.get s) m₀) = x.get s  (step 2)
        set: (chain y z).set c s = y.set (z.set c (y.get s)) s
                                 = y.set (y.get (x.set c (y.set (y.get s) m₀))) s
             From x.range ≤ y.range, x.set c s = y.set (y.get (x.set c s)) s,
             and y.get (x.set c s) = y.get (x.set c (y.set (y.get s) m₀)) by step 2,
             so (chain y z).set c s = y.set (y.get (x.set c s)) s = x.set c s.
  -/
  constructor
  · intro hle
    -- Step 1: centralizer antitonicity gives y.compl.range ≤ x.compl.range
    have hcompl : y.compl.range ≤ x.compl.range := by
      rw [LensRange.complement_range y, LensRange.complement_range x]
      exact Submonoid.centralizer_le hle
    -- Step 2: x.get factors through y.get
    have hfactor : ∀ s t : m, y.get s = y.get t → x.get s = x.get t := by
      intro s t hyt
      have hmem : y.compl.update (fun _ => Quotient.mk'' t) ∈ y.compl.range.updates :=
        ⟨fun _ => Quotient.mk'' t, Set.mem_univ _, rfl⟩
      obtain ⟨g, -, hg⟩ := hcompl hmem
      have hget : x.get (x.compl.update g s) = x.get s := by
        change x.get (x.compl.set (g (Quotient.mk'' s)) s) = x.get s
        induction g (Quotient.mk'' s) using Quotient.inductionOn with
        | h v => exact x.set_get v (x.get s)
      have hst : y.compl.update (fun _ => Quotient.mk'' t) s = t := by
        change y.set (y.get s) t = t
        rw [hyt]; exact y.get_set t
      rw [← hg] at hst
      rw [hst] at hget
      exact hget.symm
    -- Step 3: define z : Lens a b
    let m0 : m := Classical.choice inferInstance
    have hfact2 : ∀ (d : a) (s₁ s₂ : m), y.get s₁ = y.get s₂ →
        y.get (x.set d s₁) = y.get (x.set d s₂) := fun d s₁ s₂ heq => by
      obtain ⟨g, -, hg⟩ := hle ⟨fun _ => d, Set.mem_univ _, rfl⟩
      have key : ∀ s, y.get (x.set d s) = g (y.get s) := fun s => by
        have eq := congr_fun hg s
        simp only [Lens.update] at eq
        rw [← eq, y.set_get]
      simp only [key, heq]
    let z : Lens a b := {
      get := fun v => x.get (y.set v m0)
      set := fun c v => y.get (x.set c (y.set v m0))
      set_get := fun v c => (hfactor _ _ (y.set_get m0 _)).trans (x.set_get _ _)
      get_set := fun v => by rw [x.get_set, y.set_get]
      set_set := fun v c d => (hfact2 d _ _ (y.set_get m0 _)).trans (by rw [x.set_set])
    }
    let chain_eq : chain (LensIn.mk' y).lens z = (LensIn.mk' x).lens := by
      ext c mem
      simp [chain, LensIn.mk']
      obtain ⟨g, -, hg⟩ := hle ⟨fun _ => c, Set.mem_univ _, rfl⟩
      have hgkey : ∀ s, y.set (g (y.get s)) s = x.set c s := fun s => by
        have := congr_fun hg s; simp only [Lens.update] at this; exact this
      have hgget : ∀ s, y.get (x.set c s) = g (y.get s) := fun s => by
        rw [← hgkey s]; exact y.set_get s _
      have heq : y.get (x.set c (y.set (y.get mem) m0)) = y.get (x.set c mem) :=
        hfact2 c _ _ (y.set_get m0 (y.get mem))
      change y.set (y.get (x.set c (y.set (y.get mem) m0))) mem = x.set c mem
      rw [heq, hgget mem, hgkey mem]
    exact ⟨z, chain_eq⟩
  · rintro ⟨z, hz⟩
    have hz' : chain y z = x := hz
    rintro _ ⟨f, -, rfl⟩
    exact ⟨fun v => z.set (f (z.get v)) v, Set.mem_univ _,
      by funext s; rw [← hz']; simp [Lens.update, chain]⟩

noncomputable def LensIn.antisymmOrderEmb [Nonempty m] :
    Antisymmetrization (LensIn m) (· ≤ ·) ↪o LensRange m where
  toFun := Quotient.lift (fun ⟨_, lens⟩ => lens.range)
    fun a b ⟨h1, h2⟩ => le_antisymm
      ((Lens.range_defines_preorder a.lens b.lens).mpr h1)
      ((Lens.range_defines_preorder b.lens a.lens).mpr h2)
  map_rel_iff' {a b} := by
    induction a using Quotient.inductionOn with | h x =>
    induction b using Quotient.inductionOn with | h y =>
    exact Lens.range_defines_preorder x.lens y.lens
  inj' := by
    intro a b h
    induction a using Quotient.inductionOn with | h x =>
    induction b using Quotient.inductionOn with | h y =>
    apply Quotient.sound
    exact ⟨(Lens.range_defines_preorder x.lens y.lens).mp (le_of_eq h),
           (Lens.range_defines_preorder y.lens x.lens).mp (le_of_eq h.symm)⟩

/-! ## Orbits and the global getter -/

/-- The `R`-orbit equivalence on `m`: `s ~ s'` iff one is reachable from the other via
    `R`-updates (the equivalence closure of the directed orbit relation, since `R` is a
    monoid not a group). -/
def LensRange.orbit_setoid (R : LensRange m) : Setoid m where
  r := Relation.EqvGen (fun s s' => ∃ f ∈ R.updates, f s = s')
  iseqv := Relation.EqvGen.is_equivalence _

/-- The "global getter" of a LensRange: the quotient projection onto orbit-classes.

    Reading: two states give the same getter value iff they are in the same `R`-orbit.

    For a lens-derived range `R = l.range`, two states are in the same `R`-orbit iff they
    differ only in `l`'s content — so this getter encodes the *complement* of `l`.

    Convention: `glob A` is typically "what A touches", i.e. **the commutant's** orbits,
    so one writes `glob A := A.range.commutant.global_getter` (commutant = `Rᶜ`).
    Equivalently `glob A := A.rangeᶜ.global_getter`. -/
def LensRange.global_getter (R : LensRange m) : Getter (Quotient R.orbit_setoid) m where
  get := Quotient.mk R.orbit_setoid

/-- The "touched" getter: the same construction applied to the commutant.
    For a lens-derived range `R = l.range`, this is isomorphic to `l.toGetter`. -/
def LensRange.touched_getter (R : LensRange m) : Getter (Quotient Rᶜ.orbit_setoid) m :=
  Rᶜ.global_getter
