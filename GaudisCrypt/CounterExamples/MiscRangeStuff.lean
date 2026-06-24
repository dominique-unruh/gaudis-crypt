import GaudisCrypt.Language.Lens
import GaudisCrypt.ProgramRange

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

/-- Kleisli composition for `Option`: apply `g` first, then `f` on the result. -/
instance : Monoid (m → Option m) where
  mul f g := fun x => g x >>= f
  one := fun x => some x
  mul_assoc f g h := funext fun x => by
    change h x >>= (fun y => g y >>= f) = (h x >>= g) >>= f
    exact (Option.bind_assoc (h x) g f).symm
  one_mul f := funext fun x => by
    change f x >>= (fun y => some y) = f x
    cases f x <;> rfl
  mul_one f := funext fun x => by
    change some x >>= f = f x
    rfl

/-- Analogue of `TotLensRange` where updates are partial functions `m → Option m`
    composed via Kleisli composition for `Option`. -/
structure OptionLensRange (m : Type _) where
  updates : Set (m → Option m)
  one_mem : (1 : m → Option m) ∈ updates
  mul_mem : ∀ {f g : m → Option m}, f ∈ updates → g ∈ updates → f * g ∈ updates
  double_commutant :
    (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates

def OptionLensRange.from (generators : Set (m → Option m)) : OptionLensRange m where
  updates := Submonoid.centralizer (Submonoid.centralizer generators).carrier
  one_mem := Submonoid.one_mem _
  mul_mem := fun hf hg => Submonoid.mul_mem _ hf hg
  double_commutant := by
    exact Set.centralizer_centralizer_centralizer _

/-- Relational composition: `(R * S) x z = ∃ y, S x y ∧ R y z`
    (apply `S` first, then `R` — mirrors `f * g = f ∘ g` for functions). -/
instance {m : Type*} : Monoid (m → m → Prop) where
  mul R S x z := ∃ y, S x y ∧ R y z
  one := Eq
  mul_assoc R S T := funext fun x => funext fun z => propext (by
    constructor
    · rintro ⟨y, hTxy, w, hSyw, hRwz⟩; exact ⟨w, ⟨y, hTxy, hSyw⟩, hRwz⟩
    · rintro ⟨w, ⟨y, hTxy, hSyw⟩, hRwz⟩; exact ⟨y, hTxy, w, hSyw, hRwz⟩)
  one_mul R := funext fun x => funext fun z => propext (by
    constructor
    · rintro ⟨y, hRy, rfl⟩; exact hRy
    · intro hR; exact ⟨z, hR, rfl⟩)
  mul_one R := funext fun x => funext fun z => propext (by
    constructor
    · rintro ⟨y, rfl, hRy⟩; exact hRy
    · intro hR; exact ⟨x, rfl, hR⟩)

/-- Analogue of `TotLensRange` where updates are relations on `m`
    composed via relational composition. -/
structure RelLensRange (m : Type*) where
  updates : Set (m → m → Prop)
  one_mem : (1 : m → m → Prop) ∈ updates
  mul_mem : ∀ {R S : m → m → Prop}, R ∈ updates → S ∈ updates → R * S ∈ updates
  double_commutant :
    (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates



open GaudisCrypt.Language.Semantics in
/-- Kleisli composition for `SubProbability`: apply `g` first, then `f` on the result. -/
noncomputable instance {m : Type*} : Monoid (m → SubProbability m) where
  mul f g := fun x => g x >>= f
  one := pure
  mul_assoc f g h := funext fun x => by
    apply Subtype.ext; letI : MeasurableSpace m := ⊤
    exact (MeasureTheory.Measure.bind_bind
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
  one_mul f := funext fun x => by
    apply Subtype.ext; letI : MeasurableSpace m := ⊤
    exact MeasureTheory.Measure.bind_dirac
  mul_one f := funext fun x => by
    apply Subtype.ext; letI : MeasurableSpace m := ⊤
    change (MeasureTheory.Measure.dirac x).bind (fun a => (f a).1) = (f x).1
    exact MeasureTheory.Measure.dirac_bind measurable_from_top x

open GaudisCrypt.Language.Semantics in
/-- Analogue of `TotLensRange` where updates are sub-probability kernels `m → SubProbability m`
    composed via Kleisli composition for `SubProbability`. -/
structure SubProbLensRange (m : Type _) where
  updates : Set (m → SubProbability m)
  one_mem : (1 : m → SubProbability m) ∈ updates
  mul_mem : ∀ {f g : m → SubProbability m}, f ∈ updates → g ∈ updates → f * g ∈ updates
  double_commutant :
    (Submonoid.centralizer (Submonoid.centralizer updates).carrier).carrier = updates

open GaudisCrypt.Language.Semantics in
/-- Convert a vector of non-negative weights (summing to at most 1) into a
    sub-probability measure on a finite type.  The resulting measure assigns
    mass `v x` to the point `x`. -/
noncomputable def SubProbability.ofVector {a : Type*} [Fintype a]
    (v : a → NNReal) (hv : ∑ x, v x ≤ 1) : SubProbability a :=
  letI : MeasurableSpace a := ⊤
  haveI : MeasurableSingletonClass a := ⟨fun _ => trivial⟩
  ⟨∑ x : a, (v x : ENNReal) • MeasureTheory.Measure.dirac x, by
    change (∑ x : a, (v x : ENNReal) • MeasureTheory.Measure.dirac x) ⊤ ≤ 1
    simp only [MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply,
               MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply,
               smul_eq_mul, Set.top_eq_univ, Set.indicator_univ, Pi.one_apply, mul_one]
    calc ∑ x : a, (v x : ENNReal)
        = ↑(∑ x : a, v x) := by push_cast; rfl
      _ ≤ 1 := by exact_mod_cast hv⟩

open GaudisCrypt.Language.Semantics in
/-- Convert a column-sub-stochastic matrix (each column sums to at most 1) into a
    probabilistic function `b → SubProbability a`.  Column `j` of `M` gives the
    distribution `ofMatrix M hM j`.

    With this convention `ofMatrix` is a monoid homomorphism:
    `ofMatrix (M * N) = ofMatrix M * ofMatrix N`. -/
noncomputable def SubProbability.ofMatrix {a b : Type*} [Fintype a]
    (M : Matrix a b NNReal) (hM : ∀ j, ∑ i, M i j ≤ 1) :
    b → SubProbability a :=
  fun j => SubProbability.ofVector (fun i => M i j) (hM j)

section SubProbabilityOfMatrixProperties

open GaudisCrypt.Language.Semantics

variable {a b : Type*} [Fintype a] [Fintype b] -- [DecidableEq a] [DecidableEq b]

open Classical in
/-- `ofVector` is injective: equal sub-probability measures imply equal weight vectors. -/
theorem SubProbability.ofVector_inj {v w : a → NNReal} {hv : ∑ x, v x ≤ 1} {hw : ∑ x, w x ≤ 1} :
    SubProbability.ofVector v hv = SubProbability.ofVector w hw ↔ v = w := by
  constructor
  · intro h
    funext j
    have h1 := congr_arg (fun μ : SubProbability a => μ.1 {j}) h
    simp only [SubProbability.ofVector] at h1
    letI : MeasurableSpace a := ⊤
    haveI : MeasurableSingletonClass a := ⟨fun _ => trivial⟩
    simp only [MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply,
               MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply,
               smul_eq_mul, Set.indicator_singleton, Pi.one_apply] at h1
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
               Finset.mem_univ, if_true] at h1
    exact_mod_cast h1
  · rintro rfl; rfl

omit [Fintype b] in
/-- `ofMatrix` is injective. -/
theorem SubProbability.ofMatrix_inj {M N : Matrix a b NNReal}
    {hM : ∀ j, ∑ i, M i j ≤ 1} {hN : ∀ j, ∑ i, N i j ≤ 1} :
    SubProbability.ofMatrix M hM = SubProbability.ofMatrix N hN ↔ M = N := by
  constructor
  · intro h
    funext i j
    have hj := congr_fun h j
    simp only [SubProbability.ofMatrix, SubProbability.ofVector_inj] at hj
    exact congr_fun hj i
  · rintro rfl; rfl

omit [Fintype b] in
/-- The zero matrix maps to the zero (bottom) sub-probability kernel. -/
theorem SubProbability.ofMatrix_zero :
    SubProbability.ofMatrix (0 : Matrix a b NNReal) (fun _ => by simp) =
    fun _ => (⊥ : SubProbability a) := by
  funext j
  apply Subtype.ext
  simp [SubProbability.ofMatrix, SubProbability.ofVector]; rfl

open Classical in
/-- The identity matrix maps to `pure` (the Kleisli identity). -/
theorem SubProbability.ofMatrix_one :
    SubProbability.ofMatrix (1 : Matrix a a NNReal)
      (fun j => by simp [Matrix.one_apply]) = pure := by
  funext j
  apply Subtype.ext
  letI : MeasurableSpace a := ⊤
  haveI : MeasurableSingletonClass a := ⟨fun _ => trivial⟩
  simp only [SubProbability.ofMatrix, SubProbability.ofVector, Matrix.one_apply,
             pure, Pure.pure]
  simp_rw [apply_ite (α := NNReal) (β := ENNReal) (↑·)]
  simp only [ENNReal.coe_one, ENNReal.coe_zero, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `ofMatrix` is a monoid homomorphism: it maps matrix products to Kleisli products.
    The Kleisli product `ofMatrix M * ofMatrix N` applies `N` first then `M`,
    which corresponds to the matrix product `M * N`. -/
theorem SubProbability.ofMatrix_mul {M N : Matrix a a NNReal}
    {hM : ∀ j, ∑ i, M i j ≤ 1} {hN : ∀ j, ∑ i, N i j ≤ 1}
    {hMN : ∀ j, ∑ i, (M * N) i j ≤ 1} :
    SubProbability.ofMatrix M hM * SubProbability.ofMatrix N hN =
    SubProbability.ofMatrix (M * N) hMN := by
  funext j
  apply Subtype.ext
  letI : MeasurableSpace a := ⊤
  haveI : MeasurableSingletonClass a := ⟨fun _ => trivial⟩
  simp only [SubProbability.ofMatrix, SubProbability.ofVector]
  -- (ofMatrix N j >>= ofMatrix M).1 = (ofMatrix (M*N) j).1
  -- i.e., (∑ i, N i j • dirac i).bind (fun i => ∑ k, M k i • dirac k)
  --     = ∑ k, (M * N) k j • dirac k
  -- Key: (M * N) k j = ∑ i, M k i * N i j
  simp only [HMul.hMul, Mul.mul, bind, SubProbability.ofMatrix, SubProbability.ofVector]
  apply MeasureTheory.Measure.ext
  intro s _
  rw [MeasureTheory.Measure.bind_apply ‹MeasurableSet s› measurable_from_top.aemeasurable,
      MeasureTheory.lintegral_finsetSum_measure,
      MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply]
  simp only [MeasureTheory.lintegral_smul_measure,
             MeasureTheory.lintegral_dirac' _ measurable_from_top,
             MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.coe_finsetSum,
             Finset.sum_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext x
  simp only [dotProduct]
  push_cast
  simp_rw [show ∀ (A B C : ENNReal), A * (B * C) = B * A * C from
    fun A B C => by rw [← mul_assoc, mul_comm A B]]
  rw [← Finset.sum_mul]

end SubProbabilityOfMatrixProperties

namespace CE1

open GaudisCrypt.Language.Semantics

/-- The matrix for `p` from Counterexample 1 (column convention: column `j` = distribution
    over outputs given input `j`).
    - Column 0: uniform on `{1, 2}`
    - Column 1: uniform on `{0, 1}`
    - Column 2: uniform on `{0, 2}` -/
noncomputable def p_matrix : Matrix (Fin 3) (Fin 3) NNReal :=
  !![(0 : NNReal), 1/2, 1/2;
     1/2, 1/2, 0;
     1/2, 0, 1/2]

/-- The matrix for `q` from Counterexample 1 (column convention).
    - Column 0: uniform on `{1, 2}`
    - Column 1: Dirac at 0
    - Column 2: Dirac at 0 -/
noncomputable def q_matrix : Matrix (Fin 3) (Fin 3) NNReal :=
  !![(0 : NNReal), 1, 1;
     1/2, 0, 0;
     1/2, 0, 0]

/-- The probabilistic function `p` from Counterexample 1, as `SubProbability.ofMatrix p_matrix`. -/
noncomputable def p : Fin 3 → SubProbability (Fin 3) :=
  SubProbability.ofMatrix p_matrix
    (fun j => by fin_cases j <;> simp [p_matrix, Fin.sum_univ_three] <;> norm_num)

/-- The probabilistic function `q` from Counterexample 1, as `SubProbability.ofMatrix q_matrix`. -/
noncomputable def q : Fin 3 → SubProbability (Fin 3) :=
  SubProbability.ofMatrix q_matrix
    (fun j => by fin_cases j <;> simp [q_matrix, Fin.sum_univ_three]; norm_num)

/-- `p_matrix` and `q_matrix` do not commute as matrices.
    Witness: entry `(0, 0)` is `1/2` in `p_matrix * q_matrix` but `1` in `q_matrix * p_matrix`. -/
theorem matrices_not_commute : p_matrix * q_matrix ≠ q_matrix * p_matrix := by
  intro h
  have := congr_fun (congr_fun h 0) 0
  simp [p_matrix, q_matrix, Matrix.mul_apply, Fin.sum_univ_three] at this
  norm_num at this

open GaudisCrypt.Language.Semantics in
/-- `p` and `q` do not commute in the Kleisli monoid,
    because `p_matrix` and `q_matrix` do not commute as matrices. -/
theorem pq_not_commute : p * q ≠ q * p := by
  have hpq : ∀ j : Fin 3, ∑ i, (p_matrix * q_matrix) i j ≤ 1 := by
    intro j; fin_cases j <;>
    simp [p_matrix, q_matrix, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have hqp : ∀ j : Fin 3, ∑ i, (q_matrix * p_matrix) i j ≤ 1 := by
    intro j; fin_cases j <;>
    simp [p_matrix, q_matrix, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  simp only [p, q, SubProbability.ofMatrix_mul (hMN := hpq),
             SubProbability.ofMatrix_mul (hMN := hqp)]
  rw [Ne, SubProbability.ofMatrix_inj]
  exact matrices_not_commute

end CE1


/-- The centralizer of a set `S ⊆ α` with respect to a binary relation `commutes : α → β → Prop`:
    the set of all `b : β` that commute with every element of `S`. -/
def Centralizer {α β : Type*} (commutes : α → β → Prop) (S : Set α) : Set β :=
  {b | ∀ a ∈ S, commutes a b}

/-- The function matrix of `f : m → m` in column convention:
    column `j` is the Dirac distribution at `f j`, i.e., `P_f i j = 1` iff `i = f j`. -/
def functionMatrix {m : Type*} [DecidableEq m] (f : m → m) : Matrix m m NNReal :=
  Matrix.of (fun i j => if i = f j then 1 else 0)

/-- A stochastic matrix `M` commutes with a total function `f : m → m` if
    `M * P_f = P_f * M`, where `P_f` is the function matrix of `f`. -/
def commuteMT {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m NNReal) (f : Function.End m) : Prop :=
  M * functionMatrix f = functionMatrix f * M

open GaudisCrypt.Language.Semantics in
/-- A stochastic map `F : m → SubProbability m` commutes with a total function `f : m → m`
    if `F * (pure ∘ f) = (pure ∘ f) * F` in the Kleisli monoid,
    i.e., `∀ x, F (f x) = F x >>= fun y => pure (f y)`. -/
def commuteST {m : Type*} (F : m → SubProbability m) (f : Function.End m) : Prop :=
  F * (pure ∘ f) = (pure ∘ f) * F

/-- The partial-function matrix of `f : m → Option m` in column convention: column `j` is the
    Dirac column at `i` when `f j = some i`, and the zero column when `f j = none`, i.e.
    `P_f i j = 1` iff `f j = some i`. -/
def partialFunctionMatrix {m : Type*} [DecidableEq m] (f : m → Option m) : Matrix m m NNReal :=
  Matrix.of (fun i j => if f j = some i then 1 else 0)

/-- A stochastic matrix `M` commutes with a partial function `f : m → Option m` if
    `M * P_f = P_f * M`, where `P_f` is the partial-function matrix of `f`. -/
def commuteMP {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m NNReal) (f : m → Option m) : Prop :=
  M * partialFunctionMatrix f = partialFunctionMatrix f * M

open GaudisCrypt.Language.Semantics in
/-- The sub-probability kernel of a partial function `f : m → Option m`:
    `f x = some y` maps to `pure y` (Dirac at `y`), and `f x = none` maps to `⊥` (the zero
    sub-probability measure). -/
noncomputable def partialToKernel {m : Type*} (f : m → Option m) : m → SubProbability m :=
  fun x => (f x).elim ⊥ pure

open GaudisCrypt.Language.Semantics in
/-- A stochastic map `F : m → SubProbability m` commutes with a partial function
    `f : m → Option m` if `F * partialToKernel f = partialToKernel f * F` in the Kleisli monoid. -/
def commuteSP {m : Type*} (F : m → SubProbability m) (f : m → Option m) : Prop :=
  F * partialToKernel f = partialToKernel f * F


section CommuteSTReduction

open GaudisCrypt.Language.Semantics

variable {a : Type*} [Fintype a] [DecidableEq a]

open Classical in
/-- Each column of `functionMatrix f` sums to `1` (it is a Dirac column). -/
theorem functionMatrix_colSum (f : a → a) (j : a) :
    ∑ i, functionMatrix f i j = 1 := by
  simp [functionMatrix, Finset.sum_ite_eq']

open Classical in
/-- The Kleisli identity `pure ∘ f` of a total function is the sub-probability kernel
    of its function matrix `functionMatrix f`. -/
theorem pure_comp_eq_ofMatrix (f : a → a) (hf : ∀ j, ∑ i, functionMatrix f i j ≤ 1) :
    (pure ∘ f) = SubProbability.ofMatrix (functionMatrix f) hf := by
  funext j
  have h1 := congr_fun (SubProbability.ofMatrix_one (a := a)) (f j)
  simp only [Function.comp_apply]
  rw [← h1]
  unfold SubProbability.ofMatrix
  congr 1
  ext
  simp [functionMatrix, Matrix.one_apply]




/-- `commuteST (ofMatrix M) f` reduces to the matrix-level `commuteMT M f`, via
    multiplicativity (`ofMatrix_mul`) and injectivity (`ofMatrix_inj`) of `ofMatrix`. -/
theorem commuteST_ofMatrix_iff (M : Matrix a a NNReal) (hM : ∀ j, ∑ i, M i j ≤ 1) (f : a → a) :
    commuteST (SubProbability.ofMatrix M hM) f ↔ commuteMT M f := by
  have hf : ∀ j, ∑ i, functionMatrix f i j ≤ 1 := fun j => (functionMatrix_colSum f j).le
  have key : ∀ i j, (M * functionMatrix f) i j = M i (f j) := fun i j => by
    simp [Matrix.mul_apply, functionMatrix, Finset.sum_ite_eq']
  have hpf : ∀ j, ∑ i, (M * functionMatrix f) i j ≤ 1 := fun j => by
    simp only [key]; exact hM (f j)
  have key2 : ∀ j, ∑ i, (functionMatrix f * M) i j = ∑ k, M k j := fun j => by
    simp only [Matrix.mul_apply, functionMatrix, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [Finset.sum_ite_eq', ite_mul]
  have hfp : ∀ j, ∑ i, (functionMatrix f * M) i j ≤ 1 := fun j => by
    rw [key2]; exact hM j
  unfold commuteST commuteMT
  rw [pure_comp_eq_ofMatrix f hf,
      show SubProbability.ofMatrix M hM * SubProbability.ofMatrix (functionMatrix f) hf
            = SubProbability.ofMatrix (M * functionMatrix f) hpf from SubProbability.ofMatrix_mul,
      show SubProbability.ofMatrix (functionMatrix f) hf * SubProbability.ofMatrix M hM
            = SubProbability.ofMatrix (functionMatrix f * M) hfp from SubProbability.ofMatrix_mul,
      SubProbability.ofMatrix_inj]

end CommuteSTReduction


section CommuteSPReduction

open GaudisCrypt.Language.Semantics

variable {a : Type*} [Fintype a] [DecidableEq a]

/-- Each column of `partialFunctionMatrix f` sums to at most `1` (a Dirac column, or the zero
    column when `f j = none`). -/
theorem partialFunctionMatrix_colSum_le (f : a → Option a) (j : a) :
    ∑ i, partialFunctionMatrix f i j ≤ 1 := by
  simp only [partialFunctionMatrix, Matrix.of_apply]
  rcases hfj : f j with _ | i₀
  · simp
  · simp [Finset.sum_ite_eq]

open Classical in
/-- The kernel `partialToKernel f` of a partial function is the sub-probability kernel of its
    partial-function matrix. -/
theorem partialToKernel_eq_ofMatrix (f : a → Option a)
    (hf : ∀ j, ∑ i, partialFunctionMatrix f i j ≤ 1) :
    partialToKernel f = SubProbability.ofMatrix (partialFunctionMatrix f) hf := by
  funext j
  simp only [partialToKernel]
  rcases hfj : f j with _ | i₀
  · have h0 := congr_fun (SubProbability.ofMatrix_zero (a := a) (b := a)) j
    change (⊥ : SubProbability a) = _
    rw [← h0]
    unfold SubProbability.ofMatrix
    congr 1
    ext i
    simp [partialFunctionMatrix, hfj]
  · have h1 := congr_fun (SubProbability.ofMatrix_one (a := a)) i₀
    change pure i₀ = _
    rw [← h1]
    unfold SubProbability.ofMatrix
    congr 1
    ext i
    simp [partialFunctionMatrix, hfj, Matrix.one_apply, eq_comm]

/-- `commuteSP (ofMatrix M) f` reduces to the matrix-level `commuteMP M f`, via multiplicativity
    (`ofMatrix_mul`) and injectivity (`ofMatrix_inj`) of `ofMatrix`. -/
theorem commuteSP_ofMatrix_iff (M : Matrix a a NNReal) (hM : ∀ j, ∑ i, M i j ≤ 1)
    (f : a → Option a) :
    commuteSP (SubProbability.ofMatrix M hM) f ↔ commuteMP M f := by
  have hf : ∀ j, ∑ i, partialFunctionMatrix f i j ≤ 1 := partialFunctionMatrix_colSum_le f
  have key : ∀ i j, (M * partialFunctionMatrix f) i j = (f j).elim 0 (fun k => M i k) :=
    fun i j => by
      rcases hfj : f j with _ | k₀
      · simp [Matrix.mul_apply, partialFunctionMatrix, hfj]
      · simp [Matrix.mul_apply, partialFunctionMatrix, hfj, Finset.sum_ite_eq]
  have hpf : ∀ j, ∑ i, (M * partialFunctionMatrix f) i j ≤ 1 := fun j => by
    simp only [key]
    rcases hfj : f j with _ | k₀
    · simp
    · simpa using hM k₀
  have hfp : ∀ j, ∑ i, (partialFunctionMatrix f * M) i j ≤ 1 := fun j => by
    calc ∑ i, (partialFunctionMatrix f * M) i j
        = ∑ k, (∑ i, partialFunctionMatrix f i k) * M k j := by
          simp only [Matrix.mul_apply]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun k _ => (Finset.sum_mul _ _ _).symm)
      _ ≤ ∑ k, 1 * M k j := Finset.sum_le_sum (fun k _ => by gcongr; exact hf k)
      _ = ∑ k, M k j := by simp
      _ ≤ 1 := hM j
  unfold commuteSP commuteMP
  rw [partialToKernel_eq_ofMatrix f hf,
      show SubProbability.ofMatrix M hM * SubProbability.ofMatrix (partialFunctionMatrix f) hf
            = SubProbability.ofMatrix (M * partialFunctionMatrix f) hpf from
          SubProbability.ofMatrix_mul,
      show SubProbability.ofMatrix (partialFunctionMatrix f) hf * SubProbability.ofMatrix M hM
            = SubProbability.ofMatrix (partialFunctionMatrix f * M) hfp from
          SubProbability.ofMatrix_mul,
      SubProbability.ofMatrix_inj]

end CommuteSPReduction


open GaudisCrypt.Language.Semantics in
/-- The deterministic bicommutant `C(C(S))` of a set of stochastic kernels `S`: the
    `Submonoid.centralizer` (in the composition monoid `m → m`) of the deterministic centralizer
    `Centralizer commuteST S`.  Returned as a `Set (m → m)` (the submonoid carrier) so it can
    feed `TotLensRange.from`. -/
def hullST {m : Type*} (S : Set (m → SubProbability m)) : Set (Function.End m) :=
  (Submonoid.centralizer (Centralizer commuteST S)).carrier

open GaudisCrypt.Language.Semantics in
/-- The partial-function bicommutant `C(C(S))` of a set of stochastic kernels `S`: the
    `Submonoid.centralizer` (in the Kleisli-`Option` monoid `m → Option m`) of the partial
    centralizer `Centralizer commuteSP S`.  The partial analogue of `hullST`. -/
def hullSP {m : Type*} (S : Set (m → SubProbability m)) : Set (m → Option m) :=
  (Submonoid.centralizer (Centralizer commuteSP S)).carrier


namespace CE1

/-- The swap permutation `τ = (2 3)`, swapping indices `1` and `2` (0-indexed),
    as a total function on `Fin 3`. -/
def tau : Function.End (Fin 3) := ![0, 2, 1]

/-- The deterministic centralizer of `{p_matrix}` is exactly `{id, τ}`, matching the claim
    `C({p}) = {id, τ}` in Counterexample 1.

    Forward direction is a finite case bash over all `27` functions `Fin 3 → Fin 3`
    (`decide` is unavailable since `NNReal` has no computable `DecidableEq`): only `id` and
    `τ` satisfy the matrix commutation `p_matrix * P_f = P_f * p_matrix`. -/
theorem centralizer_p_matrix : Centralizer commuteMT {p_matrix} = {id, tau} := by
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq,
             Set.mem_insert_iff]
  constructor
  · intro h
    unfold commuteMT at h
    have he : ∀ i j : Fin 3,
        (p_matrix * functionMatrix f) i j = (functionMatrix f * p_matrix) i j :=
      fun i j => by rw [h]
    have e00 := he 0 0; have e01 := he 0 1; have e02 := he 0 2
    have e10 := he 1 0; have e11 := he 1 1; have e12 := he 1 2
    have e20 := he 2 0; have e21 := he 2 1; have e22 := he 2 2
    clear he h
    simp only [Matrix.mul_apply, functionMatrix, p_matrix, Fin.sum_univ_three,
               Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
               Matrix.cons_val', Matrix.empty_val',
               Matrix.cons_val_fin_one] at e00 e01 e02 e10 e11 e12 e20 e21 e22
    have cases3 : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
    rcases cases3 (f 0) with h0|h0|h0 <;>
    rcases cases3 (f 1) with h1|h1|h1 <;>
    rcases cases3 (f 2) with h2|h2|h2 <;>
      first
        | (left; funext x; fin_cases x <;> simp [h0, h1, h2]; done)
        | (right; funext x; fin_cases x <;> simp [tau, h0, h1, h2]; done)
        | (exfalso; revert e00 e01 e02 e10 e11 e12 e20 e21 e22;
           norm_num [Fin.ext_iff, h0, h1, h2])
  · have hid : functionMatrix (id : Fin 3 → Fin 3) = 1 := by
      ext i j; simp [functionMatrix, Matrix.one_apply]
    rintro (rfl | rfl)
    · show commuteMT p_matrix id
      unfold commuteMT; rw [hid, mul_one, one_mul]
    · show commuteMT p_matrix tau
      unfold commuteMT
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [p_matrix, functionMatrix, tau, Matrix.mul_apply, Fin.sum_univ_three]

/-- The deterministic centralizer of `{q_matrix}` is exactly `{id, τ}`, matching the claim
    `C({q}) = {id, τ}` in Counterexample 1.

    Same finite case bash over all `27` functions `Fin 3 → Fin 3` as `centralizer_p_matrix`:
    only `id` and `τ` satisfy `q_matrix * P_f = P_f * q_matrix`. -/
theorem centralizer_q_matrix : Centralizer commuteMT {q_matrix} = {id, tau} := by
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    unfold commuteMT at h
    have he : ∀ i j : Fin 3,
        (q_matrix * functionMatrix f) i j = (functionMatrix f * q_matrix) i j :=
      fun i j => by rw [h]
    have e00 := he 0 0; have e01 := he 0 1; have e02 := he 0 2
    have e10 := he 1 0; have e11 := he 1 1; have e12 := he 1 2
    have e20 := he 2 0; have e21 := he 2 1; have e22 := he 2 2
    clear he h
    simp only [Matrix.mul_apply, functionMatrix, q_matrix, Fin.sum_univ_three,
               Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
               Matrix.cons_val', Matrix.empty_val',
               Matrix.cons_val_fin_one] at e00 e01 e02 e10 e11 e12 e20 e21 e22
    have cases3 : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
    rcases cases3 (f 0) with h0|h0|h0 <;>
    rcases cases3 (f 1) with h1|h1|h1 <;>
    rcases cases3 (f 2) with h2|h2|h2 <;>
      first
        | (left; funext x; fin_cases x <;> simp [h0, h1, h2]; done)
        | (right; funext x; fin_cases x <;> simp [tau, h0, h1, h2]; done)
        | (exfalso; revert e00 e01 e02 e10 e11 e12 e20 e21 e22;
           norm_num [Fin.ext_iff, h0, h1, h2])
  · have hid : functionMatrix (id : Fin 3 → Fin 3) = 1 := by
      ext i j; simp [functionMatrix, Matrix.one_apply]
    rintro (rfl | rfl)
    · show commuteMT q_matrix id
      unfold commuteMT; rw [hid, mul_one, one_mul]
    · show commuteMT q_matrix tau
      unfold commuteMT
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [q_matrix, functionMatrix, tau, Matrix.mul_apply, Fin.sum_univ_three]



/-- The stochastic centralizer of `{p}` equals `{id, τ}`, by reduction to the matrix-level
    `centralizer_p_matrix` through `commuteST_ofMatrix_iff`. -/
theorem centralizer_p : Centralizer commuteST {p} = {id, tau} := by
  rw [← centralizer_p_matrix]
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  exact commuteST_ofMatrix_iff p_matrix _ f

/-- The stochastic centralizer of `{q}` equals `{id, τ}`, by reduction to the matrix-level
    `centralizer_q_matrix` through `commuteST_ofMatrix_iff`. -/
theorem centralizer_q : Centralizer commuteST {q} = {id, tau} := by
  rw [← centralizer_q_matrix]
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  exact commuteST_ofMatrix_iff q_matrix _ f


/-- The constant map to `0`, the unique fixed point of `τ = (2 3)`. -/
def c₁ : Fin 3 → Fin 3 := fun _ => 0

/-- Helper for the deterministic bicommutant: the total functions commuting under composition
    with both `id` and `τ` are exactly `{id, τ, c₁}`, where `c₁` is the constant map to `τ`'s
    fixed point `0`.

    Stated over `Function.End (Fin 3)` to pin the composition monoid unambiguously: the bare type
    `Fin 3 → Fin 3` carries two `Monoid` instances here (pointwise and composition), and the
    composition one is definitionally equal to `Function.End`'s, so this transfers by defeq. -/
theorem centralizer_id_tau :
    (Submonoid.centralizer ({id, tau} : Set (Function.End (Fin 3))) : Set (Function.End (Fin 3)))
      = {id, tau, c₁} := by
  have core : ∀ f : Fin 3 → Fin 3,
      (∀ x, tau (f x) = f (tau x)) ↔ (f = id ∨ f = tau ∨ f = c₁) := by decide
  ext f
  rw [SetLike.mem_coe, Submonoid.mem_centralizer_iff]
  constructor
  · intro hf
    have hτ := hf tau (Or.inr rfl)
    exact (core f).mp (fun x => congr_fun hτ x)
  · intro hf g hg
    have hp : ∀ x, tau (f x) = f (tau x) := (core f).mpr hf
    rcases hg with rfl | rfl
    · funext x; rfl
    · funext x; exact hp x

/-- Both deterministic bicommutants `C(C({p}))` and `C(C({q}))` equal `{id, τ, c₁}`, an abelian
    set under composition; hence every element of `hullST {p}` commutes with every element of
    `hullST {q}`.  This is the (satisfied) hypothesis of the implication that Counterexample 1
    refutes — even though `p` and `q` themselves do not commute (`not_commute`). -/
theorem hullST_p_commutes_q : ∀ f ∈ hullST {p}, ∀ g ∈ hullST {q}, f * g = g * f := by
  have hp : hullST {p} = ({id, tau, c₁} : Set (Fin 3 → Fin 3)) := by
    unfold hullST; rw [centralizer_p]; exact centralizer_id_tau
  have hq : hullST {q} = ({id, tau, c₁} : Set (Fin 3 → Fin 3)) := by
    unfold hullST; rw [centralizer_q]; exact centralizer_id_tau
  intro f hf g hg
  rw [hp] at hf
  rw [hq] at hg
  rcases hf with rfl | rfl | rfl <;> rcases hg with rfl | rfl | rfl <;>
    (funext x; fin_cases x <;> rfl)

/-- The carrier of a `Submonoid.centralizer` is the `Set.centralizer`. -/
private lemma centralizer_carrier_eq' {m : Type*} (S : Set (Function.End m)) :
    (Submonoid.centralizer S).carrier = Set.centralizer S := by
  ext x; simp [Submonoid.mem_centralizer_iff, Set.mem_centralizer_iff]

open GaudisCrypt.Language.Semantics in
/-- `hullST S` is already double-commutant closed, i.e. it is a genuine `TotLensRange`: the
    `TotLensRange.from` it generates returns exactly `hullST S`.  This holds because `hullST S` is a
    single centralizer and `C∘C∘C = C` (`Set.centralizer_centralizer_centralizer`). -/
theorem from_hullST_updates {m : Type*} (S : Set (m → SubProbability m)) :
    (TotLensRange.from (hullST S)).updates = hullST S := by
  change (Submonoid.centralizer (Submonoid.centralizer (hullST S)).carrier).carrier = hullST S
  unfold hullST
  simp only [centralizer_carrier_eq']
  exact Set.centralizer_centralizer_centralizer _


theorem theorem_negated : ¬ ∀ (m : Type) (p q : m → SubProbability m),
  (∀ f ∈ hullST {p}, ∀ g ∈ hullST {q}, f * g = g * f) → p * q = q * p := by
  intros h
  exact pq_not_commute (h _ p q hullST_p_commutes_q)

end CE1


namespace CE2

open GaudisCrypt.Language.Semantics

/-- The matrix for `p` from Counterexample 2: the simple random walk on the 4-cycle
    `0-1-2-3-0` (column convention: column `j` is the output distribution from state `j`).
    `p_matrix i j = 1/2` exactly when `i` and `j` are adjacent on the cycle.  It is symmetric,
    so it coincides with the row-stochastic matrix in the text. -/
noncomputable def p_matrix : Matrix (Fin 4) (Fin 4) NNReal :=
  !![(0 : NNReal), 1/2, 0, 1/2;
     1/2, 0, 1/2, 0;
     0, 1/2, 0, 1/2;
     1/2, 0, 1/2, 0]

/-- The matrix for `q` from Counterexample 2: the "forgetful" kernel that ignores the current
    state and jumps to `0` or `2` with equal probability (column convention).  Every column is
    `(1/2, 0, 1/2, 0)ᵀ`; this is the transpose of the row-stochastic `q = 𝟙 rᵀ`,
    `r = (1/2, 0, 1/2, 0)`, in the text. -/
noncomputable def q_matrix : Matrix (Fin 4) (Fin 4) NNReal :=
  !![(1/2 : NNReal), 1/2, 1/2, 1/2;
     0, 0, 0, 0;
     1/2, 1/2, 1/2, 1/2;
     0, 0, 0, 0]

/-- `p_matrix` and `q_matrix` do not commute as matrices.
    Witness: entry `(0, 1)` is `0` in `p_matrix * q_matrix` but `1/2` in `q_matrix * p_matrix`. -/
theorem matrices_not_commute : p_matrix * q_matrix ≠ q_matrix * p_matrix := by
  intro h
  have := congr_fun (congr_fun h 0) 1
  simp [p_matrix, q_matrix, Matrix.mul_apply, Fin.sum_univ_four] at this
  norm_num at this

/-- The probabilistic kernel `p` from Counterexample 2, as `SubProbability.ofMatrix p_matrix`. -/
noncomputable def p : Fin 4 → SubProbability (Fin 4) :=
  SubProbability.ofMatrix p_matrix
    (fun j => by fin_cases j <;> simp [p_matrix, Fin.sum_univ_four] <;> norm_num)

/-- The probabilistic kernel `q` from Counterexample 2, as `SubProbability.ofMatrix q_matrix`. -/
noncomputable def q : Fin 4 → SubProbability (Fin 4) :=
  SubProbability.ofMatrix q_matrix
    (fun j => by fin_cases j <;> simp [q_matrix, Fin.sum_univ_four] <;> norm_num)

theorem pq_not_commute : p * q ≠ q * p := by
  have hpq : ∀ j : Fin 4, ∑ i, (p_matrix * q_matrix) i j ≤ 1 := by
    intro j; fin_cases j <;>
    simp [p_matrix, q_matrix, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  have hqp : ∀ j : Fin 4, ∑ i, (q_matrix * p_matrix) i j ≤ 1 := by
    intro j; fin_cases j <;>
    simp [p_matrix, q_matrix, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  simp only [p, q, SubProbability.ofMatrix_mul (hMN := hpq),
             SubProbability.ofMatrix_mul (hMN := hqp)]
  rw [Ne, SubProbability.ofMatrix_inj]
  exact matrices_not_commute


/-- The integer cycle-adjacency matrix `A = 2 · p_matrix` (entries in `{0,1}`). -/
def Aadj : Matrix (Fin 4) (Fin 4) ℕ :=
  !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

/-- The integer `{0,1}` partial-function matrix (column convention), the `ℕ`-valued analogue of
    `partialFunctionMatrix`. -/
def pfNat (f : Fin 4 → Option (Fin 4)) : Matrix (Fin 4) (Fin 4) ℕ :=
  Matrix.of (fun i j => if f j = some i then 1 else 0)

/-- The integer "forgetful" matrix `B = 2 · q_matrix` (entries in `{0,1}`). -/
def Badj : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 1, 1, 1; 0, 0, 0, 0; 1, 1, 1, 1; 0, 0, 0, 0]

/-- General bridge: if a stochastic matrix is `½ · A` for an integer matrix `A`, then
    `commuteMP M f` is equivalent to the **integer** matrix equation `A · P_f = P_f · A`.
    Since the `{0,1}`-matrix `partialFunctionMatrix f` is the `Nat.cast` image of `pfNat f`,
    scaling by the nonzero `½` and the injectivity of `ℕ ↪ ℝ≥0` reduce the `NNReal` commutation
    to a decidable condition over `ℕ`. -/
theorem commuteMP_iff_intAdj {M : Matrix (Fin 4) (Fin 4) NNReal} {A : Matrix (Fin 4) (Fin 4) ℕ}
    (hM : M = (1 / 2 : NNReal) • A.map (Nat.cast : ℕ → NNReal)) (f : Fin 4 → Option (Fin 4)) :
    commuteMP M f ↔ A * pfNat f = pfNat f * A := by
  have hpf : partialFunctionMatrix f = (pfNat f).map (Nat.cast : ℕ → NNReal) := by
    ext i j
    simp only [partialFunctionMatrix, pfNat, Matrix.map_apply, Matrix.of_apply,
               apply_ite (Nat.cast : ℕ → NNReal), Nat.cast_one, Nat.cast_zero]
  have hmul : ∀ M N : Matrix (Fin 4) (Fin 4) ℕ,
      (M * N).map (Nat.cast : ℕ → NNReal) = M.map Nat.cast * N.map Nat.cast :=
    fun M N => (Nat.castRingHom NNReal).mapMatrix.map_mul M N
  unfold commuteMP
  rw [hM, hpf, Matrix.smul_mul, Matrix.mul_smul, ← hmul, ← hmul,
      (smul_right_injective (Matrix (Fin 4) (Fin 4) NNReal)
        (show (1 / 2 : NNReal) ≠ 0 by norm_num)).eq_iff,
      (Matrix.map_injective Nat.cast_injective).eq_iff]

/-- `commuteMP p_matrix f` is the decidable integer equation `A · P_f = P_f · A`. -/
theorem commuteMP_p_iff (f : Fin 4 → Option (Fin 4)) :
    commuteMP p_matrix f ↔ Aadj * pfNat f = pfNat f * Aadj :=
  commuteMP_iff_intAdj (by ext i j; fin_cases i <;> fin_cases j <;> simp [p_matrix, Aadj]) f

/-- `commuteMP q_matrix f` is the decidable integer equation `B · P_f = P_f · B`. -/
theorem commuteMP_q_iff (f : Fin 4 → Option (Fin 4)) :
    commuteMP q_matrix f ↔ Badj * pfNat f = pfNat f * Badj :=
  commuteMP_iff_intAdj (by ext i j; fin_cases i <;> fin_cases j <;> simp [q_matrix, Badj]) f

set_option maxHeartbeats 4000000 in
-- `decide` enumerates all `5^4 = 625` partial functions `Fin 4 → Option (Fin 4)` and checks the
-- integer commutation from `commuteMP_p_iff`; the raised limits cover that kernel computation.
set_option maxRecDepth 100000 in
/-- The deterministic-partial centralizer of `{p_matrix}` is exactly `D₄ ∪ {∅}`: the eight
    dihedral symmetries of the 4-cycle (all total bijections) together with the empty partial
    function `∅`.  This is the partial-function first centralizer `A_p` of Counterexample 2:
    `D₄ ⊆ A_p` holds, and the only proper partial map commuting with `p` is `∅`. -/
theorem centralizer_p_matrix :
    Centralizer commuteMP {p_matrix} =
      ({![none, none, none, none], ![some 0, some 1, some 2, some 3],
        ![some 0, some 3, some 2, some 1], ![some 1, some 0, some 3, some 2],
        ![some 1, some 2, some 3, some 0], ![some 2, some 1, some 0, some 3],
        ![some 2, some 3, some 0, some 1], ![some 3, some 0, some 1, some 2],
        ![some 3, some 2, some 1, some 0]} : Set (Fin 4 → Option (Fin 4))) := by
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq,
             Set.mem_insert_iff]
  rw [commuteMP_p_iff]
  revert f
  decide

/-- The 33 partial functions making up `Centralizer commuteMP {q_matrix}`, as a `Finset`
    (a flat-decidable carrier keeps the `decide` below tractable): the empty partial function
    `∅`, plus every total map sending the antipodal pair `{0, 2}` to itself (`f 0, f 2` equal to
    `0, 2` in some order) with `f 1, f 3` arbitrary. -/
def qCentralizerSet : Finset (Fin 4 → Option (Fin 4)) :=
  {![none, none, none, none],
   ![some 0, some 0, some 2, some 0], ![some 0, some 0, some 2, some 1],
   ![some 0, some 0, some 2, some 2], ![some 0, some 0, some 2, some 3],
   ![some 0, some 1, some 2, some 0], ![some 0, some 1, some 2, some 1],
   ![some 0, some 1, some 2, some 2], ![some 0, some 1, some 2, some 3],
   ![some 0, some 2, some 2, some 0], ![some 0, some 2, some 2, some 1],
   ![some 0, some 2, some 2, some 2], ![some 0, some 2, some 2, some 3],
   ![some 0, some 3, some 2, some 0], ![some 0, some 3, some 2, some 1],
   ![some 0, some 3, some 2, some 2], ![some 0, some 3, some 2, some 3],
   ![some 2, some 0, some 0, some 0], ![some 2, some 0, some 0, some 1],
   ![some 2, some 0, some 0, some 2], ![some 2, some 0, some 0, some 3],
   ![some 2, some 1, some 0, some 0], ![some 2, some 1, some 0, some 1],
   ![some 2, some 1, some 0, some 2], ![some 2, some 1, some 0, some 3],
   ![some 2, some 2, some 0, some 0], ![some 2, some 2, some 0, some 1],
   ![some 2, some 2, some 0, some 2], ![some 2, some 2, some 0, some 3],
   ![some 2, some 3, some 0, some 0], ![some 2, some 3, some 0, some 1],
   ![some 2, some 3, some 0, some 2], ![some 2, some 3, some 0, some 3]}

set_option maxHeartbeats 4000000 in
-- `decide` enumerates all `5^4 = 625` partial functions and checks the integer commutation from
-- `commuteMP_q_iff`; the `Finset` target keeps the membership check flat-decidable.
set_option maxRecDepth 100000 in
/-- The deterministic-partial centralizer of `{q_matrix}` is `A_q` of Counterexample 2: the empty
    partial function `∅` together with the 32 total maps that fix the antipodal pair `{0, 2}`
    setwise (identity or swap on it) and are arbitrary on `{1, 3}`.  In particular it contains
    `ρ = (0 2)(1 3)`, the fact the text uses (`ρ ∈ A_q`). -/
theorem centralizer_q_matrix :
    Centralizer commuteMP {q_matrix} = ↑qCentralizerSet := by
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, Finset.mem_coe]
  rw [commuteMP_q_iff]
  revert f
  decide

/-- The partial-function bicommutant `B_p = {∅, id, ρ}` of Counterexample 2, where
    `ρ = (0 2)(1 3)`, as a `Finset` (the Kleisli-`Option` monoid is decidable, and a `Finset`
    target keeps the `decide` below tractable). -/
def pBicommutantSet : Finset (Fin 4 → Option (Fin 4)) :=
  {![none, none, none, none], ![some 0, some 1, some 2, some 3],
   ![some 2, some 3, some 0, some 1]}

/-- The partial-function bicommutant `B_q = {∅, id}` of Counterexample 2, as a `Finset`. -/
def qBicommutantSet : Finset (Fin 4 → Option (Fin 4)) :=
  {![none, none, none, none], ![some 0, some 1, some 2, some 3]}

/-- The partial-function centralizer of the kernel `p` equals that of its matrix `p_matrix`
    (`= A_p = D₄ ∪ {∅}`), via `commuteSP_ofMatrix_iff` and `centralizer_p_matrix`. -/
theorem centralizer_p_SP :
    Centralizer commuteSP {p} =
      ({![none, none, none, none], ![some 0, some 1, some 2, some 3],
        ![some 0, some 3, some 2, some 1], ![some 1, some 0, some 3, some 2],
        ![some 1, some 2, some 3, some 0], ![some 2, some 1, some 0, some 3],
        ![some 2, some 3, some 0, some 1], ![some 3, some 0, some 1, some 2],
        ![some 3, some 2, some 1, some 0]} : Set (Fin 4 → Option (Fin 4))) := by
  rw [← centralizer_p_matrix]
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  exact commuteSP_ofMatrix_iff p_matrix _ f

/-- The partial-function centralizer of the kernel `q` equals that of its matrix `q_matrix`
    (`= A_q = ↑qCentralizerSet`), via `commuteSP_ofMatrix_iff` and `centralizer_q_matrix`. -/
theorem centralizer_q_SP : Centralizer commuteSP {q} = ↑qCentralizerSet := by
  rw [← centralizer_q_matrix]
  ext f
  simp only [Centralizer, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  exact commuteSP_ofMatrix_iff q_matrix _ f

set_option maxHeartbeats 4000000 in
-- `decide` enumerates all `5^4 = 625` partial functions and checks Kleisli-commutation with each
-- of the `9` elements of `A_p`; the inner `∀ a ∈ A_p` is collapsed to a conjunction first so the
-- `Decidable` instance synthesizes, and the `Finset` target keeps membership flat-decidable.
set_option maxRecDepth 100000 in
/-- The partial-function **bicommutant** `B_p = hullSP {p}` of the kernel `p` (in the
    Kleisli-`Option` monoid) is exactly `{∅, id, ρ}` with `ρ = (0 2)(1 3)`, as claimed in
    Counterexample 2.  Rewrites `A_p = Centralizer commuteSP {p}` to its explicit `9`-element
    value (`centralizer_p_SP`); the centralizer is then a decidable computation. -/
theorem hullSP_p : hullSP {p} = ↑pBicommutantSet := by
  unfold hullSP
  rw [centralizer_p_SP]
  ext g
  rw [Submonoid.mem_carrier, Submonoid.mem_centralizer_iff, Finset.mem_coe]
  simp only [Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq]
  revert g
  decide

set_option maxHeartbeats 4000000 in
-- `decide` checks Kleisli-commutation of each of the `625` partial functions with the `33`
-- elements of `A_q`; the `Finset` bounded-∀ `decidableBAll` iterates just those `33`.
set_option maxRecDepth 100000 in
/-- The partial-function **bicommutant** `B_q = hullSP {q}` of the kernel `q` (in the
    Kleisli-`Option` monoid) is exactly `{∅, id}`: `A_q` is so large that its centralizer
    collapses to the trivial maps.  In particular `ρ = (0 2)(1 3) ∈ A_q` commutes with all of
    `B_q` — the key step in Counterexample 2 (combined with `ρ ∈ B_p`). -/
theorem hullSP_q : hullSP {q} = ↑qBicommutantSet := by
  unfold hullSP
  rw [centralizer_q_SP]
  ext g
  rw [Submonoid.mem_carrier, Submonoid.mem_centralizer_iff]
  simp only [Finset.mem_coe]
  revert g
  decide

set_option maxRecDepth 10000 in
/-- **Counterexample 2, the punchline.**  The partial-function bicommutants `B_p = hullSP {p}` and
    `B_q = hullSP {q}` commute elementwise (under Kleisli composition): every `f ∈ B_p = {∅,id,ρ}`
    commutes with every `g ∈ B_q = {∅, id}`.  Yet `p` and `q` do not commute
    (`matrices_not_commute`) — so the bicommutants commuting does **not** imply the underlying
    kernels commute, even in the partial setting. -/
theorem bicommutants_commute :
    ∀ f ∈ hullSP {p}, ∀ g ∈ hullSP {q}, f * g = g * f := by
  rw [hullSP_p, hullSP_q]
  simp only [Finset.mem_coe]
  decide

theorem from_hullSP_updates {m : Type*} (S : Set (m → SubProbability m)) :
    (OptionLensRange.from (hullSP S)).updates = hullSP S := by
  change (Submonoid.centralizer (Submonoid.centralizer (hullSP S)).carrier).carrier = hullSP S
  unfold hullSP
  exact Set.centralizer_centralizer_centralizer _

theorem theorem_negated : ¬ ∀ (m : Type) (p q : m → SubProbability m),
  (∀ f ∈ hullSP {p}, ∀ g ∈ hullSP {q}, f * g = g * f) → p * q = q * p := by
  intros h
  exact pq_not_commute (h _ p q bicommutants_commute)



end CE2
