import GaudisCrypt.Language.Semantics

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

/-!
# Discrete subprobability monad
-/

/-- Expected value of f under the distribution μ -/
noncomputable
def _root_.GaudisCrypt.Language.Semantics.SubProbability.expected (μ : SubProbability a) (f : a → ENNReal) : ENNReal :=
  ∫⁻ x, f x ∂μ.1

theorem uniform_expected [Fintype a] [Nonempty a] (f : a → ENNReal) :
  SubProbability.uniform.expected f = ∑ x:a, f x / Fintype.card a
  := by
  letI : MeasurableSpace a := ⊤
  change ∫⁻ x, f x ∂(PMF.uniformOfFintype a).toMeasure = _
  rw [MeasureTheory.lintegral_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, ← div_eq_mul_inv]

theorem uniformOfFinset_expected {a : Type} [Fintype a] (fs : Finset a) (hs : fs.Nonempty)
    (f : a → ENNReal) :
    (SubProbability.uniformOfFinset fs hs).expected f = ∑ x ∈ fs, f x / fs.card := by
  classical
  letI : MeasurableSpace a := ⊤
  change ∫⁻ x, f x ∂(PMF.uniformOfFinset fs hs).toMeasure = _
  rw [MeasureTheory.lintegral_fintype]
  rw [show (fun x : a => f x * (PMF.uniformOfFinset fs hs).toMeasure {x})
        = fun x : a => if x ∈ fs then f x / (fs.card : ENNReal) else 0 from ?_]
  · rw [Finset.sum_ite_mem, Finset.univ_inter]
  · funext x
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        PMF.uniformOfFinset_apply]
    by_cases hx : x ∈ fs
    · rw [if_pos hx, if_pos hx, ← div_eq_mul_inv]
    · rw [if_neg hx, if_neg hx, mul_zero]

theorem expected_pure (x : a) : (pure x : SubProbability a).expected f = f x := by
  have h : (pure x : SubProbability a) = ⟨@MeasureTheory.Measure.dirac _ ⊤ x, _⟩ := rfl
  simp [SubProbability.expected, h]

theorem expectation_indicator (mu : SubProbability a) (s : Set a) c :
  mu.expected (s.indicator (fun _ => c)) = c * mu.ofEvent s := by
    letI : MeasurableSpace a := ⊤
    have hfin : mu.1 s ≠ (⊤ : ENNReal) :=
      ((MeasureTheory.measure_mono (Set.subset_univ s)).trans mu.2).trans_lt
        ENNReal.one_lt_top |>.ne
    simp only [SubProbability.expected, SubProbability.ofEvent, ENNReal.coe_toNNReal hfin]
    exact MeasureTheory.lintegral_indicator_const (show MeasurableSet s from trivial) c

@[fun_prop]
theorem expectation_mono [Preorder i]
  (μ : i → SubProbability a) (f : i → a → ENNReal)
  (hμ : Monotone μ) (hf : Monotone f) :
  Monotone fun x => (μ x).expected (f x) := by
    intro x y hxy; exact MeasureTheory.lintegral_mono' (hμ hxy) (hf hxy)


theorem recursion_expected {b : a → Type}
  (F : ((x : a) → SubProbability (b x)) →𝒄 ((x : a) → SubProbability (b x)))
  (Ψ : ((x : a) → (b x → ENNReal) →o ENNReal) →o ((x : a) → (b x → ENNReal) →o ENNReal))
  (h : ∀ (X : (x : a) → SubProbability (b x)),
      Ψ (fun (x : a) ↦ ⟨fun (f : b x → ENNReal) ↦ (X x).expected f, by fun_prop⟩)
         = fun (x : a) ↦ ⟨fun (f : b x → ENNReal) ↦ (F X x).expected f, by fun_prop⟩)
  (x : a) (f : b x → ENNReal)
 : (F.lfp x).expected f = Ψ.lfp x f := by
  -- ΦF maps a postcondition g to its expected value under F.lfp, pointwise in the initial state.
  -- This is the expected-value transformer induced by the least fixed point of F.
  let ΦF : (x : a) → (b x → ENNReal) →o ENNReal :=
    fun y ↦ ⟨fun g => (F.lfp y).expected g, by fun_prop⟩
  -- ΦF is a fixed point of Ψ: apply h at F.lfp, then use F(F.lfp) = F.lfp (the lfp equation).
  have hfixed : Ψ ΦF = ΦF := by
    funext y; ext g
    have h1 := DFunLike.congr_fun (congr_fun (h F.lfp) y) g
    rw [(ContinuousHom.lfp_isLfp F).1] at h1
    exact h1
  -- Easy direction: Ψ.lfp ≤ ΦF because ΦF is a fixed point and Ψ.lfp is the least one.
  have hΨ_le : Ψ.lfp ≤ ΦF := Ψ.lfp_le_fixed hfixed
  -- Hard direction: ΦF ≤ Ψ.lfp, i.e. ΦF is below every pre-fixed point of Ψ.
  -- We show this by induction on the Kleene iterates F^n ⊥, then take the supremum via MCT.
  have hΦ_le : ΦF ≤ Ψ.lfp := by
    apply OrderHom.le_lfp
    intro φ hφ  -- φ is an arbitrary pre-fixed point: Ψ φ ≤ φ
    -- Induction: each finite iterate F^n ⊥ already satisfies E[g | F^n ⊥ y] ≤ φ g y.
    have hind : ∀ n (y : a) (g : b y → ENNReal), (F^[n] ⊥ y).expected g ≤ φ y g := by
      intro n; induction n with
      | zero =>
        -- F^0 ⊥ = ⊥, the zero measure; lintegral against zero is 0.
        intro y g
        simp only [SubProbability.expected,
          show (F^[0] ⊥ y).1 = (0 : @MeasureTheory.Measure (b y) ⊤) from rfl,
          MeasureTheory.lintegral_zero_measure, zero_le]
      | succ n ih =>
        intro y g
        -- hstep: Ψ applied to the transformer of F^n ⊥ equals the transformer of F(F^n ⊥).
        have hstep := h (F^[n] ⊥)
        -- Rewrite F^(n+1) ⊥ as F applied to F^n ⊥.
        have hiter : (F^[n+1] ⊥ y).expected g = (F (F^[n] ⊥) y).expected g :=
          congrArg (SubProbability.expected · g)
                (congr_fun (Function.iterate_succ_apply' (⇑F) n ⊥) y)
        rw [hiter]
        -- Use hstep to rewrite the expected value, then apply monotonicity of Ψ (induction
        -- hypothesis) and the pre-fixed point condition φ.
        calc (F (F^[n] ⊥) y).expected g
            = Ψ (fun y' ↦ ⟨fun g' => (F^[n] ⊥ y').expected g', by fun_prop⟩) y g :=
                (DFunLike.congr_fun (congr_fun hstep y) g).symm
          _ ≤ (Ψ φ) y g := Ψ.monotone (fun y' g' => ih y' g') y g
          _ ≤ φ y g := hφ y g
    -- Pass to the limit: F.lfp = ⨆ n, F^n ⊥ (Kleene's theorem), so by MCT the expected value
    -- under F.lfp equals ⨆ n, E[g | F^n ⊥ y], and each term is ≤ φ g y by hind.
    intro y g
    change (F.lfp y).expected g ≤ φ y g
    have hmono : Monotone fun n => (F^[n] ⊥ y).1 :=
      fun m n hmn => (Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _) hmn) y
    have hmct : (F.lfp y).expected g = ⨆ n, (F^[n] ⊥ y).expected g := by
      simp only [SubProbability.expected]
      -- (F.lfp y).1 = ⨆ n, (F^n ⊥ y).1 holds by rfl from the OCPO ωSup definition.
      letI : MeasurableSpace (b y) := ⊤
      rw [show (F.lfp y).1 = ⨆ n, (F^[n] ⊥ y).1 from rfl, lintegral_iSup_measure_nat hmono]
    rw [hmct]
    exact iSup_le (fun n => hind n y g)
  exact le_antisymm (hΦ_le x f) (hΨ_le x f)




/-!

# Stateful programs

-/

@[reducible]
def Program.Post s a := a × s → ENNReal
@[reducible]
def Program.Pre s := s → ENNReal

noncomputable
def _root_.GaudisCrypt.Language.Semantics.Program.wp (prog : Program s a) (f : Program.Post s a) : Program.Pre s :=
  fun st => (prog st).expected f

theorem final_probability_wp [DecidableEq a] (prog : Program s a) (st : s) (x : a) :
  ↑(prog.finalProb1 st x) = prog.wp (fun (y, _) => if y = x then 1 else 0) st := by
  symm
  calc
    prog.wp (fun (y, _) => if y = x then 1 else 0) st
        = prog.wp (({x} ×ˢ ⊤).indicator (fun _ => 1)) st := by
      congr 1; ext ⟨y, z⟩; simp [Set.indicator]
    _ = (prog st).ofEvent ({x} ×ˢ Set.univ) := by
      simp [Program.wp, expectation_indicator]
    _ = ↑(prog.finalProb1 st x) := by
      simp [Program.finalProb1, Program.finalProb]


theorem final_probability_wp' [DecidableEq a] (prog : Program s a) (st : s) (x : a) :
  prog.finalProb1 st x = (prog.wp (fun (y, _) => if y = x then 1 else 0) st).toNNReal :=
    (ENNReal.toNNReal_coe _).symm.trans (congrArg ENNReal.toNNReal (final_probability_wp prog st x))

theorem wp_lift {s : Type} (μ : SubProbability a) (f : Program.Post s a) :
    μ.toProgram.wp f = fun st => μ.expected (fun x => f (x, st)) := by
  letI : MeasurableSpace a := ⊤
  letI : MeasurableSpace s := ⊤
  letI : MeasurableSpace (a × s) := ⊤
  ext st
  change ∫⁻ x, f x ∂(MeasureTheory.Measure.bind μ.1
        (fun y => MeasureTheory.Measure.dirac (y, st))) = ∫⁻ x, f (x, st) ∂μ.1
  rw [MeasureTheory.Measure.bind_dirac_eq_map _ measurable_from_top,
      MeasureTheory.lintegral_map measurable_from_top measurable_from_top]

theorem wp_uniform [h : Fintype a] [h : Nonempty a] (f : Program.Post s a) :
  Program.uniform.wp f = (fun s => ∑ i:a, f (i,s) / Fintype.card a) := by
  simp [Program.uniform, wp_lift, uniform_expected]

theorem wp_uniformOfFinset {st a : Type} [Fintype a] (fs : Finset a) (hs : fs.Nonempty)
    (f : Program.Post st a) :
    (Program.uniformOfFinset fs hs).wp f = (fun σ => ∑ i ∈ fs, f (i, σ) / fs.card) := by
  simp [Program.uniformOfFinset, wp_lift, uniformOfFinset_expected]


theorem wp_bind {α β : Type} (prog : Program s α) (f : α → Program s β)
    (g : Program.Post s β) :
    (prog >>= f).wp g = prog.wp (fun (a, s') => (f a).wp g s') := by
  letI : MeasurableSpace (α × s) := ⊤
  letI : MeasurableSpace (β × s) := ⊤
  ext st
  change ∫⁻ x, g x ∂((prog >>= f) st).1
      = ∫⁻ x, (∫⁻ y, g y ∂((f x.1) x.2).1) ∂(prog st).1
  have heq : ((prog >>= f) st).1
      = MeasureTheory.Measure.bind (prog st).1 (fun p => ((f p.1) p.2).1) := rfl
  rw [heq, MeasureTheory.Measure.lintegral_bind measurable_from_top.aemeasurable
        measurable_from_top.aemeasurable]

theorem wp_pure {s α : Type} (x : α) (f : Program.Post s α) :
    (pure x : Program s α).wp f = fun st => f (x, st) := by
    have h : (pure x : Program s α) = fun s => pure (x, s) := rfl
             -- Can't we somehow unfold `pure x` without auxiliary def?
    ext
    simp [h, Program.wp, expected_pure]

/-! ### Postcondition combinators for `wp`

  Basic monotonicity, the `0`-postcondition, the constant-postcondition bound
  (from sub-probability mass), linearity, and constant scaling. These are
  pure consequences of `wp = lintegral against the SubProb measure`. -/

/-- Pointwise monotonicity of `wp` in the postcondition. -/
theorem Program.wp_le_wp_of_le {s a : Type} (p : Program s a)
    (F G : Program.Post s a) (h : ∀ x, F x ≤ G x) (σ : s) :
    p.wp F σ ≤ p.wp G σ := by
  letI : MeasurableSpace (a × s) := ⊤
  exact MeasureTheory.lintegral_mono h

/-- `wp` of the constant `0` postcondition is `0`. -/
theorem Program.wp_zero_post {s a : Type} (p : Program s a) (σ : s) :
    p.wp (fun _ => (0 : ENNReal)) σ = 0 := by
  letI : MeasurableSpace (a × s) := ⊤
  exact MeasureTheory.lintegral_zero

/-- `wp` of the constant `c` postcondition is at most `c`, since the underlying
    measure is a sub-probability (total mass ≤ 1). -/
theorem Program.wp_const_le {s a : Type} (p : Program s a) (c : ENNReal) (σ : s) :
    p.wp (fun _ => c) σ ≤ c := by
  letI : MeasurableSpace (a × s) := ⊤
  show ∫⁻ _, c ∂(p σ).1 ≤ c
  rw [MeasureTheory.lintegral_const]
  calc c * (p σ).1 Set.univ ≤ c * 1 := by gcongr; exact (p σ).2
    _ = c := mul_one _

/-- Linearity of `wp` in the postcondition. -/
theorem Program.wp_add {s a : Type} (p : Program s a)
    (F G : Program.Post s a) (σ : s) :
    p.wp (fun aσ : a × s => F aσ + G aσ) σ = p.wp F σ + p.wp G σ := by
  letI : MeasurableSpace (a × s) := ⊤
  show ∫⁻ x, (F x + G x) ∂(p σ).1 = (∫⁻ x, F x ∂(p σ).1) + (∫⁻ x, G x ∂(p σ).1)
  exact MeasureTheory.lintegral_add_left measurable_from_top G

/-- Constant scaling of `wp`. -/
theorem Program.wp_const_mul {s a : Type} (p : Program s a)
    (c : ENNReal) (F : Program.Post s a) (σ : s) :
    p.wp (fun aσ : a × s => c * F aσ) σ = c * p.wp F σ := by
  letI : MeasurableSpace (a × s) := ⊤
  show ∫⁻ x, c * F x ∂(p σ).1 = c * ∫⁻ x, F x ∂(p σ).1
  exact MeasureTheory.lintegral_const_mul c measurable_from_top

/-- `wp` commutes with finite sums of postconditions. -/
theorem Program.wp_finset_sum {s α β : Type} [Fintype β]
    (p : Program s α) (F : β → α × s → ENNReal) (σ : s) :
    p.wp (fun aσ => ∑ b : β, F b aσ) σ = ∑ b : β, p.wp (F b) σ := by
  letI : MeasurableSpace (α × s) := ⊤
  show ∫⁻ aσ, (∑ b, F b aσ) ∂(p σ).1 = ∑ b, ∫⁻ aσ, F b aσ ∂(p σ).1
  exact MeasureTheory.lintegral_finset_sum _ (fun _ _ => measurable_from_top)

theorem wp_ite {α : Type} (b : Bool) (p1 p2 : Program s α)
    (f : α × s → ENNReal) (st : s) :
    (if b then p1 else p2).wp f st = if b then p1.wp f st else p2.wp f st := by
  cases b <;> rfl

theorem wp_set_state (st' : s) (f : Unit × s → ENNReal) (st : s) :
    Program.wp (StateT.set st' : Program s Unit) f st = f ((), st') := by
           -- Why doesn't (...).wp syntax work?
  simp [Program.wp, StateT.set, expected_pure]

theorem wp_get_state (f : Program.Post s s) :
    Program.wp (StateT.get) f = fun st => f (st, st) := by
  ext
  simp [Program.wp, StateT.get, expected_pure]

@[fun_prop]
theorem wp_mono [Preorder i]
  (μ : i → Program s a) (f : i → Program.Post s a)
  (hμ : Monotone μ) (hf : Monotone f) :
  Monotone fun x => (μ x).wp (f x) := by
    intro x y hxy st; exact MeasureTheory.lintegral_mono' (hμ hxy st) (hf hxy)

theorem recursion_wp {s : a → Type} {b : a → Type}
  (F : ((x : a) → Program (s x) (b x)) →𝒄 ((x : a) → Program (s x) (b x)))
  (Ψ : ((x : a) → Program.Post (s x) (b x) →o Program.Pre (s x)) →o
       ((x : a) → Program.Post (s x) (b x) →o Program.Pre (s x)))
  (h : ∀ (X : (x : a) → Program (s x) (b x)) (x : a) (f : Program.Post (s x) (b x)),
      Ψ (fun (x : a) => ⟨fun (f : Program.Post (s x) (b x)) => (X x).wp f, by fun_prop⟩) x f
         = (F X x).wp f)
  (x : a) (f : Program.Post (s x) (b x))
 : (recursion F x).wp f = Ψ.lfp x f := by
    ext st
    let curry : ((xst : Σ x : a, s x) → SubProbability (b xst.1 × s xst.1)) →𝒄
                ((x : a) → Program (s x) (b x)) :=
      OmegaCompletePartialOrder.ContinuousHom.ofFun fun f x st => f ⟨x, st⟩
    let uncurry : ((x : a) → Program (s x) (b x)) →𝒄
                  ((xst : Σ x : a, s x) → SubProbability (b xst.1 × s xst.1)) :=
      OmegaCompletePartialOrder.ContinuousHom.ofFun fun f xst => f xst.1 xst.2
    let F' : ((xst : Σ x : a, s x) → SubProbability (b xst.1 × s xst.1)) →𝒄
             ((xst : Σ x : a, s x) → SubProbability (b xst.1 × s xst.1)) :=
      uncurry.comp (F.comp curry)
    let conv1 : ((xst : Σ x : a, s x) → (b xst.1 × s xst.1 → ENNReal) →o ENNReal) →o
                ((x : a) → Program.Post (s x) (b x) →o Program.Pre (s x)) :=
      ⟨fun φ (x : a) => ⟨fun (post : Program.Post (s x) (b x)) st => φ ⟨x, st⟩ post,
                          fun _ _ hle st => (φ ⟨x, st⟩).monotone hle⟩,
       fun _ _ hle x post st => hle ⟨x, st⟩ post⟩
    let conv2 : ((x : a) → Program.Post (s x) (b x) →o Program.Pre (s x)) →o
                ((xst : Σ x : a, s x) → (b xst.1 × s xst.1 → ENNReal) →o ENNReal) :=
      ⟨fun φ xst => ⟨fun post => φ xst.1 post xst.2,
                      fun _ _ hle => (φ xst.1).monotone hle xst.2⟩,
       fun _ _ hle xst post => hle xst.1 post xst.2⟩
    let Ψ' : ((xst : Σ x : a, s x) → (b xst.1 × s xst.1 → ENNReal) →o ENNReal) →o
             ((xst : Σ x : a, s x) → (b xst.1 × s xst.1 → ENNReal) →o ENNReal) :=
      conv2.comp (Ψ.comp conv1)
    have h X :
      Ψ' (fun xst ↦ ⟨fun f ↦ (X xst).expected f, by fun_prop⟩)
           = fun xst ↦ ⟨fun f ↦ (F' X xst).expected f, by fun_prop⟩ := by
      ext xst trafo
      exact congr_fun (h (curry X) xst.1 trafo) xst.2
    calc
      (recursion F x).wp f st = (F.lfp x st).expected f := rfl
      _ = (F'.lfp ⟨x, st⟩).expected f := by
        simp only [F']
        simp only [← ContinuousHom.map_lfp_comp uncurry (F.comp curry)]
        have aux : (F.comp curry).comp uncurry = F := by
          ext; simp [uncurry, curry]
        simp [aux, uncurry]
      _ = Ψ'.lfp ⟨x, st⟩ f  := by
        apply recursion_expected; intro; apply h
      _ = Ψ.lfp x f st := by
        simp only [Ψ']
        have aux : (Ψ.comp conv1).comp conv2 = Ψ := by
          ext f x; simp only [conv1, conv2]; trivial
        rw [← OrderHom.map_lfp_comp conv2 (Ψ.comp conv1), aux]
        simp [conv2]

/-- For tailrecursive programs (in particular while-loops), we can write
    the wp iteration function (argument to `recursion_wp[_simple]`) as
    `tailrec_wp something`. In this case, we'll have some nicer properties.
    (See `while_wp_unfold` below for example.) -/
def tailrec_wp [CompleteLattice b] [CompleteLattice c] (Φ : a → b →o (c →o c)) :
  (a → b →o c) →o (a → b →o c) :=
  ⟨fun trafo x => ⟨fun (post:b) => Φ x post (trafo x post), by fun_prop⟩,
   by fun_prop⟩

noncomputable
def while_iteration_wp (c : Program s Bool) (p : Program s Unit) (_ : Unit) :
  (Program.Post s Unit) →o (Program.Pre s →o Program.Pre s) :=
  ⟨fun post => ⟨fun fp => c.wp (fun (b, st) =>
                  if b then
                    p.wp (fun ((),st) => fp st) st
                  else
                    post ((), st)),
     by fun_prop⟩,
   by fun_prop⟩

-- TODO allow types to depend on a
theorem wp_recursion_tailrec_simplify [CompleteLattice b] [CompleteLattice c]
    (Φ : a → b →o (c →o c)) post x :
    (tailrec_wp Φ).lfp x post = (Φ x post).lfp := by
  apply le_antisymm
  · have rhs_fp : tailrec_wp Φ (fun x' => ⟨fun p => (Φ x' p).lfp, by fun_prop⟩) =
                  fun x' => ⟨fun p => (Φ x' p).lfp, by fun_prop⟩ := by
      ext x' p; exact OrderHom.map_lfp (Φ x' p)
    exact (tailrec_wp Φ).lfp_le_fixed rhs_fp x post
  · apply (Φ x post).lfp_le_fixed
    exact DFunLike.congr_fun (congr_fun (OrderHom.map_lfp (tailrec_wp Φ)) x) post

theorem wp_while' :
  (while_loop c p).wp f = (tailrec_wp (while_iteration_wp c p)).lfp () f := by
  simp only [while_loop]
  apply recursion_wp (while_iteration c p) (tailrec_wp (while_iteration_wp c p)) _ () f
  simp [while_iteration, wp_bind, wp_ite, wp_pure, tailrec_wp, while_iteration_wp]

theorem wp_while :
  (while_loop c p).wp f = (while_iteration_wp c p () f).lfp := by
  simp [wp_while', wp_recursion_tailrec_simplify]

theorem wp_while_unfold (b : Program s Bool) (body : Program s Unit) (post) :
    (while_loop b body).wp post = b.wp fun (x,st) ↦
      if x then body.wp (fun (_,st) ↦ (while_loop b body).wp post st) st else post ((), st)
  := by calc
      _ = (while_iteration_wp b body () post).lfp := by simp [wp_while]
      _ = while_iteration_wp b body () post ((while_iteration_wp b body () post).lfp) := by simp
      _ = while_iteration_wp b body () post ((while_loop b body).wp post) := by simp only [wp_while]
      _ = _ := by simp [while_iteration_wp]

-- Loop invariant rule: if I is a pre-fixed-point of Ψ, then wp_while_val ≤ I.
-- Concretely: if (∀ s, if b s then wp body (fun (_, s') => I s') s else f ((), s)) ≤ I s,
-- then the loop's wp is bounded by I.
theorem wp_while_invariant (b : Program s Bool) (body : Program s Unit)
    (I : Program.Pre s) (f : Program.Post s Unit)
    (h : (b.wp fun (x, st) ↦ if x then body.wp (fun (_, st) ↦ I st) st else f ((), st))
         <= I) :
    (while_loop b body).wp f ≤ I := by
    simp only [wp_while]
    apply (while_iteration_wp b body () f).lfp_le h

theorem wp_get {α : Type} (v : Lens α s) (f : Program.Post s α) :
    (Program.get v).wp f = fun st => f (v.get st, st) := by
    simp [Program.get, wp_bind, wp_pure, wp_get_state, AsGetter.toG]

theorem wp_set {α : Type} (v : Lens α s) (x : α) (f : Program.Post s Unit) :
    (Program.set v x).wp f = fun st => f ((), v.set x st) := by
    simp [Program.set, wp_bind, wp_get_state, wp_set_state, AsSetter.toS]

/-! ## Mass-1 (full probability) lemmas

A program `p` has *mass 1* at state `σ` iff `p.wp (fun _ => 1) σ = 1`, i.e.,
the total sub-probability mass produced by `p` at `σ` equals 1. This holds for
every "real" probabilistic operation in the language (pure, get, set, uniform,
…), and is preserved by `>>=`. The lemmas below let proofs about
identical-until-bad analyses and similar mass-conservation arguments compose
mass-1 facts cleanly. -/

/-- `pure x` has mass 1. -/
theorem Program.pure_mass_one {s α : Type} (x : α) (σ : s) :
    (pure x : Program s α).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_pure]

/-- `Program.get L` has mass 1. -/
theorem Program.get_mass_one {s α : Type} (L : Lens α s) (σ : s) :
    (Program.get L).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_get]

/-- `Program.set L v` has mass 1. -/
theorem Program.set_mass_one {s α : Type} (L : Lens α s) (v : α) (σ : s) :
    (Program.set L v).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_set]

/-- `Program.uniform` has mass 1 (the uniform distribution sums to 1 over its
    finite, non-empty support). -/
theorem Program.uniform_mass_one {s α : Type} [Fintype α] [Nonempty α] (σ : s) :
    (Program.uniform : Program s α).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_uniform]
  show ∑ _i : α, (1 : ENNReal) / (Fintype.card α : ENNReal) = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_div_assoc, mul_one,
      ENNReal.div_self
        (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0))
        (ENNReal.natCast_ne_top _)]

/-- `Program.uniformOfFinset` has mass 1. -/
theorem Program.uniformOfFinset_mass_one {s α : Type} [Fintype α]
    (fs : Finset α) (hs : fs.Nonempty) (σ : s) :
    (Program.uniformOfFinset fs hs).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_uniformOfFinset]
  show ∑ _i ∈ fs, (1 : ENNReal) / (fs.card : ENNReal) = 1
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_one,
      ENNReal.div_self
        (by exact_mod_cast (Finset.card_ne_zero.mpr hs))
        (ENNReal.natCast_ne_top _)]

/-- **Mass-1 composes through `>>=`**: if `p` and every `k a` have mass 1, then
    so does `p >>= k`. The workhorse for chaining mass-conservation facts
    through composite programs. -/
theorem Program.mass_bind {s α β : Type}
    (p : Program s α) (k : α → Program s β)
    (hp : ∀ σ, p.wp (fun _ => (1 : ENNReal)) σ = 1)
    (hk : ∀ a σ, (k a).wp (fun _ => (1 : ENNReal)) σ = 1)
    (σ : s) :
    (p >>= k).wp (fun _ => (1 : ENNReal)) σ = 1 := by
  rw [wp_bind]
  have h_post : (fun aσ : α × s => (k aσ.1).wp (fun _ => (1 : ENNReal)) aσ.2)
              = fun _ : α × s => (1 : ENNReal) := by
    funext aσ
    exact hk aσ.1 aσ.2
  rw [h_post]
  exact hp σ
