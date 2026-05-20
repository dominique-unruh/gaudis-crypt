import PlonkLean.Semantics


/-!
# Discrete subprobability monad
-/

/-- Expected value of f under the distribution μ -/
noncomputable
def SubProbability.expected (μ : SubProbability a) (f : a → ENNReal) : ENNReal :=
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


-- TODO Let b depend on a?
theorem recursion_expected (F : (a → SubProbability b) →𝒄 (a → SubProbability b))
  (Ψ : (a → (b → ENNReal) →o ENNReal) →o (a → (b → ENNReal) →o ENNReal))
  (h : ∀ (X : a → SubProbability b),
      Ψ (fun (x : a) ↦ ⟨fun (f : b → ENNReal) ↦ (X x).expected f, by fun_prop⟩)
         = fun (x : a) ↦ ⟨fun (f : b → ENNReal) ↦ (F X x).expected f, by fun_prop⟩)
         (x : a) (f : b → ENNReal)
 : (F.lfp x).expected f = Ψ.lfp x f := by
  -- SubProbability b uses @Measure b ⊤ explicitly; provide ⊤ as a transparent instance
  -- so that lintegral lemmas can find MeasurableSpace b without causing an instance mismatch.
  letI : MeasurableSpace b := ⊤
  -- ΦF maps a postcondition g to its expected value under F.lfp, pointwise in the initial state.
  -- This is the expected-value transformer induced by the least fixed point of F.
  let ΦF : a → (b → ENNReal) →o ENNReal :=
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
    have hind : ∀ n g y, (F^[n] ⊥ y).expected g ≤ φ y g := by
      intro n; induction n with
      | zero =>
        -- F^0 ⊥ = ⊥, the zero measure; lintegral against zero is 0.
        intro g y
        simp only [SubProbability.expected,
          show (F^[0] ⊥ y).1 = (0 : @MeasureTheory.Measure b ⊤) from rfl,
          MeasureTheory.lintegral_zero_measure, zero_le]
      | succ n ih =>
        intro g y
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
          _ ≤ (Ψ φ) y g := Ψ.monotone (fun y' g' => ih g' y') y g
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
      rw [show (F.lfp y).1 = ⨆ n, (F^[n] ⊥ y).1 from rfl, lintegral_iSup_measure_nat hmono]
    rw [hmct]
    exact iSup_le (fun n => hind n g y)
  exact le_antisymm (hΦ_le x f) (hΨ_le x f)




/-!

# Stateful programs

-/

@[reducible]
def Program.Post s a := a × s → ENNReal
@[reducible]
def Program.Pre s := s → ENNReal

noncomputable
def Program.wp (prog : Program s a) (f : Program.Post s a) : Program.Pre s :=
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

-- TODO Let b,s depend on a?
theorem recursion_wp (F : (a → Program s b) →𝒄 (a → Program s b))
  (Ψ : (a → Program.Post s b →o Program.Pre s) →o (a → Program.Post s b →o Program.Pre s))
  (h : ∀ (X : a → Program s b) (f : Program.Post s b) (x : a),
      Ψ (fun (x : a) => ⟨fun (f : Program.Post s b) => (X x).wp f, by fun_prop⟩) x f
         = (F X x).wp f)
  (f : Program.Post s b) x
 : (recursion F x).wp f = Ψ.lfp x f := by
    ext st
    let curry : (a × s → SubProbability (b × s)) →𝒄 (a → Program s b) :=
      OmegaCompletePartialOrder.ContinuousHom.ofFun fun f a b => f (a, b)
    let uncurry :  (a → Program s b) →𝒄 (a × s → SubProbability (b × s)) :=
      OmegaCompletePartialOrder.ContinuousHom.ofFun fun f a => f a.1 a.2
    let F' : (a × s → SubProbability (b × s)) →𝒄 (a × s → SubProbability (b × s)) :=
      uncurry.comp (F.comp curry)
    let conv1 : (a × s → (b × s → ENNReal) →o ENNReal) →o (a → Program.Post s b →o Program.Pre s) :=
      ⟨fun φ (x : a) => ⟨fun (post : Program.Post s b) st => φ (x, st) post,
                                                      by fun_prop⟩, by fun_prop⟩
    let conv2 : (a → Program.Post s b →o Program.Pre s) →o (a × s → (b × s → ENNReal) →o ENNReal) :=
      ⟨fun φ (x, st) => ⟨fun post => φ x post st, by fun_prop⟩, by fun_prop⟩
    let Ψ' : (a × s → (b × s → ENNReal) →o ENNReal) →o (a × s → (b × s → ENNReal) →o ENNReal) :=
      conv2.comp (Ψ.comp conv1)
    have h X :
      Ψ' (fun x ↦ ⟨fun f ↦ (X x).expected f, by fun_prop⟩)
           = fun x ↦ ⟨fun f ↦ (F' X x).expected f, by fun_prop⟩ := by
      ext xst trafo
      exact congr_fun (h (curry X) trafo xst.1) xst.2
    calc
      (recursion F x).wp f st = (F.lfp x st).expected f := rfl
      _ = (F'.lfp (x,st)).expected f := by
        simp only [F']
        simp only [← ContinuousHom.map_lfp_comp uncurry (F.comp curry)]
        have aux : (F.comp curry).comp uncurry = F := by
          ext; simp [uncurry, curry]
        simp [aux, uncurry]
      _ = Ψ'.lfp (x,st) f  := by
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
  apply recursion_wp (while_iteration c p) (tailrec_wp (while_iteration_wp c p)) _ f ()
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
    simp [Program.get, wp_bind, wp_pure, wp_get_state]

theorem wp_set {α : Type} (v : Lens α s) (x : α) (f : Program.Post s Unit) :
    (Program.set v x).wp f = fun st => f ((), v.set x st) := by
    simp [Program.set, wp_bind, wp_get_state, wp_set_state]
