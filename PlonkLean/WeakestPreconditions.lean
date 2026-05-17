import PlonkLean.Semantics


/-!
# Discrete subprobability monad
-/

/-- Expected value of f under the distribution μ -/
noncomputable
def SubProbability.expected (μ : SubProbability a) (f : a → ENNReal) : ENNReal :=
  ∫⁻ x, f x ∂μ.1

theorem uniform_expected [Fintype a] [Nonempty a] (f: a → ENNReal) :
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

theorem expectation_indicator (mu: SubProbability a) (s : Set a) c :
  mu.expected (s.indicator (fun _ => c)) = c * mu.ofEvent s := by
    simp [SubProbability.expected, SubProbability.ofEvent]
    sorry

theorem expectation_mono1 : Monotone fun (p : SubProbability a) => p.expected := by
  sorry

theorem expectation_mono2 (p: SubProbability a) : Monotone fun f => p.expected f := by
  sorry

theorem recursion_expected (F : (a → SubProbability b) →𝒄 (a → SubProbability b))
  (Ψ : ((b → ENNReal) →o (a → ENNReal)) →o ((b → ENNReal) →o (a → ENNReal)))
  (h : ∀ (X : a → SubProbability b),
      Ψ ⟨fun (f : b → ENNReal) (x : a) => (X x).expected f,
          fun _ _ hf x => expectation_mono2 (X x) hf⟩
         = ⟨fun (f : b → ENNReal) (x : a) => (F X x).expected f,
             fun _ _ hf x => expectation_mono2 (F X x) hf⟩)
         (x : a) (f : b → ENNReal)
 : (F.lfp x).expected f = Ψ.lfp f x := by
  -- SubProbability b uses @Measure b ⊤ explicitly; provide ⊤ as a transparent instance
  -- so that lintegral lemmas can find MeasurableSpace b without causing an instance mismatch.
  letI : MeasurableSpace b := ⊤
  -- ΦF maps a postcondition g to its expected value under F.lfp, pointwise in the initial state.
  -- This is the expected-value transformer induced by the least fixed point of F.
  let ΦF : (b → ENNReal) →o (a → ENNReal) :=
    ⟨fun g y => (F.lfp y).expected g, fun g1 g2 hg y => expectation_mono2 (F.lfp y) hg⟩
  -- ΦF is a fixed point of Ψ: apply h at F.lfp, then use F(F.lfp) = F.lfp (the lfp equation).
  have hfixed : Ψ ΦF = ΦF := by
    apply OrderHom.ext; funext g y
    have h1 := congr_fun (congr_fun (congrArg DFunLike.coe (h F.lfp)) g) y
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
    have hind : ∀ n g y, (F^[n] ⊥ y).expected g ≤ φ g y := by
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
          congrArg (SubProbability.expected · g) (congr_fun (Function.iterate_succ_apply' (⇑F) n ⊥) y)
        rw [hiter]
        -- Use hstep to rewrite the expected value, then apply monotonicity of Ψ (induction
        -- hypothesis) and the pre-fixed point condition φ.
        calc (F (F^[n] ⊥) y).expected g
            = (Ψ ⟨fun g' y' => (F^[n] ⊥ y').expected g', fun g1 g2 hg y' => expectation_mono2 (F^[n] ⊥ y') hg⟩) g y :=
                (congr_fun (congr_fun (congrArg DFunLike.coe hstep) g) y).symm
          _ ≤ (Ψ φ) g y := Ψ.monotone (fun g' y' => ih g' y') g y
          _ ≤ φ g y := hφ g y
    -- Pass to the limit: F.lfp = ⨆ n, F^n ⊥ (Kleene's theorem), so by MCT the expected value
    -- under F.lfp equals ⨆ n, E[g | F^n ⊥ y], and each term is ≤ φ g y by hind.
    intro g y
    show (F.lfp y).expected g ≤ φ g y
    have hmono : Monotone fun n => (F^[n] ⊥ y).1 :=
      fun m n hmn => (Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _) hmn) y
    have hmct : (F.lfp y).expected g = ⨆ n, (F^[n] ⊥ y).expected g := by
      simp only [SubProbability.expected]
      -- (F.lfp y).1 = ⨆ n, (F^n ⊥ y).1 holds by rfl from the OCPO ωSup definition.
      rw [show (F.lfp y).1 = ⨆ n, (F^[n] ⊥ y).1 from rfl, lintegral_iSup_measure_nat hmono]
    rw [hmct]
    exact iSup_le (fun n => hind n g y)
  exact le_antisymm (hΦ_le f x) (hΨ_le f x)




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
    prog.wp (fun (y, _) => if y = x then 1 else 0) st = prog.wp (({x} ×ˢ ⊤).indicator (fun _ => 1)) st := by
      simp [Program.wp]
      sorry
    _ = (prog st).ofEvent ({x} ×ˢ Set.univ) := by
      simp [Program.wp, expectation_indicator]
    _ = ↑(prog.finalProb1 st x) := by
      simp [Program.finalProb1, Program.finalProb]


theorem final_probability_wp' [DecidableEq a] (prog : Program s a) (st : s) (x : a) :
  prog.finalProb1 st x = (prog.wp (fun (y, _) => if y = x then 1 else 0) st).toNNReal :=
    sorry

theorem wp_lift (μ : SubProbability a) : μ.toProgram.wp f = fun st => μ.expected (fun x => f (x,st))
  := sorry

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
    have h : (pure x : Program s α) = fun s => pure (x, s) := rfl  -- Can't we somehow unfold `pure x` without auxiliary def?
    ext
    simp [h, Program.wp, expected_pure]

theorem wp_ite {α : Type} (b : Bool) (p1 p2 : Program s α)
    (f : α × s → ENNReal) (st : s) :
    (if b then p1 else p2).wp f st = if b then p1.wp f st else p2.wp f st := by
  cases b <;> rfl

theorem wp_set (st' : s) (f : Unit × s → ENNReal) (st : s) :
    Program.wp (StateT.set st' : Program s Unit) f st = f ((), st') := by  -- Why doesn't (...).wp syntax work?
  simp [Program.wp, StateT.set, expected_pure]

theorem wp_get (f : Program.Post s s) :
    Program.wp (StateT.get) f = fun st => f (st, st) := by
  ext
  simp [Program.wp, StateT.get, expected_pure]

theorem wp_mono : Monotone fun (p : Program s a) => p.wp := by
  intro p q hpq f st
  simp only [Program.wp, SubProbability.expected]
  exact MeasureTheory.lintegral_mono' (hpq st) le_rfl

private theorem recursion_wp_mono {X : a → Program s b} :
  Monotone fun f x ↦ (X x).wp f := by
  sorry -- Use wp_mono

theorem recursion_wp (F : (a → Program s b) →𝒄 (a → Program s b))
  (Ψ : ((Program.Post s b) →o (a → Program.Pre s)) →o ((Program.Post s b) →o (a → Program.Pre s)))
  (h : ∀ (X : a → Program s b),
      Ψ ⟨fun (f : Program.Post s b) (x : a) => (X x).wp f, recursion_wp_mono⟩
         = ⟨fun (f : Program.Post s b) (x : a) => (F X x).wp f, recursion_wp_mono⟩)
         (x : a) (f : Program.Post s b)
 : (F.lfp x).wp f = Ψ.lfp f x := by
    ext st
    let curry : (a × s → SubProbability (b × s)) →𝒄 (a → Program s b) :=
      OmegaCompletePartialOrder.ContinuousHom.ofFun fun f a b => f (a, b)
    let uncurry :  (a → Program s b) →𝒄 (a × s → SubProbability (b × s)) :=
      OmegaCompletePartialOrder.ContinuousHom.ofFun fun f a => f a.1 a.2
    let F' : (a × s → SubProbability (b × s)) →𝒄 (a × s → SubProbability (b × s)) :=
      uncurry.comp (F.comp curry)
    let conv1 : ((b × s → ENNReal) →o (a × s → ENNReal)) →o ((b × s → ENNReal) →o (a → s → ENNReal)) :=
      ⟨fun φ => ⟨fun g => Function.curry (φ g), fun g1 g2 hg a' b' => φ.monotone hg (a', b')⟩,
       fun φ1 φ2 hφ g a' b' => hφ g (a', b')⟩
    let conv2 : ((b × s → ENNReal) →o (a → s → ENNReal)) →o ((b × s → ENNReal) →o (a × s → ENNReal)) :=
      ⟨fun φ => ⟨fun g => Function.uncurry (φ g), fun g1 g2 hg ⟨a', b'⟩ => φ.monotone hg a' b'⟩,
       fun φ1 φ2 hφ g ⟨a', b'⟩ => hφ g a' b'⟩
    let Ψ' : ((b × s → ENNReal) →o (a × s → ENNReal)) →o ((b × s → ENNReal) →o (a × s → ENNReal)) :=
      conv2.comp (Ψ.comp conv1)
      -- ⟨fun f => conv2 (Ψ (conv1 f)), fun f1 f2 hf g ⟨a, b⟩ => Ψ.monotone (fun g' a' b' => hf g' (a', b')) g a b⟩
    have h X : Ψ' ⟨fun f x ↦ (X x).expected f, fun g1 g2 hg x => MeasureTheory.lintegral_mono hg⟩ =
              ⟨fun f x ↦ (F' X x).expected f, fun g1 g2 hg x => MeasureTheory.lintegral_mono hg⟩ := by
      let X' : a → Program s b := curry X
      have lhs : conv1 ⟨fun f x ↦ (X x).expected f, fun g1 g2 hg x => MeasureTheory.lintegral_mono hg⟩ =
          ⟨fun f x ↦ (X' x).wp f, recursion_wp_mono⟩ := by
        apply OrderHom.ext; funext g a' b'; rfl
      change conv2 (Ψ (conv1 ⟨fun f x ↦ (X x).expected f, _⟩)) = ⟨fun f x ↦ (F' X x).expected f, _⟩
      rw [lhs, h X']
      apply OrderHom.ext; funext g x; rfl
    calc
      (F.lfp x).wp f st = (F.lfp x st).expected f := rfl
      _ = (F'.lfp (x,st)).expected f := by
        simp only [F', ← ContinuousHom.map_lfp_comp uncurry (F.comp curry)]
        congr 1
      _ = Ψ'.lfp f (x,st)  := by
        apply recursion_expected; apply h
      _ = Ψ.lfp f x st := by
        simp [Ψ', ← OrderHom.map_lfp_comp conv2 (Ψ.comp conv1)]
        congr 1

theorem recursion_wp_simple (F : Program s b →𝒄 Program s b)
  (Ψ : ((Program.Post s b) →o Program.Pre s) →o ((Program.Post s b) →o Program.Pre s))
  (h : ∀ (X : Program s b),
      Ψ ⟨fun (f : Program.Post s b) => X.wp f,
          fun _ _ hf st => expectation_mono2 (X st) hf⟩
         = ⟨fun (f : Program.Post s b) => (F X).wp f,
             fun _ _ hf st => expectation_mono2 (F X st) hf⟩)
         (f : Program.Post s b)
 : F.lfp.wp f = Ψ.lfp f := by
  -- Program s b = s → SubProbability (b × s), and wp = expected, so this is
  -- recursion_expected specialised to a := s, b := b × s.
  ext st
  exact recursion_expected F Ψ h st f

/-- For tailrecursive programs (in particular while-loops), we can write
    the wp iteration function (argument to `recursion_wp[_simple]`) as
    `tailrec_wp something`. In this case, we'll have some nicer properties.
    (See `while_wp_unfold` below for example.) -/
def tailrec_wp [CompleteLattice a] [CompleteLattice b] (Φ : a → b →o b) :
  (a →o b) →o (a →o b) :=
  ⟨fun trafo => ⟨fun post => Φ post (trafo post), sorry⟩, sorry⟩

noncomputable
def while_iteration_wp (c : Program s Bool) (p : Program s Unit)
  (post : Program.Post s Unit) :
  Program.Pre s →o Program.Pre s :=
  ⟨fun fp => c.wp (fun (b, st) =>
            if b then
              p.wp (fun ((),st) => fp st) st
            else
              post ((), st)),
   sorry⟩

@[deprecated while_iteration_wp]
noncomputable
def while_iteration_wp''' (c : Program s Bool) (p : Program s Unit) :=
  tailrec_wp (while_iteration_wp c p)

theorem wp_recursion_tailrec_simplify [CompleteLattice a] [CompleteLattice b] (Φ : a → b →o b) post :
  (tailrec_wp Φ).lfp post = (Φ post).lfp := by
  have lhs_fp : Function.IsFixedPt (Φ post) ((tailrec_wp Φ).lfp post) := sorry
  clear lhs_fp
  have leq : (tailrec_wp Φ).lfp post <= (Φ post).lfp := sorry
  have rhs_fp : Function.IsFixedPt (tailrec_wp Φ) ⟨fun post => (Φ post).lfp, sorry⟩ := sorry
  have geq : (tailrec_wp Φ).lfp >= ⟨fun post => (Φ post).lfp, sorry⟩ := sorry
  clear rhs_fp
  sorry -- Immediate from leq and geq

theorem wp_while' : (while_loop c p).wp f = (tailrec_wp (while_iteration_wp c p)).lfp f := by
  simp only [while_loop]
  apply recursion_wp_simple
  simp [while_iteration, wp_bind, wp_ite, wp_pure, tailrec_wp, while_iteration_wp]

theorem wp_while :
  (while_loop c p).wp f = (while_iteration_wp c p f).lfp := by
  simp [wp_while', wp_recursion_tailrec_simplify]

theorem wp_while_unfold (b : Program s Bool) (body : Program s Unit)
    (f : Program.Post s Unit) (post) :
    (while_loop b body).wp post = b.wp fun (x,st) ↦ if x then body.wp (fun (x,st)
         ↦ (while_loop b body).wp post st) st else post ((), st)
  := by calc
      _ = (while_iteration_wp b body post).lfp := by simp [wp_while]
      _ = while_iteration_wp b body post ((while_iteration_wp b body post).lfp) := sorry
      _ = while_iteration_wp b body post ((while_loop b body).wp post) := by simp only [wp_while]
      _ = _ := by simp [while_iteration_wp]
