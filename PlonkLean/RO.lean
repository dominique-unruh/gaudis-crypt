import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder

import PlonkLean.Misc
import PlonkLean.Semantics
import PlonkLean.WeakestPreconditions
import PlonkLean.Lens
import PlonkLean.LensRange
import PlonkLean.ProgramRange
import PlonkLean.Unsorted

------ Oracles

opaque input : Type
opaque output : Type
instance : Countable state := sorry
instance : Inhabited input := sorry
instance : Fintype input := sorry
instance : Inhabited output := sorry
instance : Fintype output := sorry


axiom random_oracle_state : Variable (input -> Option output)

instance [Fintype a] [Fintype b] : Fintype (a → b) := sorry
instance : DecidableEq input := sorry

/- samples from the entire `input -> output` function space -/
noncomputable def random_oracle_init := do
  let (h : input -> output) <- Program.uniform
  Program.set random_oracle_state (fun x => some (h x))

/- initializes the state with `none` for all inputs -/
noncomputable def lazy_init : Program state Unit := Program.set random_oracle_state (fun _ => none)



/- fills all the holes with output of a uniformly sampled function -/
noncomputable def convert : Program state Unit := do
  let h <- Program.get random_oracle_state
  let (y : input -> output) <- Program.uniform
  Program.set random_oracle_state (fun x => some ((h x).getD (y x)))

noncomputable def lazy_init_convert : Program state Unit := do
  lazy_init
  convert

/- `convert` only reads and writes `random_oracle_state` (modulo a uniform sample). -/
theorem convert_inRange_ro : convert.inRange random_oracle_state.range := by
  show ((Program.get random_oracle_state) >>= fun h =>
          (Program.uniform : Program state (input → output)) >>= fun y =>
            Program.set random_oracle_state (fun x => some ((h x).getD (y x)))).inRange _
  refine Program.inRange_bind (Program.inRange_get _) ?_
  intro _
  refine Program.inRange_bind ?_ ?_
  · exact Program.inRange_mono Program.inRange_uniform bot_le
  · intro _
    exact Program.inRange_set _ _

private theorem program_ext {s a : Type} (p q : Program s a)
    (h : ∀ f, p.wp f = q.wp f) : p = q := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  have hf := congrFun (h (A.indicator 1)) st
  simp only [Program.wp, SubProbability.expected] at hf
  rwa [MeasureTheory.lintegral_indicator_one hA,
       MeasureTheory.lintegral_indicator_one hA] at hf

theorem claim_1 :
   lazy_init_convert = random_oracle_init := by
   apply program_ext
   intro f
   simp [lazy_init_convert, lazy_init, convert, random_oracle_init,
         wp_bind, wp_set, wp_get, wp_uniform,
         random_oracle_state.set_get, random_oracle_state.set_set,
         Option.getD_none]

/- (lazy_query; convert) == (convert; eager_query) -/
noncomputable def lazy_query (inp : input) : Program state output := do
  let h <- Program.get random_oracle_state
  let cached := h inp
  match cached with
  | some x => return x
  | none =>
    let value <- Program.uniform
    Program.set random_oracle_state (fun x => if x=inp then some value else h x)
    return value

noncomputable def random_oracle_query (inp : input) : Program state output := do
  let h <- Program.get random_oracle_state
  return (h inp).getD default


noncomputable def lazy_query_conv (inp : input) :  Program state Unit := do
  let _ <- lazy_query inp
  convert

noncomputable def conv_random_oracle (inp : input) :  Program state Unit := do
  convert
  let _ <- random_oracle_query inp


private lemma sum_update_eq_card_mul_sum {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]
   (i : α) (G : (α → β) → ENNReal) : ∑ v : β, ∑ y : α → β, G (Function.update y i v) = (Fintype.card β : ENNReal) * ∑ z : α → β, G z := by
  let e : β × (α → β) ≃ β × (α → β) :=
    { toFun := fun p => (p.2 i, Function.update p.2 i p.1)
      invFun := fun p => (p.2 i, Function.update p.2 i p.1)
      left_inv := by
        rintro ⟨v, y⟩
        ext
        · exact Function.update_self i v y
        · simp [Function.update_idem, Function.update_eq_self]
      right_inv := by
        rintro ⟨w, z⟩
        ext
        · exact Function.update_self i w z
        · simp [Function.update_idem, Function.update_eq_self] }
  calc ∑ v : β, ∑ y : α → β, G (Function.update y i v)
      = ∑ p : β × (α → β), G (Function.update p.2 i p.1) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ q : β × (α → β), G q.2 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ w : β, ∑ z : α → β, G z := by
        rw [Fintype.sum_prod_type]
    _ = (Fintype.card β : ENNReal) * ∑ z : α → β, G z := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem claim_2 (inp : input) :
  lazy_query_conv inp = conv_random_oracle inp := by
  apply program_ext
  intro f
  funext s
  show (lazy_query_conv inp).wp f s = (conv_random_oracle inp).wp f s
  simp only [lazy_query_conv, lazy_query, conv_random_oracle, random_oracle_query, convert,
             wp_bind, wp_set, wp_get, wp_pure, wp_uniform]
  cases h_eq : random_oracle_state.get s inp with
  | some x => simp [wp_pure]
  | none =>
    simp only [wp_bind, wp_set, wp_pure, wp_uniform,
               random_oracle_state.set_get, random_oracle_state.set_set]
    have integrand_eq : ∀ (value : output) (y : input → output),
        (fun x' : input =>
          some ((if x' = inp then some value else random_oracle_state.get s x').getD (y x')))
        = (fun x' : input =>
          some ((random_oracle_state.get s x').getD (Function.update y inp value x'))) := by
      intros value y
      funext x'
      by_cases hx : x' = inp
      · subst hx; simp [Function.update_self, h_eq]
      · simp [if_neg hx, Function.update_of_ne hx]
    simp_rw [integrand_eq]
    have hO_ne_zero : (Fintype.card output : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    have hO_ne_top : (Fintype.card output : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hF_ne_zero : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    have hF_ne_top : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    let G : (input → output) → ENNReal := fun z =>
      f ((), random_oracle_state.set
          (fun x' => some ((random_oracle_state.get s x').getD (z x'))) s)
    change (∑ v : output, (∑ y : input → output, G (Function.update y inp v) /
                          (Fintype.card (input → output) : ENNReal)) /
                         (Fintype.card output : ENNReal))
       = ∑ z : input → output, G z / (Fintype.card (input → output) : ENNReal)
    calc (∑ v : output, (∑ y : input → output, G (Function.update y inp v) /
                          (Fintype.card (input → output) : ENNReal)) /
                         (Fintype.card output : ENNReal))
        = (∑ v : output, ∑ y : input → output, G (Function.update y inp v)) /
              ((Fintype.card (input → output) : ENNReal) *
               (Fintype.card output : ENNReal)) := by
            simp_rw [div_eq_mul_inv]
            simp_rw [← Finset.sum_mul]
            rw [mul_assoc]
            congr 1
            exact (ENNReal.mul_inv (Or.inl hF_ne_zero) (Or.inl hF_ne_top)).symm
      _ = ((Fintype.card output : ENNReal) * ∑ z : input → output, G z) /
              ((Fintype.card (input → output) : ENNReal) *
               (Fintype.card output : ENNReal)) := by
            rw [sum_update_eq_card_mul_sum]
      _ = (∑ z : input → output, G z) /
            (Fintype.card (input → output) : ENNReal) := by
            rw [mul_comm (Fintype.card (input → output) : ENNReal)
                         (Fintype.card output : ENNReal)]
            exact ENNReal.mul_div_mul_left _ _ hO_ne_zero hO_ne_top
      _ = ∑ z : input → output, G z /
            (Fintype.card (input → output) : ENNReal) := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul]

axiom adv : Program state Unit

noncomputable def adv_conv : Program state Unit := do
  adv
  convert

noncomputable def conv_adv : Program state Unit := do
  convert
  adv

/- Disjointness assumption: `adv` does not touch `random_oracle_state`.
   We express it as `adv.inRange random_oracle_state.compl.range` (= adv lives in
   the lens-complement of `random_oracle_state`). This single hypothesis replaces
   the previous two `adv_commutes_get_ro` / `adv_commutes_set_ro` axioms — the
   commutativity now follows from `commute_of_disjoint_lens`. -/
axiom adv_inRange_compl_ro : adv.inRange random_oracle_state.compl.range

private lemma Program_bind_assoc {s a b c : Type}
    (p : Program s a) (f : a → Program s b) (g : b → Program s c) :
    (p >>= f) >>= g = p >>= fun x => f x >>= g := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  letI : MeasurableSpace (c × s) := ⊤
  exact MeasureTheory.Measure.bind_bind
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable

private lemma Program_pure_bind {s a b : Type} (x : a) (f : a → Program s b) :
    (pure x : Program s a) >>= f = f x := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  exact MeasureTheory.Measure.dirac_bind measurable_from_top (x, st)

private lemma Program_bind_pure {s a : Type} (m : Program s a) :
    m >>= pure = m := by
  funext st
  apply Subtype.ext
  letI : MeasurableSpace (a × s) := ⊤
  change MeasureTheory.Measure.bind (m st).1 (fun p => @MeasureTheory.Measure.dirac (a × s) ⊤ p)
      = (m st).1
  rw [show (fun (p : a × s) => @MeasureTheory.Measure.dirac (a × s) ⊤ p) =
          (fun (p : a × s) => @MeasureTheory.Measure.dirac (a × s) ⊤ (id p)) from rfl]
  rw [MeasureTheory.Measure.bind_dirac_eq_map (m st).1 measurable_id]
  exact MeasureTheory.Measure.map_id

/- `Program.uniform` is state-preserving and produces an independent sample, so it commutes
   with any program. -/
private theorem adv_commutes_uniform {α : Type} [Fintype α] [Nonempty α] {a : Type}
    (k : α → Program state a) :
    (adv >>= fun _ => (Program.uniform : Program state α) >>= k)
  = (Program.uniform >>= fun y => adv >>= fun _ => k y) := by
  apply program_ext
  intro f
  funext s
  simp only [wp_bind, wp_uniform]
  change (adv s).expected (fun x => ∑ y, (k y).wp f x.2 / (Fintype.card α : ENNReal))
      = ∑ y, (adv s).expected (fun x => (k y).wp f x.2) / (Fintype.card α : ENNReal)
  simp only [SubProbability.expected]
  letI : MeasurableSpace (Unit × state) := ⊤
  rw [MeasureTheory.lintegral_finset_sum _ (fun _ _ => measurable_from_top)]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [div_eq_mul_inv]
  exact MeasureTheory.lintegral_mul_const _ measurable_from_top

theorem claim_3 : adv_conv = conv_adv := by
  change (adv >>= fun _ => convert) = (convert >>= fun _ => adv)
  -- Disjointness of the lens-complement with the lens itself (an equality, hence ≤).
  have h_disj : random_oracle_state.compl.range ≤ (random_oracle_state.range)ᶜ :=
    le_of_eq (LensRange.complement_range _)
  -- Pair-output commutation from the headline lemma.
  have h_commute : (adv >>= fun x => convert >>= fun y => pure (x, y))
                 = (convert >>= fun y => adv >>= fun x => pure (x, y)) :=
    Program.commute_of_disjoint_lens adv_inRange_compl_ro convert_inRange_ro h_disj
  -- Massage both sides of the goal into the pair-output form so we can rewrite.
  have hL : (adv >>= fun _ => convert)
          = (adv >>= fun x => convert >>= fun y => pure (x, y)) >>= fun _ => pure () := by
    apply Program.ext_of_wp; intro F; funext σ
    simp [wp_bind, wp_pure]
  have hR : (convert >>= fun _ => adv)
          = (convert >>= fun y => adv >>= fun x => pure (x, y)) >>= fun _ => pure () := by
    apply Program.ext_of_wp; intro F; funext σ
    simp [wp_bind, wp_pure]
  rw [hL, hR, h_commute]


axiom want_more : Variable Bool
axiom oracle_input : Variable input
axiom oracle_output : Variable output
axiom adversary_result : Variable Bool

noncomputable def skip : Program state Unit := do
  return ()

/- The non-RO state variables are disjoint from `random_oracle_state`. -/
axiom disjoint_want_more_ro : disjoint want_more random_oracle_state
axiom disjoint_oracle_input_ro : disjoint oracle_input random_oracle_state
axiom disjoint_oracle_output_ro : disjoint oracle_output random_oracle_state
axiom disjoint_adversary_result_ro : disjoint adversary_result random_oracle_state

attribute [instance] disjoint_want_more_ro disjoint_oracle_input_ro
                     disjoint_oracle_output_ro disjoint_adversary_result_ro

/- Helper: setting on a disjoint lens doesn't change `random_oracle_state.get`. -/
private lemma RO_get_v_set_disjoint {α : Type} (v : Variable α) [disjoint v random_oracle_state]
    (x : α) (s : state) :
    random_oracle_state.get (v.set x s) = random_oracle_state.get s := by
  have h : v.set x s = random_oracle_state.set (random_oracle_state.get s) (v.set x s) := by
    rw [← disjoint.commute, random_oracle_state.get_set]
  rw [h, random_oracle_state.set_get]

/- Helper: setting `random_oracle_state` doesn't change a disjoint lens's get. -/
private lemma v_get_RO_set_disjoint {α : Type} (v : Variable α) [disjoint v random_oracle_state]
    (Z : input → Option output) (s : state) :
    v.get (random_oracle_state.set Z s) = v.get s := by
  have h : random_oracle_state.set Z s = v.set (v.get s) (random_oracle_state.set Z s) := by
    rw [disjoint.commute, v.get_set]
  rw [h, v.set_get]

/- Explicit `convert.wp` formula derived from the definition. -/
private lemma convert_wp_eq (f : Program.Post state Unit) (s : state) :
    convert.wp f s = ∑ y : input → output,
      f ((), random_oracle_state.set
            (fun x => some ((random_oracle_state.get s x).getD (y x))) s) /
      (Fintype.card (input → output) : ENNReal) := by
  simp [convert, wp_bind, wp_set, wp_get, wp_uniform]

/- `convert` commutes with `Program.set v x` for any `v` disjoint from `random_oracle_state`. -/
private theorem convert_commutes_set {α : Type} (v : Variable α) [disjoint v random_oracle_state]
    (x : α) :
    (Program.set v x >>= fun _ => convert) = (convert >>= fun _ => Program.set v x) := by
  apply program_ext
  intro f
  funext s
  simp only [wp_bind, wp_set]
  rw [convert_wp_eq, convert_wp_eq]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  refine Prod.ext rfl ?_
  change random_oracle_state.set _ (v.set x s) = v.set x (random_oracle_state.set _ s)
  rw [show (fun x' : input => some ((random_oracle_state.get (v.set x s) x').getD (y x'))) =
            (fun x' : input => some ((random_oracle_state.get s x').getD (y x'))) from by
        funext x'; rw [RO_get_v_set_disjoint]]
  exact (disjoint.commute s x _).symm

/- `convert` commutes with `Program.get v` for any `v` disjoint from `random_oracle_state`,
   in continuation-passing form. -/
private theorem convert_commutes_get {α β : Type} (v : Variable α)
    [disjoint v random_oracle_state] (k : α → Program state β) :
    (Program.get v >>= fun y => convert >>= fun _ => k y)
    = (convert >>= fun _ => Program.get v >>= k) := by
  apply program_ext
  intro f
  funext s
  simp only [wp_bind, wp_get]
  rw [convert_wp_eq, convert_wp_eq]
  apply Finset.sum_congr rfl
  intro y _
  rw [v_get_RO_set_disjoint]

/- Value-passing variant of claim_2: the lazy_query result is preserved across `convert`. -/
private theorem claim_2_strong (inp : input) :
    (lazy_query inp >>= fun v => convert >>= fun _ => pure v) =
    (convert >>= fun _ => random_oracle_query inp) := by
  apply program_ext
  intro f
  funext s
  change (lazy_query inp >>= fun v => convert >>= fun _ => pure v).wp f s =
         (convert >>= fun _ => random_oracle_query inp).wp f s
  simp only [lazy_query, random_oracle_query, convert,
             wp_bind, wp_set, wp_get, wp_pure, wp_uniform]
  cases h_eq : random_oracle_state.get s inp with
  | some x =>
    simp [wp_pure, h_eq, random_oracle_state.set_get, Option.getD_some]
  | none =>
    simp only [wp_bind, wp_set, wp_pure, wp_uniform,
               random_oracle_state.set_get, random_oracle_state.set_set, h_eq,
               Option.getD_none, Option.getD_some]
    have integrand_eq : ∀ (value : output) (y : input → output),
        (fun x' : input =>
          some ((if x' = inp then some value else random_oracle_state.get s x').getD (y x')))
        = (fun x' : input =>
          some ((random_oracle_state.get s x').getD (Function.update y inp value x'))) := by
      intros value y
      funext x'
      by_cases hx : x' = inp
      · subst hx; simp [Function.update_self, h_eq]
      · simp [if_neg hx, Function.update_of_ne hx]
    simp_rw [integrand_eq]
    have hO_ne_zero : (Fintype.card output : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    have hO_ne_top : (Fintype.card output : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hF_ne_zero : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    have hF_ne_top : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    let G : (input → output) → ENNReal := fun z =>
      f (z inp, random_oracle_state.set
          (fun x' => some ((random_oracle_state.get s x').getD (z x'))) s)
    have lhs_rewrite : ∀ (value : output) (y : input → output),
        f (value, random_oracle_state.set
            (fun x' => some ((random_oracle_state.get s x').getD (Function.update y inp value x'))) s)
        = G (Function.update y inp value) := by
      intros value y
      change f (value, _) = f ((Function.update y inp value) inp, _)
      rw [Function.update_self]
    simp_rw [lhs_rewrite]
    change (∑ v : output, (∑ y : input → output, G (Function.update y inp v) /
                          (Fintype.card (input → output) : ENNReal)) /
                         (Fintype.card output : ENNReal))
       = ∑ z : input → output, G z / (Fintype.card (input → output) : ENNReal)
    calc (∑ v : output, (∑ y : input → output, G (Function.update y inp v) /
                          (Fintype.card (input → output) : ENNReal)) /
                         (Fintype.card output : ENNReal))
        = (∑ v : output, ∑ y : input → output, G (Function.update y inp v)) /
              ((Fintype.card (input → output) : ENNReal) *
               (Fintype.card output : ENNReal)) := by
            simp_rw [div_eq_mul_inv]
            simp_rw [← Finset.sum_mul]
            rw [mul_assoc]
            congr 1
            exact (ENNReal.mul_inv (Or.inl hF_ne_zero) (Or.inl hF_ne_top)).symm
      _ = ((Fintype.card output : ENNReal) * ∑ z : input → output, G z) /
              ((Fintype.card (input → output) : ENNReal) *
               (Fintype.card output : ENNReal)) := by
            rw [sum_update_eq_card_mul_sum]
      _ = (∑ z : input → output, G z) /
            (Fintype.card (input → output) : ENNReal) := by
            rw [mul_comm (Fintype.card (input → output) : ENNReal)
                         (Fintype.card output : ENNReal)]
            exact ENNReal.mul_div_mul_left _ _ hO_ne_zero hO_ne_top
      _ = ∑ z : input → output, G z /
            (Fintype.card (input → output) : ENNReal) := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul]

/- Continuation-passing variant: `lazy_query inp` followed by `convert` followed by `k` equals
   `convert` followed by `random_oracle_query inp` followed by `k`. -/
private theorem claim_2_cont {β : Type} (inp : input) (k : output → Program state β) :
    (lazy_query inp >>= fun v => convert >>= fun _ => k v)
  = (convert >>= fun _ => random_oracle_query inp >>= k) := by
  have h1 : (lazy_query inp >>= fun v => convert >>= fun _ => k v)
        = (lazy_query inp >>= fun v => convert >>= fun _ => pure v) >>= k := by
    rw [Program_bind_assoc]
    congr 1; funext v
    rw [Program_bind_assoc]
    congr 1; funext _
    rw [Program_pure_bind]
  have h2 : (convert >>= fun _ => random_oracle_query inp >>= k)
        = (convert >>= fun _ => random_oracle_query inp) >>= k := by
    rw [Program_bind_assoc]
  rw [h1, h2, claim_2_strong]

/- Pushing `convert` past the `let inp ← get oracle_input; let v ← lazy_query inp; set oracle_output v`
   piece. -/
private theorem query_set_convert_eq :
    ((Program.get oracle_input >>= fun inp =>
      lazy_query inp >>= fun v =>
      Program.set oracle_output v) >>= fun _ => convert)
  = (convert >>= fun _ =>
      Program.get oracle_input >>= fun inp =>
      random_oracle_query inp >>= fun v =>
      Program.set oracle_output v) := by
  simp_rw [Program_bind_assoc, convert_commutes_set, claim_2_cont]
  exact convert_commutes_get oracle_input _

/- Factor `convert` out of an `if`: if the then-branch starts with `convert` and the else-branch
   is `convert`, we can move `convert` outside. -/
private lemma if_factor_convert (b : Bool) (X : Program state Unit) :
    (if b = true then convert >>= fun _ => X else convert)
  = convert >>= fun _ => (if b = true then X else pure ()) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (Program_bind_pure convert).symm
  · rfl

/- Body of the loop with `convert` appended on the lazy side equals `convert` prepended
   on the eager side. -/
private theorem body_convert_eq :
    ((do
      adv
      if ← Program.get want_more then
        Program.set oracle_output (← lazy_query (← Program.get oracle_input))
      else
        skip) >>= fun _ => convert)
  = (convert >>= fun _ => do
      adv
      if ← Program.get want_more then
        Program.set oracle_output (← random_oracle_query (← Program.get oracle_input))
      else
        skip) := by
  -- Step 1: bind_assoc to push outer convert through adv's bind.
  rw [Program_bind_assoc]
  -- LHS: adv >>= fun _ => ((get want_more >>= ...) >>= convert)
  -- Step 2: bind_assoc inside, then distribute over if.
  conv_lhs =>
    arg 2; ext _
    rw [Program_bind_assoc]
    -- Now: get want_more >>= fun b => (if b then T_lazy else skip) >>= convert
    arg 2; ext b
    rw [show ((if b = true then
                (Program.get oracle_input >>= fun inp =>
                 lazy_query inp >>= fun v =>
                 Program.set oracle_output v)
              else skip) >>= fun _ => convert)
            = (if b = true then
                ((Program.get oracle_input >>= fun inp =>
                 lazy_query inp >>= fun v =>
                 Program.set oracle_output v) >>= fun _ => convert)
              else (skip >>= fun _ => convert))
            from by split_ifs <;> rfl]
    rw [show (skip >>= fun _ => convert : Program state Unit) = convert from
          Program_pure_bind () _]
    rw [query_set_convert_eq]
    rw [if_factor_convert]
  -- Now LHS: adv >>= fun _ => (get want_more >>= fun b => convert >>= ...)
  -- Step 3: push convert past get want_more.
  conv_lhs =>
    arg 2; ext _
    rw [convert_commutes_get]
  -- LHS: adv >>= fun _ => (convert >>= fun _ => get want_more >>= ...)
  -- Step 4: bind_assoc reverse, then claim_3, then bind_assoc.
  rw [← Program_bind_assoc,
      show (adv >>= fun _ => convert) = (convert >>= fun _ => adv) from claim_3,
      Program_bind_assoc]
  rfl

noncomputable def oracle_loop
  (init : Program state Unit)
  (oracle : input -> Program state output) : Program state Bool := do
  Program.set want_more true
  init
  while_loop (Program.get want_more) (do
    adv
    if ← Program.get want_more then
      Program.set oracle_output (← oracle (← Program.get oracle_input))
    else
      skip
  )
  Program.get adversary_result


/-
Proof sketch of `claim_4`:
The sequence of calls of `oracle_loop lazy_init lazy_query` must look something like

1. `lazy_init; adv; lazy_query; ... adv; lazy_query`

This is equivalent (up to `random_oracle_state`) to

2. `lazy_init; adv; lazy_query; ... adv; lazy_query; convert`

Using `claim_3` we can convert last two calls into `eager_query` and get

3. `lazy_init; adv; lazy_query; ...  lazy_query ;adv; convert; eager_query`

Using `claim_2` move `convert` to the front

4. `lazy_init; convert; adv; lazy_query; ...  lazy_query ;convert; adv; eager_query`

Continue doing that (by induction?) to get

5. `eager_init; convert; adv; eager_query; ... adv; eager_query`

Get rid of `convert`

-/

private noncomputable def loop_body_lazy : Program state Unit := do
  adv
  if ← Program.get want_more then
    Program.set oracle_output (← lazy_query (← Program.get oracle_input))
  else
    skip

private noncomputable def loop_body_eager : Program state Unit := do
  adv
  if ← Program.get want_more then
    Program.set oracle_output (← random_oracle_query (← Program.get oracle_input))
  else
    skip

private theorem body_def_convert_eq :
    (loop_body_lazy >>= fun _ => convert) = (convert >>= fun _ => loop_body_eager) :=
  body_convert_eq

/- Helper: bot bind anything is bot. -/
private lemma Program_bot_bind {s a b : Type} (F : a → Program s b) :
    (⊥ : Program s a) >>= F = ⊥ := by
  funext st
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

/- Helper: bind with constant bot is bot. -/
private lemma Program_bind_bot {s a b : Type} (m : Program s a) :
    m >>= (fun _ => (⊥ : Program s b)) = ⊥ := by
  funext st
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_right' _

/- The intermediate iteration: same as `while_iteration` for the lazy body, but with `convert`
   in the else branch (representing "loop terminates, then convert"). -/
private noncomputable def Ψ_iter :
    (Unit → Program state Unit) →𝒄 (Unit → Program state Unit) :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Unit → Program state Unit) => fun () =>
    do if ← Program.get want_more then
         loop_body_lazy
         fp ()
       else convert

/- Kleene induction on the lazy side: at every finite iterate, the lazy iterate composed with
   `convert` equals the same iterate of `Ψ_iter`. -/
private lemma loop_kleene_lazy : ∀ n : ℕ,
    (((while_iteration (Program.get want_more) loop_body_lazy)^[n]
      (⊥ : Unit → Program state Unit)) () >>= (fun _ => convert))
    = (Ψ_iter^[n] (⊥ : Unit → Program state Unit)) () := by
  intro n
  induction n with
  | zero =>
    change ((⊥ : Unit → Program state Unit) () >>= fun _ => convert) = (⊥ : Unit → Program state Unit) ()
    change ((⊥ : Program state Unit) >>= fun _ => convert) = (⊥ : Program state Unit)
    exact Program_bot_bind _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    -- LHS: (while_iteration cond body_lazy (F_lazy^[n] ⊥)) () >>= convert
    -- RHS: Ψ_iter (Ψ_iter^[n] ⊥) ()
    -- Unfold while_iteration and Ψ_iter, apply if-distribute, then ih.
    change (((Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_lazy >>= fun _ =>
                  ((while_iteration (Program.get want_more) loop_body_lazy)^[n] ⊥) ()
              else (pure () : Program state Unit)) >>= fun _ => convert)
        = (Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_lazy >>= fun _ => (Ψ_iter^[n] ⊥) ()
              else convert
    rw [Program_bind_assoc]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      rw [Program_bind_assoc]
      congr 1; funext _
      exact ih
    · simp only [h, if_false]
      exact Program_pure_bind () _

/- Kleene induction on the eager side: `convert` prepended to each eager iterate equals the
   same iterate of `Ψ_iter`. -/
private lemma loop_kleene_eager : ∀ n : ℕ,
    convert >>= (fun _ => ((while_iteration (Program.get want_more) loop_body_eager)^[n]
      (⊥ : Unit → Program state Unit)) ())
    = (Ψ_iter^[n] (⊥ : Unit → Program state Unit)) () := by
  intro n
  induction n with
  | zero =>
    change (convert >>= fun _ => (⊥ : Unit → Program state Unit) ()) = (⊥ : Unit → Program state Unit) ()
    change (convert >>= fun _ => (⊥ : Program state Unit)) = (⊥ : Program state Unit)
    exact Program_bind_bot _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    -- LHS: convert >>= F_eager (F_eager^[n] ⊥) ()
    -- RHS: Ψ_iter (Ψ_iter^[n] ⊥) ()
    change (convert >>= fun _ => (Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_eager >>= fun _ =>
                  ((while_iteration (Program.get want_more) loop_body_eager)^[n] ⊥) ()
              else (pure () : Program state Unit))
        = (Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_lazy >>= fun _ => (Ψ_iter^[n] ⊥) ()
              else convert
    -- Push convert past get want_more.
    rw [show (convert >>= fun _ => (Program.get want_more) >>=
              fun b => if b = true then loop_body_eager >>= fun _ =>
                  ((while_iteration (Program.get want_more) loop_body_eager)^[n] ⊥) ()
                else (pure () : Program state Unit))
            = ((Program.get want_more) >>= fun b => convert >>= fun _ =>
                if b = true then loop_body_eager >>= fun _ =>
                  ((while_iteration (Program.get want_more) loop_body_eager)^[n] ⊥) ()
                else (pure () : Program state Unit)) from by
        rw [← convert_commutes_get]]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      -- LHS: convert >>= body_eager >>= F_eager^[n] ⊥ ()
      -- Use body_def_convert_eq to swap convert and body
      rw [← Program_bind_assoc]
      rw [show (convert >>= fun _ => loop_body_eager) = (loop_body_lazy >>= fun _ => convert) from
            body_def_convert_eq.symm]
      rw [Program_bind_assoc]
      congr 1; funext _
      exact ih
    · simp only [h, if_false]
      exact Program_bind_pure _

/- Lift the Kleene iterate identity to the lfp via ω-continuity of bind. -/
private theorem loop_coupling :
    ((while_loop (Program.get want_more) loop_body_lazy) >>= fun _ => convert)
  = (convert >>= fun _ => while_loop (Program.get want_more) loop_body_eager) := by
  -- Both sides equal Ψ_iter.lfp ().
  -- LHS = W_lazy >>= convert = (F_lazy.lfp ()) >>= convert
  --     = (⨆ n, F_lazy^[n] ⊥ ()) >>= convert    [Kleene + pointwise sup]
  --     = ⨆ n, (F_lazy^[n] ⊥ ()) >>= convert     [ω-continuity of `>>= convert`]
  --     = ⨆ n, Ψ_iter^[n] ⊥ ()                   [loop_kleene_lazy]
  --     = Ψ_iter.lfp ()
  -- RHS, symmetrically using loop_kleene_eager.
  let F_lazy := while_iteration (Program.get want_more) loop_body_lazy
  let F_eager := while_iteration (Program.get want_more) loop_body_eager
  have hL_chain : ∀ n, ((F_lazy^[n] ⊥ : Unit → Program state Unit) () >>= (fun _ => convert))
                     = (Ψ_iter^[n] ⊥ : Unit → Program state Unit) () := loop_kleene_lazy
  have hE_chain : ∀ n, convert >>= (fun _ => (F_eager^[n] ⊥ : Unit → Program state Unit) ())
                     = (Ψ_iter^[n] ⊥ : Unit → Program state Unit) () := loop_kleene_eager
  -- ω-continuity of `· >>= convert` and `convert >>= ·`.
  have h_bind_convert_cont :
      OmegaCompletePartialOrder.ωScottContinuous
        (fun (m : Program state Unit) => m >>= fun _ => convert) := by fun_prop
  have h_convert_bind_cont :
      OmegaCompletePartialOrder.ωScottContinuous
        (fun (m : Program state Unit) => convert >>= fun _ => m) := by fun_prop
  -- Express W_lazy, W_eager, Ψ.lfp as ωSup's of their Kleene chains.
  change (F_lazy.lfp ()) >>= (fun _ => convert) = convert >>= (fun _ => F_eager.lfp ())
  -- Get the chains
  let chain_lazy : OmegaCompletePartialOrder.Chain (Unit → Program state Unit) :=
    ⟨fun n => F_lazy^[n] ⊥,
     Monotone.monotone_iterate_of_le_map F_lazy.monotone (OrderBot.bot_le _)⟩
  let chain_eager : OmegaCompletePartialOrder.Chain (Unit → Program state Unit) :=
    ⟨fun n => F_eager^[n] ⊥,
     Monotone.monotone_iterate_of_le_map F_eager.monotone (OrderBot.bot_le _)⟩
  let chain_Ψ : OmegaCompletePartialOrder.Chain (Unit → Program state Unit) :=
    ⟨fun n => Ψ_iter^[n] ⊥,
     Monotone.monotone_iterate_of_le_map Ψ_iter.monotone (OrderBot.bot_le _)⟩
  have hLfpL : F_lazy.lfp = OmegaCompletePartialOrder.ωSup chain_lazy := rfl
  have hLfpE : F_eager.lfp = OmegaCompletePartialOrder.ωSup chain_eager := rfl
  -- F_lazy.lfp () = ωSup (chain_lazy.map (eval at ()))
  have hLfpL_at : F_lazy.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_lazy.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by
    rw [hLfpL]; rfl
  have hLfpE_at : F_eager.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_eager.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by
    rw [hLfpE]; rfl
  -- LHS = F_lazy.lfp () >>= convert
  rw [hLfpL_at, hLfpE_at]
  rw [h_bind_convert_cont.map_ωSup]
  rw [h_convert_bind_cont.map_ωSup]
  -- Now both sides are ωSup's. Show the chains are equal pointwise.
  congr 1
  ext n
  -- Show: F_lazy^[n] ⊥ () >>= convert = convert >>= F_eager^[n] ⊥ ()
  exact (hL_chain n).trans (hE_chain n).symm

theorem claim_4 :
    (oracle_loop lazy_init lazy_query >>= fun b => convert >>= fun _ => pure b)
  = oracle_loop random_oracle_init random_oracle_query
  := by
  -- Fold the inline bodies as `loop_body_lazy` / `loop_body_eager` (definitionally equal).
  change ((Program.set want_more true >>= fun _ =>
            lazy_init >>= fun _ =>
              while_loop (Program.get want_more) loop_body_lazy >>= fun _ =>
                Program.get adversary_result) >>= fun b => convert >>= fun _ => pure b)
       = (Program.set want_more true >>= fun _ =>
            random_oracle_init >>= fun _ =>
              while_loop (Program.get want_more) loop_body_eager >>= fun _ =>
                Program.get adversary_result)
  -- Flatten binds.
  simp_rw [Program_bind_assoc]
  -- Step 1: tail rewrite.
  rw [show ((Program.get adversary_result) >>= fun b => convert >>= fun _ => pure b)
        = (convert >>= fun _ => Program.get adversary_result) from by
      rw [convert_commutes_get]
      congr 1; funext b; exact Program_bind_pure _]
  -- Step 2: regroup `while_lazy >>= _ => convert` and apply loop_coupling.
  rw [show (∀ (W : Program state Unit) (K : Program state Bool),
        (W >>= fun _ => convert >>= fun _ => K) = ((W >>= fun _ => convert) >>= fun _ => K))
        from fun W K => (Program_bind_assoc _ _ _).symm]
  rw [loop_coupling]
  rw [Program_bind_assoc]
  -- Step 3: regroup `lazy_init >>= _ => convert` and apply claim_1.
  rw [show (∀ (L : Program state Unit) (K : Program state Bool),
        (L >>= fun _ => convert >>= fun _ => K) = ((L >>= fun _ => convert) >>= fun _ => K))
        from fun L K => (Program_bind_assoc _ _ _).symm]
  rw [show (lazy_init >>= fun _ => convert) = random_oracle_init from claim_1]

/-- `claim_5`: the lazy and eager oracle loops agree on every postcondition that is
    invariant under writes to `random_oracle_state` (i.e., every postcondition that only
    depends on the *non-RO* part of state).

    Intuitively: an adversary that observes only its own global variables (none of which
    are the random oracle's internal state) cannot tell lazy from eager. -/
theorem claim_5 (F : Bool × state → ENNReal)
    (hF_inv : ∀ (b : Bool) (σ : state) (x : input → Option output),
        F (b, random_oracle_state.set x σ) = F (b, σ)) :
    (oracle_loop lazy_init lazy_query).wp F
  = (oracle_loop random_oracle_init random_oracle_query).wp F := by
  -- Step 1: convert composed with `pure b` is wp-transparent for RO-invariant F.
  -- (convert >>= fun _ => pure b).wp F σ = F (b, σ).
  have h_convert : ∀ (b : Bool) (σ : state),
      (convert >>= fun _ : Unit => (pure b : Program state Bool)).wp F σ = F (b, σ) := by
    intros b σ
    simp only [wp_bind, wp_pure]
    rw [convert_wp_eq]
    -- ∑ y, F (b, random_oracle_state.set (...) σ) / card = F (b, σ)
    simp_rw [hF_inv]
    -- ∑ y : input → output, F (b, σ) / card = F (b, σ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- ↑card * (F (b, σ) / ↑card) = F (b, σ)
    have hcard_pos : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    have hcard_top : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.mul_div_cancel hcard_pos hcard_top]
  -- Step 2: use claim_4 to bridge the two loops.
  have h4_wp := congr_arg (fun prog : Program state Bool => prog.wp F) claim_4
  simp only at h4_wp  -- beta-reduce
  -- h4_wp : (lazy_loop >>= fun b => convert >>= fun _ => pure b).wp F = eager_loop.wp F
  rw [wp_bind] at h4_wp
  -- h4_wp : lazy_loop.wp (fun ⟨b, σ⟩ => (convert >>= fun _ => pure b).wp F σ) = eager_loop.wp F
  -- Replace the inner expression using h_convert.
  have h_eq : (fun (bσ : Bool × state) =>
                  (convert >>= fun _ : Unit => (pure bσ.1 : Program state Bool)).wp F bσ.2)
            = (fun (bσ : Bool × state) => F (bσ.1, bσ.2)) := by
    funext bσ; exact h_convert bσ.1 bσ.2
  rw [h_eq] at h4_wp
  -- h4_wp : lazy_loop.wp (fun bσ => F (bσ.1, bσ.2)) = eager_loop.wp F.
  -- After beta + eta, this is lazy_loop.wp F = eager_loop.wp F.
  exact h4_wp

/-- **SubProb-level form of `claim_5`**: for any projection `h : state → β` of
    state that is invariant under writes to `random_oracle_state` (i.e., `h` only
    sees the *non-RO* part of state), the lazy and eager oracle loops produce the
    same distribution over `Bool × β`.

    This is the "lazy oracle is indistinguishable from eager oracle by the
    adversary's observable variables" statement: an adversary that observes only
    `h σ` (which doesn't depend on the RO's internal state) sees identical
    distributions in both worlds. -/
theorem claim_5_subprob {β : Type} (h : state → β)
    (h_inv : ∀ (σ : state) (x : input → Option output),
        h (random_oracle_state.set x σ) = h σ)
    (σ₀ : state) :
    (oracle_loop lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state => (pure (bσ.1, h bσ.2) : SubProbability (Bool × β)))
    =
    (oracle_loop random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state => (pure (bσ.1, h bσ.2) : SubProbability (Bool × β))) := by
  apply Subtype.ext
  letI : MeasurableSpace (Bool × state) := ⊤
  letI : MeasurableSpace (Bool × β) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  -- Reduce both sides via `Measure.bind_apply` to lintegrals.
  show MeasureTheory.Measure.bind (oracle_loop lazy_init lazy_query σ₀).1
        (fun bσ : Bool × state =>
          @MeasureTheory.Measure.dirac (Bool × β) ⊤ (bσ.1, h bσ.2)) A
    = MeasureTheory.Measure.bind (oracle_loop random_oracle_init random_oracle_query σ₀).1
        (fun bσ : Bool × state =>
          @MeasureTheory.Measure.dirac (Bool × β) ⊤ (bσ.1, h bσ.2)) A
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  -- Now both sides are `∫⁻ bσ, dirac (bσ.1, h bσ.2) A ∂(…).1`,
  -- i.e. (… .wp F σ₀) for F bσ := dirac (bσ.1, h bσ.2) A.
  -- This F is RO-invariant because `h` is.
  exact congr_fun (claim_5
      (fun bσ : Bool × state =>
        (@MeasureTheory.Measure.dirac (Bool × β) ⊤ (bσ.1, h bσ.2)) A)
      (by intros b σ x; simp only; rw [h_inv])) σ₀

/-- **Form (a) of `claim_5` — lens-complement projection**.

    The joint distribution of (adv's bit, the entire non-RO part of state) is
    identical under lazy and eager RO.

    `random_oracle_state.compl.get` is the lens-complement getter: it returns
    the equivalence class of σ modulo "differs only in RO content". This is
    the most concrete glob-style form — the returned type is a `Quotient` of
    state by the RO-equivalence, with no `Program.range` machinery involved. -/
theorem claim_5_compl (σ₀ : state) :
    (oracle_loop lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid)))
    =
    (oracle_loop random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid))) := by
  refine claim_5_subprob random_oracle_state.compl.get ?_ σ₀
  -- h_inv: random_oracle_state.compl.get (set x σ) = random_oracle_state.compl.get σ.
  -- compl.get is `Quotient.mk''` on the equal_outside setoid, and set x σ ~ σ
  -- via the witness `random_oracle_state.get σ`:
  --   set (get σ) (set x σ) = set (get σ) σ = σ (by set_set and get_set).
  intro σ x
  exact Quotient.sound ⟨random_oracle_state.get σ,
    (random_oracle_state.set_set σ x (random_oracle_state.get σ)).trans
      (random_oracle_state.get_set σ)⟩

/-- **Form (c) of `claim_5` — `Program.glob adv`**.

    The joint distribution of (adv's bit, what `adv` can see/modify) is
    identical under lazy and eager RO.

    This is the natural cryptographic indistinguishability statement:
    `(Program.glob adv).get bσ.2` is the equivalence class of `bσ.2` under
    `(adv.range)ᶜ`-orbits — i.e., "everything adv could possibly observe or
    affect", quotiented by symmetries outside adv's reach.

    Corollary of `claim_5_subprob` applied to `(Program.glob adv).get`. The
    RO-invariance of this projection follows from `adv_inRange_compl_ro` via
    the inclusion `random_oracle_state.range ≤ (adv.range)ᶜ`. -/
theorem claim_5_glob (σ₀ : state) :
    (oracle_loop lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals)))
    =
    (oracle_loop random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals))) := by
  refine claim_5_subprob (Program.glob adv).get ?_ σ₀
  intro σ x
  -- Goal: Quotient.mk (adv.range)ᶜ.orbit_setoid (set x σ)
  --     = Quotient.mk (adv.range)ᶜ.orbit_setoid σ
  apply Quotient.sound
  -- Goal reduces to: Relation.EqvGen (∃ f ∈ (adv.range)ᶜ.updates, f s = s') (set x σ) σ
  change Relation.EqvGen
      (fun s s' : state => ∃ f ∈ ((adv.range)ᶜ : LensRange state).updates, f s = s')
      (random_oracle_state.set x σ) σ
  -- Use symm: it's easier to give a forward step σ ↦ set x σ.
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  -- Witness: f := random_oracle_state.set x. Membership chain below.
  refine ⟨random_oracle_state.set x, ?_, rfl⟩
  -- random_oracle_state.set x ∈ random_oracle_state.range.updates (canonical).
  have h_in_ro : random_oracle_state.set x ∈ random_oracle_state.range.updates := by
    refine ⟨Function.const _ x, Set.mem_univ _, ?_⟩
    funext σ'
    simp [Lens.update]
  -- adv.range ≤ random_oracle_state.compl.range (from adv_inRange_compl_ro).
  have hadv_le : adv.range ≤ random_oracle_state.compl.range :=
    sInf_le adv_inRange_compl_ro
  -- Antitone complement + complement_range + compl_compl give the inclusion.
  have h_le : random_oracle_state.range ≤ (adv.range)ᶜ := by
    have hflip : (random_oracle_state.compl.range)ᶜ ≤ (adv.range)ᶜ := by
      change (Submonoid.centralizer random_oracle_state.compl.range.updates).carrier
           ⊆ (Submonoid.centralizer adv.range.updates).carrier
      exact Submonoid.centralizer_le hadv_le
    rwa [LensRange.complement_range, LensRange.compl_compl] at hflip
  exact h_le h_in_ro

/-! ## Phase 6 — General lazy/eager transfer relation

The existing `claim_5` is for `oracle_loop` specifically. Below we abstract the
underlying principle into a `Program.transfer` relation that captures
"`convert` slides past `p` and turns lazy operations into eager ones", with
closure lemmas making it usable for arbitrary program structures (e.g.
`cr_experiment`). -/

/-- `convert` is a probability measure: its total mass is 1.
    All pieces (`get`, `uniform`, `set`) preserve mass. -/
lemma convert_mass (σ : state) : convert.wp (fun _ => 1) σ = 1 := by
  simp only [convert, wp_bind, wp_get, wp_uniform, wp_set]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN_pos : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hN_top : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_div_cancel hN_pos hN_top]

/-- `convert` is absorbed by `random_oracle_init`: a fresh uniform sample
    overwrites any prior RO content. -/
lemma convert_random_oracle_init :
    (convert >>= fun _ => random_oracle_init) = random_oracle_init := by
  apply program_ext
  intro f
  funext σ
  show (convert >>= fun _ => random_oracle_init).wp f σ = random_oracle_init.wp f σ
  simp only [convert, random_oracle_init, wp_bind, wp_set, wp_get, wp_uniform, wp_pure,
             random_oracle_state.set_set]
  -- LHS: ∑ y : input → output, (∑ h : input → output, f ((), RO.set (some ∘ h) σ) / card) / card
  -- RHS: ∑ h : input → output, f ((), RO.set (some ∘ h) σ) / card
  -- The inner term doesn't depend on y, so summing 1/card over y gives 1.
  set N : ENNReal := (Fintype.card (input → output) : ENNReal) with hN
  set S : ENNReal := ∑ h : input → output,
      f ((), random_oracle_state.set (fun x => some (h x)) σ) / N
  have hN_pos : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_pos.ne'
  have hN_top : N ≠ ⊤ := by rw [hN]; exact ENNReal.natCast_ne_top _
  -- LHS = ∑ y, S / N = card * (S / N) = N * (S / N) = S = RHS.
  show ∑ _y : input → output, S / N = S
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN,
      mul_comm N (S / N), ENNReal.div_mul_cancel hN_pos hN_top]

/-- **Lazy/eager transfer relation**: `p` followed by `convert` produces the
    same joint `α × state` distribution as `convert` followed by `q`.

    Captures "`convert` slides past `p`, turning lazy operations into eager ones".
    Closed under bind; reflexive on RO-disjoint programs. Together with the base
    cases `lazy_init ↦ random_oracle_init` (claim_1) and
    `lazy_query x ↦ random_oracle_query x` (claim_2_strong), this lets us
    transfer any program built from these primitives. -/
def Program.transfer {α : Type} (p q : Program state α) : Prop :=
  (p >>= fun a => convert >>= fun _ => pure a) = (convert >>= fun _ => q)

/-- Reflexivity on RO-disjoint programs: a program that doesn't modify
    `random_oracle_state` commutes with `convert`, so transfers to itself. -/
lemma Program.transfer_refl_of_inRange_compl
    {α : Type} [Countable α] {p : Program state α}
    (hp : p.inRange random_oracle_state.compl.range) :
    Program.transfer p p := by
  show (p >>= fun a => convert >>= fun _ => pure a) = (convert >>= fun _ => p)
  have h_disj : random_oracle_state.compl.range ≤ (random_oracle_state.range)ᶜ :=
    le_of_eq (LensRange.complement_range _)
  have h_commute : (p >>= fun a => convert >>= fun b => pure (a, b))
                 = (convert >>= fun b => p >>= fun a => pure (a, b)) :=
    Program.commute_of_disjoint_lens hp convert_inRange_ro h_disj
  have hL : (p >>= fun a => convert >>= fun b => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program state α))
          = (p >>= fun a => convert >>= fun _ => (Pure.pure a : Program state α)) := by
    rw [Program_bind_assoc]; congr 1; funext a
    rw [Program_bind_assoc]; congr 1; funext _
    rw [Program_pure_bind]
  have hR : (convert >>= fun b => p >>= fun a => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program state α))
          = (convert >>= fun _ => p) := by
    rw [Program_bind_assoc]
    congr 1; funext _
    rw [Program_bind_assoc]
    rw [show (fun a : α => pure (a, ()) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program state α)))
          = (fun a : α => (Pure.pure a : Program state α)) from by
        funext a; rw [Program_pure_bind]]
    exact Program_bind_pure _
  rw [← hL, h_commute, hR]

/-- Bind closure: transfer chains under `>>=`. -/
lemma Program.transfer_bind {α β : Type}
    {p q : Program state α} {p' q' : α → Program state β}
    (h : Program.transfer p q) (h' : ∀ a, Program.transfer (p' a) (q' a)) :
    Program.transfer (p >>= p') (q >>= q') := by
  show ((p >>= p') >>= fun b => convert >>= fun _ => pure b)
      = (convert >>= fun _ => q >>= q')
  rw [Program_bind_assoc]
  conv_lhs =>
    rhs; ext a
    rw [show (p' a >>= fun b => convert >>= fun _ => (Pure.pure b : Program state β))
          = (convert >>= fun _ => q' a) from h' a]
  conv_lhs =>
    rhs; ext a
    rw [show (convert >>= fun _ => q' a)
          = (convert >>= fun _ => (Pure.pure a : Program state α)) >>= q' from by
        rw [Program_bind_assoc]; congr 1; funext _; rw [Program_pure_bind]]
  rw [← Program_bind_assoc]
  rw [show (p >>= fun a => convert >>= fun _ => (Pure.pure a : Program state α))
        = (convert >>= fun _ => q) from h]
  rw [Program_bind_assoc]

/-- Pure transfers to itself. -/
lemma Program.transfer_pure {α : Type} (a : α) :
    Program.transfer (Pure.pure a : Program state α) (Pure.pure a) := by
  show ((Pure.pure a : Program state α) >>= fun a' => convert >>= fun _ => pure a')
      = (convert >>= fun _ => Pure.pure a)
  rw [Program_pure_bind]

/-- `lazy_init` transfers to `random_oracle_init`. -/
lemma Program.transfer_lazy_init :
    Program.transfer lazy_init random_oracle_init := by
  show (lazy_init >>= fun _ => convert >>= fun _ => (Pure.pure () : Program state Unit))
      = (convert >>= fun _ => random_oracle_init)
  have hL : (lazy_init >>= fun _ => convert >>= fun _ => (Pure.pure () : Program state Unit))
          = lazy_init >>= fun _ => convert := by
    congr 1; funext _
    exact Program_bind_pure _
  rw [hL]
  show lazy_init_convert = (convert >>= fun _ => random_oracle_init)
  rw [claim_1]
  exact convert_random_oracle_init.symm

/-- `lazy_query x` transfers to `random_oracle_query x`. This is `claim_2_strong`
    restated in the transfer language. -/
lemma Program.transfer_lazy_query (x : input) :
    Program.transfer (lazy_query x) (random_oracle_query x) :=
  claim_2_strong x

/-- `convert.wp` of any constant function equals that constant (since `convert`
    is a probability measure). Specialization of `Program.wp_const_mul` + `convert_mass`. -/
lemma convert_wp_const (c : ENNReal) (σ : state) :
    convert.wp (fun _ : Unit × state => c) σ = c := by
  have h := Program.wp_const_mul convert c (fun _ : Unit × state => (1 : ENNReal)) σ
  simp only [mul_one] at h
  rw [h, convert_mass, mul_one]

/-- **Transfer at the wp level for value-only postconditions**.
    For `G : α → ENNReal`, the wp of `p` and `q` against `fun aσ => G aσ.1`
    agree (at any starting state), given the transfer + absorption hypotheses. -/
theorem Program.transfer_wp_value {α : Type}
    {p q : Program state α}
    (h_transfer : Program.transfer p q)
    (h_absorb : (convert >>= fun _ => q) = q)
    (G : α → ENNReal) (σ₀ : state) :
    p.wp (fun aσ : α × state => G aσ.1) σ₀
  = q.wp (fun aσ : α × state => G aσ.1) σ₀ := by
  -- Combine transfer + absorb into the master equation:
  --   (p >>= a => convert >>= pure a) = q.
  have h_eq : (p >>= fun a => convert >>= fun _ => (Pure.pure a : Program state α)) = q := by
    rw [h_transfer, h_absorb]
  -- Apply wp at σ₀ with F = (fun aσ => G aσ.1).
  have h_wp := congrArg
      (fun (r : Program state α) =>
        r.wp (fun aσ : α × state => G aσ.1) σ₀) h_eq
  simp only at h_wp
  rw [← h_wp]
  -- Now show: p.wp (G ∘ fst) σ₀ = (p >>= a => convert >>= pure a).wp (G ∘ fst) σ₀.
  rw [wp_bind]
  congr 1
  funext aσ_p
  obtain ⟨a, σ_p⟩ := aσ_p
  -- Compute the inner wp on convert >>= pure a.
  show G a = (convert >>= fun _ => (Pure.pure a : Program state α)).wp
                (fun aσ : α × state => G aσ.1) σ_p
  rw [wp_bind, wp_pure]
  -- Goal: G a = convert.wp (fun aσ_c : Unit × state => G a) σ_p.
  show G a = convert.wp (fun _ : Unit × state => G a) σ_p
  rw [convert_wp_const]

/-- **Value marginal**: SubProb-level statement of the transfer. -/
theorem Program.transfer_value_marginal {α : Type}
    {p q : Program state α}
    (h_transfer : Program.transfer p q)
    (h_absorb : (convert >>= fun _ => q) = q)
    (σ₀ : state) :
    (p σ₀ >>= fun aσ => (Pure.pure aσ.1 : SubProbability α))
  = (q σ₀ >>= fun aσ => (Pure.pure aσ.1 : SubProbability α)) := by
  apply Subtype.ext
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace (α × state) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  show MeasureTheory.Measure.bind (p σ₀).1 (fun aσ : α × state =>
          (@MeasureTheory.Measure.dirac α ⊤ aσ.1)) A
     = MeasureTheory.Measure.bind (q σ₀).1 (fun aσ : α × state =>
          (@MeasureTheory.Measure.dirac α ⊤ aσ.1)) A
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
      MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  -- Goal: ∫⁻ aσ, dirac aσ.1 A ∂(p σ₀).1 = ∫⁻ aσ, dirac aσ.1 A ∂(q σ₀).1.
  -- This is p.wp (fun aσ => dirac aσ.1 A) σ₀ = q.wp (...) σ₀, where the test
  -- function factors as G aσ.1 with G = fun a => dirac a A.
  exact Program.transfer_wp_value h_transfer h_absorb
    (fun a : α => (@MeasureTheory.Measure.dirac α ⊤ a) A) σ₀
