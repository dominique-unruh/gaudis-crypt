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
noncomputable instance : DecidableEq output := Classical.decEq output


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

theorem lazy_init_convert_eq_random_oracle_init :
   lazy_init_convert = random_oracle_init := by
   apply Program.ext_of_wp
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

/-- `lazy_query` only reads and writes `random_oracle_state`. -/
theorem lazy_query_inRange_ro (inp : input) :
    (lazy_query inp).inRange random_oracle_state.range := by
  refine Program.inRange_bind (Program.inRange_get _) ?_
  intro h
  cases h inp with
  | some x => exact Program.inRange_pure _ _
  | none =>
    refine Program.inRange_bind ?_ ?_
    · exact Program.inRange_mono Program.inRange_uniform bot_le
    · intro value
      refine Program.inRange_bind (Program.inRange_set _ _) ?_
      intro _
      exact Program.inRange_pure _ _


noncomputable def lazy_query_conv (inp : input) :  Program state Unit := do
  let _ <- lazy_query inp
  convert

noncomputable def conv_random_oracle (inp : input) :  Program state Unit := do
  convert
  let _ <- random_oracle_query inp


-- `lazy_query_conv_eq_conv_random_oracle` (Unit-form: `lazy_query_conv inp = conv_random_oracle inp`) is
-- derived from the value-tracking variant `lazy_query_convert_cont_eq_convert_random_oracle_query` below. The actual
-- arithmetic lives in `lazy_query_convert_eq_convert_random_oracle_query`.

/-- **Sum-over-`Function.update` reorganization** (would-be-generic). Used by
    `lazy_query_convert_eq_convert_random_oracle_query`. Cannot be moved out of this file as-is because the local
    `sorry`'d `Fintype (a → b)` instance below shadows Mathlib's
    `Pi.instFintype`, causing type-class instance mismatches at the call site
    if the lemma is elaborated in a module that doesn't see the local
    instance. Move once the duplicate Fintype instance is removed. -/
private lemma sum_update_eq_card_mul_sum {α β : Type*}
    [DecidableEq α] [Fintype α] [Fintype β]
    (i : α) (G : (α → β) → ENNReal) :
    ∑ v : β, ∑ y : α → β, G (Function.update y i v)
    = (Fintype.card β : ENNReal) * ∑ z : α → β, G z := by
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
lemma convert_wp_eq (f : Program.Post state Unit) (s : state) :
    convert.wp f s = ∑ y : input → output,
      f ((), random_oracle_state.set
            (fun x => some ((random_oracle_state.get s x).getD (y x))) s) /
      (Fintype.card (input → output) : ENNReal) := by
  simp [convert, wp_bind, wp_set, wp_get, wp_uniform]

/- `convert` commutes with `Program.set v x` for any `v` disjoint from `random_oracle_state`. -/
private theorem convert_commutes_set {α : Type} (v : Variable α) [disjoint v random_oracle_state]
    (x : α) :
    (Program.set v x >>= fun _ => convert) = (convert >>= fun _ => Program.set v x) := by
  apply Program.ext_of_wp
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
theorem convert_commutes_get {α β : Type} (v : Variable α)
    [disjoint v random_oracle_state] (k : α → Program state β) :
    (Program.get v >>= fun y => convert >>= fun _ => k y)
    = (convert >>= fun _ => Program.get v >>= k) := by
  apply Program.ext_of_wp
  intro f
  funext s
  simp only [wp_bind, wp_get]
  rw [convert_wp_eq, convert_wp_eq]
  apply Finset.sum_congr rfl
  intro y _
  rw [v_get_RO_set_disjoint]

/- Value-passing variant of lazy_query_conv_eq_conv_random_oracle: the lazy_query result is preserved across `convert`. -/
theorem lazy_query_convert_eq_convert_random_oracle_query (inp : input) :
    (lazy_query inp >>= fun v => convert >>= fun _ => pure v) =
    (convert >>= fun _ => random_oracle_query inp) := by
  apply Program.ext_of_wp
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
private theorem lazy_query_convert_cont_eq_convert_random_oracle_query {β : Type} (inp : input) (k : output → Program state β) :
    (lazy_query inp >>= fun v => convert >>= fun _ => k v)
  = (convert >>= fun _ => random_oracle_query inp >>= k) := by
  have h1 : (lazy_query inp >>= fun v => convert >>= fun _ => k v)
        = (lazy_query inp >>= fun v => convert >>= fun _ => pure v) >>= k := by
    rw [Program.bind_assoc]
    congr 1; funext v
    rw [Program.bind_assoc]
    congr 1; funext _
    rw [Program.pure_bind]
  have h2 : (convert >>= fun _ => random_oracle_query inp >>= k)
        = (convert >>= fun _ => random_oracle_query inp) >>= k := by
    rw [Program.bind_assoc]
  rw [h1, h2, lazy_query_convert_eq_convert_random_oracle_query]

/-- Unit-form lazy/eager bridge: `lazy_query inp; convert = convert; random_oracle_query inp`
    (the trailing `random_oracle_query` result is discarded on both sides).
    Derived from the value-tracking `lazy_query_convert_cont_eq_convert_random_oracle_query` by specializing `k := pure ()`. -/
theorem lazy_query_conv_eq_conv_random_oracle (inp : input) :
    lazy_query_conv inp = conv_random_oracle inp := by
  change (lazy_query inp >>= fun _ => convert)
       = (convert >>= fun _ => random_oracle_query inp >>= fun _ => pure ())
  rw [show (lazy_query inp >>= fun _ : output => (convert : Program state Unit))
        = (lazy_query inp >>= fun _ : output =>
            convert >>= fun _ : Unit => (pure () : Program state Unit))
        from by congr 1; funext _; exact (Program.bind_pure convert).symm]
  exact lazy_query_convert_cont_eq_convert_random_oracle_query inp (fun _ => pure ())

/- Pushing `convert` past the `let inp ← get oracle_input; let v ← lazy_query inp; set oracle_output v`
   piece. -/
theorem query_set_convert_eq :
    ((Program.get oracle_input >>= fun inp =>
      lazy_query inp >>= fun v =>
      Program.set oracle_output v) >>= fun _ => convert)
  = (convert >>= fun _ =>
      Program.get oracle_input >>= fun inp =>
      random_oracle_query inp >>= fun v =>
      Program.set oracle_output v) := by
  simp_rw [Program.bind_assoc, convert_commutes_set, lazy_query_convert_cont_eq_convert_random_oracle_query]
  exact convert_commutes_get oracle_input _

/- Factor `convert` out of an `if`: if the then-branch starts with `convert` and the else-branch
   is `convert`, we can move `convert` outside. -/
lemma if_factor_convert (b : Bool) (X : Program state Unit) :
    (if b = true then convert >>= fun _ => X else convert)
  = convert >>= fun _ => (if b = true then X else pure ()) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (Program.bind_pure convert).symm
  · rfl
