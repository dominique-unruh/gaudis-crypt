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

-- `claim_2` (Unit-form: `lazy_query_conv inp = conv_random_oracle inp`) is
-- derived from the value-tracking variant `claim_2_cont` below. The actual
-- arithmetic lives in `claim_2_strong`.

/-! ## Phase 4 — Oracle loops parameterised by an adversary

Below, `adv` and `h_adv` are *parameters* (via a `variable` declaration), not
axioms. Every `oracle_loop`-style definition and `claim_3`–`claim_5*`-style
theorem in this section is parameterised over an arbitrary adversary
`adv : Program state Unit` together with its RO-disjointness hypothesis
`h_adv : adv.inRange random_oracle_state.compl.range`.

This enables instantiation with wrapped/composed adversaries (CR reductions,
hybrid games, etc.) without re-axiomatising or re-deriving the framework. -/

section AdvParam

variable (adv : Program state Unit)

noncomputable def adv_conv : Program state Unit := do
  adv
  convert

noncomputable def conv_adv : Program state Unit := do
  convert
  adv

variable (h_adv : adv.inRange random_oracle_state.compl.range)


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

include h_adv in
theorem claim_3 : adv_conv adv = conv_adv adv := by
  change (adv >>= fun _ => convert) = (convert >>= fun _ => adv)
  -- Disjointness of the lens-complement with the lens itself (an equality, hence ≤).
  have h_disj : random_oracle_state.compl.range ≤ (random_oracle_state.range)ᶜ :=
    le_of_eq (LensRange.complement_range _)
  -- Pair-output commutation from the headline lemma.
  have h_commute : (adv >>= fun x => convert >>= fun y => pure (x, y))
                 = (convert >>= fun y => adv >>= fun x => pure (x, y)) :=
    Program.commute_of_disjoint_lens h_adv convert_inRange_ro h_disj
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
    rw [Program.bind_assoc]
    congr 1; funext v
    rw [Program.bind_assoc]
    congr 1; funext _
    rw [Program.pure_bind]
  have h2 : (convert >>= fun _ => random_oracle_query inp >>= k)
        = (convert >>= fun _ => random_oracle_query inp) >>= k := by
    rw [Program.bind_assoc]
  rw [h1, h2, claim_2_strong]

/-- Unit-form lazy/eager bridge: `lazy_query inp; convert = convert; random_oracle_query inp`
    (the trailing `random_oracle_query` result is discarded on both sides).
    Derived from the value-tracking `claim_2_cont` by specializing `k := pure ()`. -/
theorem claim_2 (inp : input) :
    lazy_query_conv inp = conv_random_oracle inp := by
  change (lazy_query inp >>= fun _ => convert)
       = (convert >>= fun _ => random_oracle_query inp >>= fun _ => pure ())
  rw [show (lazy_query inp >>= fun _ : output => (convert : Program state Unit))
        = (lazy_query inp >>= fun _ : output =>
            convert >>= fun _ : Unit => (pure () : Program state Unit))
        from by congr 1; funext _; exact (Program.bind_pure convert).symm]
  exact claim_2_cont inp (fun _ => pure ())

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
  simp_rw [Program.bind_assoc, convert_commutes_set, claim_2_cont]
  exact convert_commutes_get oracle_input _

/- Factor `convert` out of an `if`: if the then-branch starts with `convert` and the else-branch
   is `convert`, we can move `convert` outside. -/
private lemma if_factor_convert (b : Bool) (X : Program state Unit) :
    (if b = true then convert >>= fun _ => X else convert)
  = convert >>= fun _ => (if b = true then X else pure ()) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (Program.bind_pure convert).symm
  · rfl

/- Body of the loop with `convert` appended on the lazy side equals `convert` prepended
   on the eager side. -/
include h_adv in
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
  rw [Program.bind_assoc]
  -- LHS: adv >>= fun _ => ((get want_more >>= ...) >>= convert)
  -- Step 2: bind_assoc inside, then distribute over if.
  conv_lhs =>
    arg 2; ext _
    rw [Program.bind_assoc]
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
          Program.pure_bind () _]
    rw [query_set_convert_eq]
    rw [if_factor_convert]
  -- Now LHS: adv >>= fun _ => (get want_more >>= fun b => convert >>= ...)
  -- Step 3: push convert past get want_more.
  conv_lhs =>
    arg 2; ext _
    rw [convert_commutes_get]
  -- LHS: adv >>= fun _ => (convert >>= fun _ => get want_more >>= ...)
  -- Step 4: bind_assoc reverse, then claim_3, then bind_assoc.
  rw [← Program.bind_assoc,
      show (adv >>= fun _ => convert) = (convert >>= fun _ => adv) from claim_3 adv h_adv,
      Program.bind_assoc]
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

include h_adv in
private theorem body_def_convert_eq :
    (loop_body_lazy adv >>= fun _ => convert) = (convert >>= fun _ => loop_body_eager adv) :=
  body_convert_eq adv h_adv

/- The intermediate iteration: same as `while_iteration` for the lazy body, but with `convert`
   in the else branch (representing "loop terminates, then convert"). -/
private noncomputable def Ψ_iter :
    (Unit → Program state Unit) →𝒄 (Unit → Program state Unit) :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Unit → Program state Unit) => fun () =>
    do if ← Program.get want_more then
         loop_body_lazy adv
         fp ()
       else convert

/- Kleene induction on the lazy side: at every finite iterate, the lazy iterate composed with
   `convert` equals the same iterate of `Ψ_iter`. -/
private lemma loop_kleene_lazy : ∀ n : ℕ,
    (((while_iteration (Program.get want_more) (loop_body_lazy adv))^[n]
      (⊥ : Unit → Program state Unit)) () >>= (fun _ => convert))
    = ((Ψ_iter adv)^[n] (⊥ : Unit → Program state Unit)) () := by
  intro n
  induction n with
  | zero =>
    change ((⊥ : Unit → Program state Unit) () >>= fun _ => convert) = (⊥ : Unit → Program state Unit) ()
    change ((⊥ : Program state Unit) >>= fun _ => convert) = (⊥ : Program state Unit)
    exact Program.bot_bind _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    -- LHS: (while_iteration cond body_lazy (F_lazy^[n] ⊥)) () >>= convert
    -- RHS: Ψ_iter (Ψ_iter^[n] ⊥) ()
    -- Unfold while_iteration and Ψ_iter, apply if-distribute, then ih.
    change (((Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_lazy adv >>= fun _ =>
                  ((while_iteration (Program.get want_more) (loop_body_lazy adv))^[n] ⊥) ()
              else (pure () : Program state Unit)) >>= fun _ => convert)
        = (Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_lazy adv >>= fun _ => ((Ψ_iter adv)^[n] ⊥) ()
              else convert
    rw [Program.bind_assoc]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      rw [Program.bind_assoc]
      congr 1; funext _
      exact ih
    · simp only [h, if_false]
      exact Program.pure_bind () _

/- Kleene induction on the eager side: `convert` prepended to each eager iterate equals the
   same iterate of `Ψ_iter`. -/
include h_adv in
private lemma loop_kleene_eager : ∀ n : ℕ,
    convert >>= (fun _ => ((while_iteration (Program.get want_more) (loop_body_eager adv))^[n]
      (⊥ : Unit → Program state Unit)) ())
    = ((Ψ_iter adv)^[n] (⊥ : Unit → Program state Unit)) () := by
  intro n
  induction n with
  | zero =>
    change (convert >>= fun _ => (⊥ : Unit → Program state Unit) ()) = (⊥ : Unit → Program state Unit) ()
    change (convert >>= fun _ => (⊥ : Program state Unit)) = (⊥ : Program state Unit)
    exact Program.bind_bot _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    -- LHS: convert >>= F_eager (F_eager^[n] ⊥) ()
    -- RHS: Ψ_iter (Ψ_iter^[n] ⊥) ()
    change (convert >>= fun _ => (Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_eager adv >>= fun _ =>
                  ((while_iteration (Program.get want_more) (loop_body_eager adv))^[n] ⊥) ()
              else (pure () : Program state Unit))
        = (Program.get want_more) >>= fun b =>
              if b = true then
                loop_body_lazy adv >>= fun _ => ((Ψ_iter adv)^[n] ⊥) ()
              else convert
    -- Push convert past get want_more.
    rw [show (convert >>= fun _ => (Program.get want_more) >>=
              fun b => if b = true then loop_body_eager adv >>= fun _ =>
                  ((while_iteration (Program.get want_more) (loop_body_eager adv))^[n] ⊥) ()
                else (pure () : Program state Unit))
            = ((Program.get want_more) >>= fun b => convert >>= fun _ =>
                if b = true then loop_body_eager adv >>= fun _ =>
                  ((while_iteration (Program.get want_more) (loop_body_eager adv))^[n] ⊥) ()
                else (pure () : Program state Unit)) from by
        rw [← convert_commutes_get]]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      -- LHS: convert >>= body_eager >>= F_eager^[n] ⊥ ()
      -- Use body_def_convert_eq to swap convert and body
      rw [← Program.bind_assoc]
      rw [show (convert >>= fun _ => loop_body_eager adv)
              = (loop_body_lazy adv >>= fun _ => convert) from
            (body_def_convert_eq adv h_adv).symm]
      rw [Program.bind_assoc]
      congr 1; funext _
      exact ih
    · simp only [h, if_false]
      exact Program.bind_pure _

/- Lift the Kleene iterate identity to the lfp via ω-continuity of bind. -/
include h_adv in
private theorem loop_coupling :
    ((while_loop (Program.get want_more) (loop_body_lazy adv)) >>= fun _ => convert)
  = (convert >>= fun _ => while_loop (Program.get want_more) (loop_body_eager adv)) := by
  -- Both sides equal Ψ_iter.lfp ().
  let F_lazy := while_iteration (Program.get want_more) (loop_body_lazy adv)
  let F_eager := while_iteration (Program.get want_more) (loop_body_eager adv)
  have hL_chain : ∀ n, ((F_lazy^[n] ⊥ : Unit → Program state Unit) () >>= (fun _ => convert))
                     = ((Ψ_iter adv)^[n] ⊥ : Unit → Program state Unit) () := loop_kleene_lazy adv
  have hE_chain : ∀ n, convert >>= (fun _ => (F_eager^[n] ⊥ : Unit → Program state Unit) ())
                     = ((Ψ_iter adv)^[n] ⊥ : Unit → Program state Unit) () :=
    loop_kleene_eager adv h_adv
  -- ω-continuity of `· >>= convert` and `convert >>= ·`.
  have h_bind_convert_cont :
      OmegaCompletePartialOrder.ωScottContinuous
        (fun (m : Program state Unit) => m >>= fun _ => convert) := by fun_prop
  have h_convert_bind_cont :
      OmegaCompletePartialOrder.ωScottContinuous
        (fun (m : Program state Unit) => convert >>= fun _ => m) := by fun_prop
  change (F_lazy.lfp ()) >>= (fun _ => convert) = convert >>= (fun _ => F_eager.lfp ())
  let chain_lazy : OmegaCompletePartialOrder.Chain (Unit → Program state Unit) :=
    ⟨fun n => F_lazy^[n] ⊥,
     Monotone.monotone_iterate_of_le_map F_lazy.monotone (OrderBot.bot_le _)⟩
  let chain_eager : OmegaCompletePartialOrder.Chain (Unit → Program state Unit) :=
    ⟨fun n => F_eager^[n] ⊥,
     Monotone.monotone_iterate_of_le_map F_eager.monotone (OrderBot.bot_le _)⟩
  have hLfpL : F_lazy.lfp = OmegaCompletePartialOrder.ωSup chain_lazy := rfl
  have hLfpE : F_eager.lfp = OmegaCompletePartialOrder.ωSup chain_eager := rfl
  have hLfpL_at : F_lazy.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_lazy.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by
    rw [hLfpL]; rfl
  have hLfpE_at : F_eager.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_eager.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by
    rw [hLfpE]; rfl
  rw [hLfpL_at, hLfpE_at]
  rw [h_bind_convert_cont.map_ωSup]
  rw [h_convert_bind_cont.map_ωSup]
  congr 1
  ext n
  exact (hL_chain n).trans (hE_chain n).symm

include h_adv in
theorem claim_4 :
    (oracle_loop adv lazy_init lazy_query >>= fun b => convert >>= fun _ => pure b)
  = oracle_loop adv random_oracle_init random_oracle_query
  := by
  -- Fold the inline bodies as `loop_body_lazy` / `loop_body_eager` (definitionally equal).
  change ((Program.set want_more true >>= fun _ =>
            lazy_init >>= fun _ =>
              while_loop (Program.get want_more) (loop_body_lazy adv) >>= fun _ =>
                Program.get adversary_result) >>= fun b => convert >>= fun _ => pure b)
       = (Program.set want_more true >>= fun _ =>
            random_oracle_init >>= fun _ =>
              while_loop (Program.get want_more) (loop_body_eager adv) >>= fun _ =>
                Program.get adversary_result)
  -- Flatten binds.
  simp_rw [Program.bind_assoc]
  -- Step 1: tail rewrite.
  rw [show ((Program.get adversary_result) >>= fun b => convert >>= fun _ => pure b)
        = (convert >>= fun _ => Program.get adversary_result) from by
      rw [convert_commutes_get]
      congr 1; funext b; exact Program.bind_pure _]
  -- Step 2: regroup `while_lazy >>= _ => convert` and apply loop_coupling.
  rw [show (∀ (W : Program state Unit) (K : Program state Bool),
        (W >>= fun _ => convert >>= fun _ => K) = ((W >>= fun _ => convert) >>= fun _ => K))
        from fun W K => (Program.bind_assoc _ _ _).symm]
  rw [loop_coupling adv h_adv]
  rw [Program.bind_assoc]
  -- Step 3: regroup `lazy_init >>= _ => convert` and apply claim_1.
  rw [show (∀ (L : Program state Unit) (K : Program state Bool),
        (L >>= fun _ => convert >>= fun _ => K) = ((L >>= fun _ => convert) >>= fun _ => K))
        from fun L K => (Program.bind_assoc _ _ _).symm]
  rw [show (lazy_init >>= fun _ => convert) = random_oracle_init from claim_1]

include h_adv in
/-- `claim_5`: the lazy and eager oracle loops agree on every postcondition that is
    invariant under writes to `random_oracle_state` (i.e., every postcondition that only
    depends on the *non-RO* part of state).

    Intuitively: an adversary that observes only its own global variables (none of which
    are the random oracle's internal state) cannot tell lazy from eager. -/
theorem claim_5 (F : Bool × state → ENNReal)
    (hF_inv : ∀ (b : Bool) (σ : state) (x : input → Option output),
        F (b, random_oracle_state.set x σ) = F (b, σ)) :
    (oracle_loop adv lazy_init lazy_query).wp F
  = (oracle_loop adv random_oracle_init random_oracle_query).wp F := by
  -- Step 1: convert composed with `pure b` is wp-transparent for RO-invariant F.
  have h_convert : ∀ (b : Bool) (σ : state),
      (convert >>= fun _ : Unit => (pure b : Program state Bool)).wp F σ = F (b, σ) := by
    intros b σ
    simp only [wp_bind, wp_pure]
    rw [convert_wp_eq]
    simp_rw [hF_inv]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard_pos : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_pos.ne'
    have hcard_top : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [ENNReal.mul_div_cancel hcard_pos hcard_top]
  have h4_wp := congr_arg (fun prog : Program state Bool => prog.wp F) (claim_4 adv h_adv)
  simp only at h4_wp
  rw [wp_bind] at h4_wp
  have h_eq : (fun (bσ : Bool × state) =>
                  (convert >>= fun _ : Unit => (pure bσ.1 : Program state Bool)).wp F bσ.2)
            = (fun (bσ : Bool × state) => F (bσ.1, bσ.2)) := by
    funext bσ; exact h_convert bσ.1 bσ.2
  rw [h_eq] at h4_wp
  exact h4_wp

include h_adv in
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
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state => (pure (bσ.1, h bσ.2) : SubProbability (Bool × β)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state => (pure (bσ.1, h bσ.2) : SubProbability (Bool × β))) := by
  apply Subtype.ext
  letI : MeasurableSpace (Bool × state) := ⊤
  letI : MeasurableSpace (Bool × β) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  show MeasureTheory.Measure.bind (oracle_loop adv lazy_init lazy_query σ₀).1
        (fun bσ : Bool × state =>
          @MeasureTheory.Measure.dirac (Bool × β) ⊤ (bσ.1, h bσ.2)) A
    = MeasureTheory.Measure.bind
        (oracle_loop adv random_oracle_init random_oracle_query σ₀).1
        (fun bσ : Bool × state =>
          @MeasureTheory.Measure.dirac (Bool × β) ⊤ (bσ.1, h bσ.2)) A
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  exact congr_fun (claim_5 adv h_adv
      (fun bσ : Bool × state =>
        (@MeasureTheory.Measure.dirac (Bool × β) ⊤ (bσ.1, h bσ.2)) A)
      (by intros b σ x; simp only; rw [h_inv])) σ₀

include h_adv in
/-- **Form (a) of `claim_5` — lens-complement projection**.

    The joint distribution of (adv's bit, the entire non-RO part of state) is
    identical under lazy and eager RO.

    `random_oracle_state.compl.get` is the lens-complement getter: it returns
    the equivalence class of σ modulo "differs only in RO content". This is
    the most concrete glob-style form — the returned type is a `Quotient` of
    state by the RO-equivalence, with no `Program.range` machinery involved. -/
theorem claim_5_compl (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid))) := by
  refine claim_5_subprob adv h_adv random_oracle_state.compl.get ?_ σ₀
  intro σ x
  exact Quotient.sound ⟨random_oracle_state.get σ,
    (random_oracle_state.set_set σ x (random_oracle_state.get σ)).trans
      (random_oracle_state.get_set σ)⟩

include h_adv in
/-- **Form (c) of `claim_5` — `Program.glob adv`**.

    The joint distribution of (adv's bit, what `adv` can see/modify) is
    identical under lazy and eager RO.

    This is the natural cryptographic indistinguishability statement:
    `(Program.glob adv).get bσ.2` is the equivalence class of `bσ.2` under
    `(adv.range)ᶜ`-orbits — i.e., "everything adv could possibly observe or
    affect", quotiented by symmetries outside adv's reach.

    Corollary of `claim_5_subprob` applied to `(Program.glob adv).get`. The
    RO-invariance of this projection follows from `h_adv` via
    the inclusion `random_oracle_state.range ≤ (adv.range)ᶜ`. -/
theorem claim_5_glob (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals))) := by
  refine claim_5_subprob adv h_adv (Program.glob adv).get ?_ σ₀
  intro σ x
  apply Quotient.sound
  change Relation.EqvGen
      (fun s s' : state => ∃ f ∈ ((adv.range)ᶜ : LensRange state).updates, f s = s')
      (random_oracle_state.set x σ) σ
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  refine ⟨random_oracle_state.set x, ?_, rfl⟩
  have h_in_ro : random_oracle_state.set x ∈ random_oracle_state.range.updates := by
    refine ⟨Function.const _ x, Set.mem_univ _, ?_⟩
    funext σ'
    simp [Lens.update]
  have hadv_le : adv.range ≤ random_oracle_state.compl.range :=
    sInf_le h_adv
  have h_le : random_oracle_state.range ≤ (adv.range)ᶜ := by
    have hflip : (random_oracle_state.compl.range)ᶜ ≤ (adv.range)ᶜ := by
      change (Submonoid.centralizer random_oracle_state.compl.range.updates).carrier
           ⊆ (Submonoid.centralizer adv.range.updates).carrier
      exact Submonoid.centralizer_le hadv_le
    rwa [LensRange.complement_range, LensRange.compl_compl] at hflip
  exact h_le h_in_ro

end AdvParam

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

/-- `convert` is absorbed by any program that starts with `random_oracle_init`:
    `convert >>= (random_oracle_init >>= rest) = random_oracle_init >>= rest`.
    Used by `convert_*_experiment_eager` lemmas (where the experiment starts
    with `random_oracle_init`) to absorb a preceding `convert` step. -/
lemma convert_bind_random_oracle_init_bind {α : Type} (rest : Program state α) :
    (convert >>= fun _ : Unit =>
      random_oracle_init >>= fun _ : Unit => rest)
    = random_oracle_init >>= fun _ : Unit => rest := by
  rw [← Program.bind_assoc, convert_random_oracle_init]

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
    rw [Program.bind_assoc]; congr 1; funext a
    rw [Program.bind_assoc]; congr 1; funext _
    rw [Program.pure_bind]
  have hR : (convert >>= fun b => p >>= fun a => pure (a, b)) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program state α))
          = (convert >>= fun _ => p) := by
    rw [Program.bind_assoc]
    congr 1; funext _
    rw [Program.bind_assoc]
    rw [show (fun a : α => pure (a, ()) >>=
              (fun ab : α × Unit => (Pure.pure ab.1 : Program state α)))
          = (fun a : α => (Pure.pure a : Program state α)) from by
        funext a; rw [Program.pure_bind]]
    exact Program.bind_pure _
  rw [← hL, h_commute, hR]

/-- Any program in `v.range`, for a `v` disjoint from `random_oracle_state`,
    transfers to itself. Convenience composition of `transfer_refl_of_inRange_compl`,
    `inRange_mono`, and `Lens.range_le_compl_of_disjoint`. -/
lemma Program.transfer_of_inRange_disjoint {α : Type} [Countable α]
    (p : Program state α) {β : Type} (v : Lens β state)
    [disjoint v random_oracle_state]
    (hp : p.inRange v.range) :
    Program.transfer p p :=
  Program.transfer_refl_of_inRange_compl
    (Program.inRange_mono hp
      (Lens.range_le_compl_of_disjoint v random_oracle_state))

/-- `Program.set v x` transfers to itself when `v` is disjoint from `random_oracle_state`.
    Common one-liner replacing the `transfer_of_inRange_disjoint _ v (inRange_set _ _)` chain. -/
lemma Program.transfer_set_of_disjoint_ro {α : Type}
    (v : Lens α state) [disjoint v random_oracle_state] (x : α) :
    Program.transfer (Program.set v x) (Program.set v x) :=
  Program.transfer_of_inRange_disjoint _ v (Program.inRange_set v x)

/-- `Program.get v` transfers to itself when `v` is disjoint from `random_oracle_state`. -/
lemma Program.transfer_get_of_disjoint_ro {α : Type} [Countable α]
    (v : Lens α state) [disjoint v random_oracle_state] :
    Program.transfer (Program.get v) (Program.get v) :=
  Program.transfer_of_inRange_disjoint _ v (Program.inRange_get v)

/-- `Program.uniform` transfers to itself (it doesn't touch state at all). -/
lemma Program.transfer_uniform {α : Type} [Countable α] [Fintype α] [Nonempty α] :
    Program.transfer (Program.uniform : Program state α) Program.uniform :=
  Program.transfer_refl_of_inRange_compl
    (Program.inRange_mono Program.inRange_uniform bot_le)

/-- Bind closure: transfer chains under `>>=`. -/
lemma Program.transfer_bind {α β : Type}
    {p q : Program state α} {p' q' : α → Program state β}
    (h : Program.transfer p q) (h' : ∀ a, Program.transfer (p' a) (q' a)) :
    Program.transfer (p >>= p') (q >>= q') := by
  show ((p >>= p') >>= fun b => convert >>= fun _ => pure b)
      = (convert >>= fun _ => q >>= q')
  rw [Program.bind_assoc]
  conv_lhs =>
    rhs; ext a
    rw [show (p' a >>= fun b => convert >>= fun _ => (Pure.pure b : Program state β))
          = (convert >>= fun _ => q' a) from h' a]
  conv_lhs =>
    rhs; ext a
    rw [show (convert >>= fun _ => q' a)
          = (convert >>= fun _ => (Pure.pure a : Program state α)) >>= q' from by
        rw [Program.bind_assoc]; congr 1; funext _; rw [Program.pure_bind]]
  rw [← Program.bind_assoc]
  rw [show (p >>= fun a => convert >>= fun _ => (Pure.pure a : Program state α))
        = (convert >>= fun _ => q) from h]
  rw [Program.bind_assoc]

/-- Pure transfers to itself. -/
lemma Program.transfer_pure {α : Type} (a : α) :
    Program.transfer (Pure.pure a : Program state α) (Pure.pure a) := by
  show ((Pure.pure a : Program state α) >>= fun a' => convert >>= fun _ => pure a')
      = (convert >>= fun _ => Pure.pure a)
  rw [Program.pure_bind]

/-- `lazy_init` transfers to `random_oracle_init`. -/
lemma Program.transfer_lazy_init :
    Program.transfer lazy_init random_oracle_init := by
  show (lazy_init >>= fun _ => convert >>= fun _ => (Pure.pure () : Program state Unit))
      = (convert >>= fun _ => random_oracle_init)
  have hL : (lazy_init >>= fun _ => convert >>= fun _ => (Pure.pure () : Program state Unit))
          = lazy_init >>= fun _ => convert := by
    congr 1; funext _
    exact Program.bind_pure _
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


/-- `(lazy_query inp >>= set oracle_output)` is in `L.compl.range` for any lens
    `L` disjoint from both `random_oracle_state` and `oracle_output`. Useful for
    `wp_strengthen_lens_preserved` arguments downstream. -/
lemma lazy_query_then_set_oracle_output_inRange_compl
    {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_output L]
    (inp : input) :
    (lazy_query inp >>= fun y => Program.set oracle_output y).inRange
        L.compl.range := by
  refine Program.inRange_bind ?_ ?_
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state L)
  · intro y
    exact Program.set_inRange_compl_of_disjoint oracle_output L _

/-! ### RO-key-level properties of `lazy_query` + `set oracle_output`

These are the workhorse lemmas for "deferred sampling" arguments in
random-oracle proofs:

- `lazy_query_set_oracle_output_preserves_RO_at_other_key`: a query at
  `inp ≠ k` doesn't change `RO[k]`, so we can strengthen the post with
  the `RO[k]`-preserved condition.
- `RO_setentry_neq_commutes_lazy_query_set_oracle_output`: writes to
  different RO keys commute past the query. This is the mechanical core
  of "averaged invariance" arguments for indistinct-key reasoning.
-/

/-- `(lazy_query inp >>= set oracle_output)` preserves `RO[k]` for `inp ≠ k`.
    More precisely, the wp can be strengthened with the `RO[k]`-preserved
    condition. -/
lemma lazy_query_set_oracle_output_preserves_RO_at_other_key
    (inp k : input) (h_neq : inp ≠ k) (σ : state) (F : Unit × state → ENNReal) :
    (lazy_query inp >>= fun y_lq => Program.set oracle_output y_lq).wp F σ
    = (lazy_query inp >>= fun y_lq => Program.set oracle_output y_lq).wp
        (fun aσ_lq =>
          if random_oracle_state.get aσ_lq.2 k = random_oracle_state.get σ k
          then F aσ_lq else 0) σ := by
  haveI _disj_oo_ro : disjoint oracle_output random_oracle_state := disjoint_oracle_output_ro
  simp only [lazy_query, wp_bind, wp_get, wp_uniform, wp_pure, wp_set]
  cases h_eq : random_oracle_state.get σ inp with
  | some v =>
    simp only [h_eq, wp_pure]
    have h_RO_pres : random_oracle_state.get (oracle_output.set v σ) k
        = random_oracle_state.get σ k := by
      rw [random_oracle_state.get_of_disjoint_set]
    rw [if_pos h_RO_pres]
  | none =>
    simp only [h_eq, wp_bind, wp_uniform, wp_set, wp_pure]
    congr 1
    funext v
    have h_RO_pres : random_oracle_state.get
        (oracle_output.set v (random_oracle_state.set
          (fun x_1 => if x_1 = inp then some v else random_oracle_state.get σ x_1) σ)) k
        = random_oracle_state.get σ k := by
      rw [random_oracle_state.get_of_disjoint_set oracle_output v,
          random_oracle_state.set_get]
      simp only [if_neg (Ne.symm h_neq)]
    rw [if_pos h_RO_pres]

/-- Fine-grained RO commutativity: a write to `RO[x]` commutes with
    `(lazy_query inp >>= set oracle_output)` when `inp ≠ x`. Writes to
    different RO keys commute, and `oracle_output` is disjoint from RO.
    Mechanical core of averaged-invariance MISS-case arguments. -/
lemma RO_setentry_neq_commutes_lazy_query_set_oracle_output
    (inp x : input) (h_neq : inp ≠ x) (y : output) (σ : state)
    (F : Unit × state → ENNReal) :
    (lazy_query inp >>= fun y_lq => Program.set oracle_output y_lq).wp F
      (random_oracle_state.set (fun k => if k = x then some y
                                       else random_oracle_state.get σ k) σ)
    = (lazy_query inp >>= fun y_lq => Program.set oracle_output y_lq).wp
      (fun aσ_lq => F (aσ_lq.1, random_oracle_state.set
                              (fun k => if k = x then some y
                                       else random_oracle_state.get aσ_lq.2 k) aσ_lq.2))
      σ := by
  haveI _disj_oo_ro : disjoint oracle_output random_oracle_state := disjoint_oracle_output_ro
  have h_state_eq : ∀ (v : output) (σ' : state),
      oracle_output.set v (random_oracle_state.set
        (fun k => if k = x then some y else random_oracle_state.get σ' k) σ')
      = random_oracle_state.set
        (fun k => if k = x then some y
                  else random_oracle_state.get (oracle_output.set v σ') k)
        (oracle_output.set v σ') := by
    intro v σ'
    rw [disjoint_oracle_output_ro.commute]
    congr 1
    funext k
    by_cases hk : k = x
    · simp only [if_pos hk]
    · simp only [if_neg hk]
      rw [random_oracle_state.get_of_disjoint_set]
  rw [wp_bind, wp_bind]
  conv_lhs => rw [show (fun aσ_lq : output × state =>
                          (Program.set oracle_output aσ_lq.1).wp F aσ_lq.2)
                    = (fun aσ_lq : output × state =>
                          F ((), oracle_output.set aσ_lq.1 aσ_lq.2))
                  from by funext aσ_lq; rw [wp_set]]
  conv_rhs => rw [show (fun aσ_lq : output × state =>
                          (Program.set oracle_output aσ_lq.1).wp
                            (fun aσ_lq' : Unit × state =>
                              F (aσ_lq'.1, random_oracle_state.set
                                (fun k => if k = x then some y
                                          else random_oracle_state.get aσ_lq'.2 k) aσ_lq'.2))
                            aσ_lq.2)
                    = (fun aσ_lq : output × state =>
                          F ((), random_oracle_state.set
                            (fun k => if k = x then some y
                                      else random_oracle_state.get
                                            (oracle_output.set aσ_lq.1 aσ_lq.2) k)
                            (oracle_output.set aσ_lq.1 aσ_lq.2)))
                  from by funext aσ_lq; rw [wp_set]]
  set σ_xy : state := random_oracle_state.set
    (fun k => if k = x then some y else random_oracle_state.get σ k) σ with σ_xy_def
  have h_RO_xy_inp : random_oracle_state.get σ_xy inp = random_oracle_state.get σ inp := by
    show random_oracle_state.get (random_oracle_state.set _ σ) inp
        = random_oracle_state.get σ inp
    rw [random_oracle_state.set_get, if_neg h_neq]
  simp only [lazy_query, wp_bind, wp_get]
  rw [h_RO_xy_inp]
  cases h_eq : random_oracle_state.get σ inp with
  | some v =>
    simp only [wp_pure]
    congr 1
    rw [σ_xy_def, h_state_eq v σ]
  | none =>
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
    have h_setentry_commute : ∀ v : output,
        random_oracle_state.set
          (fun k => if k = inp then some v
                    else random_oracle_state.get (random_oracle_state.set
                          (fun k' => if k' = x then some y else random_oracle_state.get σ k') σ) k)
          (random_oracle_state.set
            (fun k' => if k' = x then some y else random_oracle_state.get σ k') σ)
        = random_oracle_state.set
          (fun k => if k = x then some y else random_oracle_state.get
              (random_oracle_state.set
                (fun k' => if k' = inp then some v else random_oracle_state.get σ k') σ) k)
          (random_oracle_state.set
            (fun k => if k = inp then some v else random_oracle_state.get σ k) σ) := by
      intro v
      rw [random_oracle_state.set_set, random_oracle_state.set_set]
      congr 1
      funext k
      simp only [random_oracle_state.set_get]
      by_cases hk_x : k = x
      · by_cases hk_inp : k = inp
        · exfalso; exact h_neq (hk_inp.symm.trans hk_x)
        · simp [if_pos hk_x, if_neg hk_inp]
      · by_cases hk_inp : k = inp
        · simp [if_neg hk_x, if_pos hk_inp]
        · simp [if_neg hk_x, if_neg hk_inp]
    congr 1
    funext v
    congr 1
    congr 1
    rw [σ_xy_def, h_setentry_commute v]
    rw [← h_state_eq v
      (random_oracle_state.set
        (fun k => if k = inp then some v else random_oracle_state.get σ k) σ)]


/-! ## Generic adversary + oracle loop primitives

Both `cr_loop_body`/`cr_loop` (in `CollisionResistance.lean`) and
`ow_loop_body`/`ow_loop` (in `OneWayness.lean`) use the *same* shape:
"run the adversary, then perform one oracle call on whatever the adversary
wrote to `oracle_input`, storing the result in `oracle_output`." The
shared abstraction lives here. Game-specific files alias these. -/

/-- One round of an adversary-and-query loop body. Generic over the adversary;
    parameterised over the oracle so it can be instantiated to `lazy_query` or
    `random_oracle_query`. -/
noncomputable def oracle_step (adv : Program state Unit)
    (oracle : input → Program state output) : Program state Unit := do
  adv
  Program.set oracle_output (← oracle (← Program.get oracle_input))

/-- Run `oracle_step adv oracle` for `q` rounds. -/
noncomputable def oracle_loop_n (adv : Program state Unit) :
    ℕ → (input → Program state output) → Program state Unit
  | 0,     _      => pure ()
  | n + 1, oracle => do
      oracle_step adv oracle
      oracle_loop_n adv n oracle

/-- `oracle_step adv` transfers from lazy to eager, provided `adv` is
    RO-disjoint. -/
lemma Program.transfer_oracle_step
    {adv : Program state Unit}
    (h_adv : adv.inRange random_oracle_state.compl.range) :
    Program.transfer (oracle_step adv lazy_query)
                     (oracle_step adv random_oracle_query) := by
  show Program.transfer
    (adv >>= fun _ => Program.get oracle_input >>= fun inp =>
      lazy_query inp >>= fun y => Program.set oracle_output y)
    (adv >>= fun _ => Program.get oracle_input >>= fun inp =>
      random_oracle_query inp >>= fun y => Program.set oracle_output y)
  apply Program.transfer_bind (Program.transfer_refl_of_inRange_compl h_adv)
  intro _
  apply Program.transfer_bind (Program.transfer_get_of_disjoint_ro oracle_input)
  intro inp
  apply Program.transfer_bind (Program.transfer_lazy_query inp)
  intro y
  exact Program.transfer_set_of_disjoint_ro oracle_output y

/-- `oracle_loop_n adv q` transfers from lazy to eager. -/
lemma Program.transfer_oracle_loop_n
    {adv : Program state Unit}
    (h_adv : adv.inRange random_oracle_state.compl.range)
    (q : ℕ) :
    Program.transfer (oracle_loop_n adv q lazy_query)
                     (oracle_loop_n adv q random_oracle_query) := by
  induction q with
  | zero => exact Program.transfer_pure ()
  | succ n ih =>
    show Program.transfer
      (oracle_step adv lazy_query >>= fun _ => oracle_loop_n adv n lazy_query)
      (oracle_step adv random_oracle_query >>=
        fun _ => oracle_loop_n adv n random_oracle_query)
    exact Program.transfer_bind (Program.transfer_oracle_step h_adv) (fun _ => ih)

/-- Generic preservation: `oracle_step adv` stays in `L.compl.range` for any
    lens `L` disjoint from `random_oracle_state`, `oracle_input`, and
    `oracle_output`, provided the adversary stays in `L.compl.range`. -/
lemma oracle_step_inRange_compl {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_input L]
    [disjoint oracle_output L]
    {adv : Program state Unit}
    (h_adv : adv.inRange L.compl.range) :
    (oracle_step adv lazy_query).inRange L.compl.range := by
  show (adv >>= fun _ =>
        Program.get oracle_input >>= fun inp =>
          lazy_query inp >>= fun y =>
            Program.set oracle_output y).inRange L.compl.range
  refine Program.inRange_bind h_adv ?_
  intro _
  refine Program.inRange_bind
    (Program.get_inRange_compl_of_disjoint oracle_input L) ?_
  intro inp
  exact lazy_query_then_set_oracle_output_inRange_compl L inp

/-- Generic preservation lifted to the loop, by induction on `q`. -/
lemma oracle_loop_n_inRange_compl {γ : Type} (L : Lens γ state)
    [disjoint random_oracle_state L]
    [disjoint oracle_input L]
    [disjoint oracle_output L]
    {adv : Program state Unit}
    (h_adv : adv.inRange L.compl.range)
    (q : ℕ) :
    (oracle_loop_n adv q lazy_query).inRange L.compl.range := by
  induction q with
  | zero => exact Program.inRange_pure _ _
  | succ n ih =>
    show (oracle_step adv lazy_query >>= fun _ =>
          oracle_loop_n adv n lazy_query).inRange _
    exact Program.inRange_bind (oracle_step_inRange_compl L h_adv) (fun _ => ih)

/-- **Linear-growth bound for `oracle_loop_n`**. If a single body iteration
    bumps the wp of `f` (against the state-projected post) by at most a
    constant `c`, then `q` iterations bump it by at most `q * c`. Captures
    the standard "loop accumulation" pattern used for both query-budget
    bounds (e.g. each query bumps RO size by ≤ 1) and probability bounds
    (e.g. each query has ≤ 1/N chance of producing a target value). -/
lemma oracle_loop_n_wp_linear_bound
    {adv : Program state Unit}
    {f : state → ENNReal} {c : ENNReal}
    (h_body : ∀ σ, (oracle_step adv lazy_query).wp
                     (fun yσ : Unit × state => f yσ.2) σ ≤ f σ + c)
    (q : ℕ) (σ : state) :
    (oracle_loop_n adv q lazy_query).wp
        (fun yσ : Unit × state => f yσ.2) σ ≤ f σ + (q : ENNReal) * c := by
  induction q generalizing σ with
  | zero =>
    show (pure () : Program state Unit).wp _ σ ≤ _
    rw [wp_pure]; simp
  | succ n ih =>
    show (oracle_step adv lazy_query >>= fun _ =>
          oracle_loop_n adv n lazy_query).wp _ σ ≤ _
    rw [wp_bind]
    calc (oracle_step adv lazy_query).wp (fun yσ : Unit × state =>
            (oracle_loop_n adv n lazy_query).wp
              (fun yσ' : Unit × state => f yσ'.2) yσ.2) σ
        ≤ (oracle_step adv lazy_query).wp (fun yσ : Unit × state =>
            f yσ.2 + (n : ENNReal) * c) σ := by
          apply Program.wp_le_wp_of_le
          intro yσ
          exact ih yσ.2
      _ = (oracle_step adv lazy_query).wp
            (fun yσ : Unit × state => f yσ.2) σ +
          (oracle_step adv lazy_query).wp
            (fun _ : Unit × state => (n : ENNReal) * c) σ := by
          rw [Program.wp_add]
      _ ≤ (f σ + c) + (n : ENNReal) * c := by
          gcongr
          · exact h_body σ
          · exact Program.wp_const_le _ _ _
      _ = f σ + ((n + 1 : ℕ) : ENNReal) * c := by
          push_cast; ring

/-! ### Generic per-query indicator step

The "one lazy_query bumps a state-indicator `f` by at most the integrated
pointwise badness" pattern. Captures `lazy_query_collision_step`,
`lazy_query_RO_size_step` (in `CollisionResistance.lean`) and
`lazy_query_useful_preimage_step` (in `OneWayness.lean`). -/

/-- **Per-query indicator step (generic)**. If on every cache-miss, the new
    fresh sample `y` at input `x` bumps `f` by at most `bad x y σ`, then the
    wp of `lazy_query x` on the state-marginal of `f` is at most
    `f σ + (∑ y, bad x y σ) / |output|`. Cache-hit case is trivial since
    `lazy_query` is `pure y_cache` there (state unchanged). -/
lemma lazy_query_wp_step
    (f : state → ENNReal) (bad : input → output → state → ENNReal)
    (h_bound : ∀ x σ y, random_oracle_state.get σ x = none →
        f (random_oracle_state.set
              (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ)
        ≤ f σ + bad x y σ)
    (x : input) (σ : state) :
    (lazy_query x).wp (fun yσ : output × state => f yσ.2) σ
    ≤ f σ + (∑ y : output, bad x y σ) / Fintype.card output := by
  simp only [lazy_query, wp_bind, wp_get]
  cases h_cache : random_oracle_state.get σ x with
  | some y_cache =>
    simp only [wp_pure]
    exact le_self_add
  | none =>
    simp only [wp_bind, wp_uniform, wp_set, wp_pure]
    set N : ENNReal := (Fintype.card output : ENNReal) with hN_def
    have hN_pos : N ≠ 0 := by rw [hN_def]; exact_mod_cast Fintype.card_pos.ne'
    have hN_top : N ≠ ⊤ := by rw [hN_def]; exact ENNReal.natCast_ne_top _
    calc ∑ y : output, f (random_oracle_state.set
            (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ) / N
        = (∑ y : output, f (random_oracle_state.set
            (fun x' => if x' = x then some y else random_oracle_state.get σ x') σ)) / N := by
          simp_rw [ENNReal.div_eq_inv_mul]
          rw [← Finset.mul_sum]
      _ ≤ (∑ y : output, (f σ + bad x y σ)) / N := by
          gcongr with y _
          exact h_bound x σ y h_cache
      _ = (N * f σ + ∑ y : output, bad x y σ) / N := by
          rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN_def]
      _ = f σ + (∑ y : output, bad x y σ) / N := by
          rw [ENNReal.add_div]
          rw [mul_comm N (f σ), mul_div_assoc, ENNReal.div_self hN_pos hN_top, mul_one]

/-- **Generic oracle-step indicator bump**. One `oracle_step adv` bumps the
    state-indicator `f` by at most `c σ`, given that:
    (1) the adversary preserves `f` (in expectation),
    (2) the adversary preserves `c` (in expectation),
    (3) writes to `oracle_output` leave `f` unchanged,
    (4) one `lazy_query` bumps `f` by at most `c σ`.

    Captures the standard "Layer A + adv-preservation" pattern: a single
    loop body iteration bumps the indicator by the per-query amount,
    because the adversary alone preserves it. Used by both CR and OW for
    multiple indicators (collision, RO_size, useful_preimage). -/
lemma oracle_step_wp_indicator_bump
    {adv : Program state Unit}
    {f : state → ENNReal} (c : state → ENNReal)
    (h_adv_preserves_f : ∀ σ, adv.wp (fun yσ : Unit × state => f yσ.2) σ ≤ f σ)
    (h_adv_preserves_c : ∀ σ, adv.wp (fun yσ : Unit × state => c yσ.2) σ ≤ c σ)
    (h_set_oo : ∀ y σ, f (oracle_output.set y σ) = f σ)
    (h_lazy_query : ∀ x σ,
        (lazy_query x).wp (fun yσ : output × state => f yσ.2) σ ≤ f σ + c σ)
    (σ : state) :
    (oracle_step adv lazy_query).wp (fun yσ : Unit × state => f yσ.2) σ
    ≤ f σ + c σ := by
  show (adv >>= fun _ =>
        Program.get oracle_input >>= fun inp =>
          lazy_query inp >>= fun y =>
            Program.set oracle_output y).wp _ σ ≤ _
  rw [wp_bind]
  have h_inner : ∀ σ_a : state,
      (Program.get oracle_input >>= fun inp =>
        lazy_query inp >>= fun y => Program.set oracle_output y).wp
          (fun yσ : Unit × state => f yσ.2) σ_a
      ≤ f σ_a + c σ_a := by
    intro σ_a
    simp only [wp_bind, wp_get]
    rw [show (fun yσ : output × state =>
              (Program.set oracle_output yσ.1).wp
                (fun yσ' : Unit × state => f yσ'.2) yσ.2)
            = (fun yσ : output × state => f yσ.2) from by
      funext yσ
      rw [wp_set]
      exact h_set_oo yσ.1 yσ.2]
    exact h_lazy_query (oracle_input.get σ_a) σ_a
  calc adv.wp _ σ
      ≤ adv.wp (fun yσ : Unit × state => f yσ.2 + c yσ.2) σ := by
        apply Program.wp_le_wp_of_le; intro yσ; exact h_inner yσ.2
    _ = adv.wp (fun yσ : Unit × state => f yσ.2) σ
        + adv.wp (fun yσ : Unit × state => c yσ.2) σ := by rw [Program.wp_add]
    _ ≤ f σ + c σ := add_le_add (h_adv_preserves_f σ) (h_adv_preserves_c σ)

/-- Constant-`c` specialization of `oracle_step_wp_indicator_bump`. The
    adversary trivially preserves a constant via `Program.wp_const_le`. -/
lemma oracle_step_wp_indicator_bump_const
    {adv : Program state Unit}
    {f : state → ENNReal} (c : ENNReal)
    (h_adv_preserves : ∀ σ, adv.wp (fun yσ : Unit × state => f yσ.2) σ ≤ f σ)
    (h_set_oo : ∀ y σ, f (oracle_output.set y σ) = f σ)
    (h_lazy_query : ∀ x σ,
        (lazy_query x).wp (fun yσ : output × state => f yσ.2) σ ≤ f σ + c)
    (σ : state) :
    (oracle_step adv lazy_query).wp (fun yσ : Unit × state => f yσ.2) σ
    ≤ f σ + c :=
  oracle_step_wp_indicator_bump (fun _ => c) h_adv_preserves
    (fun σ' => Program.wp_const_le adv c σ') h_set_oo h_lazy_query σ
