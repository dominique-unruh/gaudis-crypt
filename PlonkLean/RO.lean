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


private lemma sum_update_eq_card_mul_sum {α β : Type*}
    [DecidableEq α] [Fintype α] [Fintype β]
    (i : α) (G : (α → β) → ENNReal) :
    ∑ v : β, ∑ y : α → β, G (Function.update y i v) =
    (Fintype.card β : ENNReal) * ∑ z : α → β, G z := by
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

/- Disjointness assumptions: `adv` does not read or write `random_oracle_state`,
   and is independent of the uniform sampling inside `convert`. -/
axiom adv_commutes_get_ro {a : Type} (k : (input → Option output) → Program state a) :
    (adv >>= fun _ => Program.get random_oracle_state >>= k)
  = (Program.get random_oracle_state >>= fun h => adv >>= fun _ => k h)

axiom adv_commutes_set_ro (x : input → Option output) :
    (adv >>= fun _ => Program.set random_oracle_state x)
  = (Program.set random_oracle_state x >>= fun _ => adv)

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
  simp only [convert]
  rw [adv_commutes_get_ro]
  simp_rw [adv_commutes_uniform]
  simp_rw [adv_commutes_set_ro]
  simp_rw [Program_bind_assoc]
