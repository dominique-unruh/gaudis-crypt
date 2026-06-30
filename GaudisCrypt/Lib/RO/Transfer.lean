import GaudisCrypt.Lib.RO.Basic
import GaudisCrypt.Footprint

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

/-!
# Lazy/eager transfer

This file is the bridge between the lazy and eager random oracles.

* `convert` — the operation that fills in undefined RO entries with a
  fresh uniform function. It's the program-level witness that lazy and
  eager are interchangeable.

* Convert algebra: how `convert` interacts with `wp`, with `set`/`get` on
  disjoint variables, and with `random_oracle_init`. Includes the
  `claim_*` family of foundational lazy/eager equations
  (`lazy_init_convert_eq_random_oracle_init`,
  `lazy_query_convert_eq_convert_random_oracle_query`, etc.).

* `Program.transfer` — the lazy/eager transfer relation, defined as
  `(p >>= λa. convert >>= pure a) = (convert >>= q)`. Closure laws under
  `bind`, `while_loop`, etc. lift it to compound programs.

* `wp`/marginal bridges — `Program.transfer_wp_value`,
  `Program.transfer_value_marginal`, plus the enriched
  RO-invariant variants.
-/

/-! ## Convert -/

/-- Fill in undefined entries of the random oracle with a fresh uniform
    function. The bridge between lazy and eager: applied to a lazy state,
    `convert` produces the same distribution as an eager state. -/
noncomputable def convert : Program state Unit := do
  let h <- Program.get random_oracle_state
  let (y : input -> output) <- Program.uniform
  Program.set random_oracle_state (fun x => some ((h x).getD (y x)))

/-- Lazy init followed by `convert` — used to state the foundational
    `lazy_init_convert_eq_random_oracle_init` equation. -/
noncomputable def lazy_init_convert : Program state Unit := do
  lazy_init
  convert

/-- `lazy_query` followed by `convert`, discarding the query result.
    Used to state `lazy_query_conv_eq_conv_random_oracle`. -/
noncomputable def lazy_query_conv (inp : input) : Program state Unit := do
  let _ <- lazy_query inp
  convert

/-- `convert` followed by `random_oracle_query`, discarding the result. -/
noncomputable def conv_random_oracle (inp : input) : Program state Unit := do
  convert
  let _ <- random_oracle_query inp

/-- `convert` only reads and writes `random_oracle_state` (modulo a uniform sample). -/
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

/-- `convert`'s **probabilistic** footprint lies in `random_oracle_state.footprint` — the prob analogue
    of `convert_inRange_ro`, used to drive the countability-free transfer-reflexivity. -/
theorem convert_inFootprint_ro : convert.inFootprint random_oracle_state.footprint := by
  show ((Program.get random_oracle_state) >>= fun h =>
          (Program.uniform : Program state (input → output)) >>= fun y =>
            Program.set random_oracle_state (fun x => some ((h x).getD (y x)))).inFootprint _
  refine Program.inFootprint_bind (Program.inFootprint_get _) ?_
  intro _
  refine Program.inFootprint_bind ?_ ?_
  · exact Program.inFootprint_mono Program.inFootprint_uniform bot_le
  · intro _
    exact Program.inFootprint_set _ _

/-! ## Convert algebra -/

/-- `convert` is a probability measure: its total mass is 1.
    All pieces (`get`, `uniform`, `set`) preserve mass. -/
lemma convert_mass (σ : state) : convert.wp (fun _ => 1) σ = 1 := by
  simp only [convert, wp_bind, wp_get, wp_uniform, wp_set]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN_pos : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hN_top : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_div_cancel hN_pos hN_top]

/-- Explicit `convert.wp` formula derived from the definition. -/
lemma convert_wp_eq (f : Program.Post state Unit) (s : state) :
    convert.wp f s = ∑ y : input → output,
      f ((), random_oracle_state.set
            (fun x => some ((random_oracle_state.get s x).getD (y x))) s) /
      (Fintype.card (input → output) : ENNReal) := by
  simp [convert, wp_bind, wp_set, wp_get, wp_uniform]

/-- `convert.wp` of any constant function equals that constant (since `convert`
    is a probability measure). Specialization of `Program.wp_const_mul` + `convert_mass`. -/
lemma convert_wp_const (c : ENNReal) (σ : state) :
    convert.wp (fun _ : Unit × state => c) σ = c := by
  have h := Program.wp_const_mul convert c (fun _ : Unit × state => (1 : ENNReal)) σ
  simp only [mul_one] at h
  rw [h, convert_mass, mul_one]

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

/-- `convert` commutes with `Program.set v x` for any `v` disjoint from `random_oracle_state`. -/
theorem convert_commutes_set {α : Type} (v : Variable α) [disjoint v random_oracle_state]
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

/-- `convert` commutes with `Program.get v` for any `v` disjoint from `random_oracle_state`,
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

/-! ## Foundational lazy/eager equations (the `claim_*` family) -/

/-- **`lazy_init` then `convert` = `random_oracle_init`.** The eager
    initialisation is exactly the lazy initialisation followed by a fresh
    uniform sampling that fills the cache. -/
theorem lazy_init_convert_eq_random_oracle_init :
    lazy_init_convert = random_oracle_init := by
  apply Program.ext_of_wp
  intro f
  simp [lazy_init_convert, lazy_init, convert, random_oracle_init,
        wp_bind, wp_set, wp_get, wp_uniform,
        random_oracle_state.set_get, random_oracle_state.set_set,
        Option.getD_none]

/-- **Sum-over-`Function.update` reorganization** (would-be-generic). Used by
    `lazy_query_convert_eq_convert_random_oracle_query`. Cannot be moved out
    of this file as-is because the local `sorry`'d `Fintype (a → b)`
    instance in `Basic.lean` shadows Mathlib's `Pi.instFintype`, causing
    type-class instance mismatches at the call site if the lemma is
    elaborated in a module that doesn't see the local instance. Move once
    the duplicate Fintype instance is removed. -/
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

/-- **Value-passing lazy/eager bridge for `lazy_query`**: `lazy_query` followed
    by `convert` (passing the value through) equals `convert` followed by
    `random_oracle_query`. This is the workhorse equation; the Unit-form
    `lazy_query_conv_eq_conv_random_oracle` and the continuation form
    `lazy_query_convert_cont_eq_convert_random_oracle_query` are corollaries. -/
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

/-- Continuation-passing variant of `lazy_query_convert_eq_convert_random_oracle_query`. -/
theorem lazy_query_convert_cont_eq_convert_random_oracle_query
    {β : Type} (inp : input) (k : output → Program state β) :
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
    Derived from the value-tracking variant by specializing `k := pure ()`. -/
theorem lazy_query_conv_eq_conv_random_oracle (inp : input) :
    lazy_query_conv inp = conv_random_oracle inp := by
  change (lazy_query inp >>= fun _ => convert)
       = (convert >>= fun _ => random_oracle_query inp >>= fun _ => pure ())
  rw [show (lazy_query inp >>= fun _ : output => (convert : Program state Unit))
        = (lazy_query inp >>= fun _ : output =>
            convert >>= fun _ : Unit => (pure () : Program state Unit))
        from by congr 1; funext _; exact (Program.bind_pure convert).symm]
  exact lazy_query_convert_cont_eq_convert_random_oracle_query inp (fun _ => pure ())

/-- Factor `convert` out of an `if`: if the then-branch starts with `convert`
    and the else-branch IS `convert`, we can move `convert` outside. -/
lemma if_factor_convert (b : Bool) (X : Program state Unit) :
    (if b = true then convert >>= fun _ => X else convert)
  = convert >>= fun _ => (if b = true then X else pure ()) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact (Program.bind_pure convert).symm
  · rfl

/-- `convert` is absorbed by `random_oracle_init`: a fresh uniform sample
    overwrites any prior RO content. -/
lemma convert_random_oracle_init :
    (convert >>= fun _ => random_oracle_init) = random_oracle_init := by
  apply Program.ext_of_wp
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
    cases `lazy_init ↦ random_oracle_init` (lazy_init_convert_eq_random_oracle_init) and
    `lazy_query x ↦ random_oracle_query x` (lazy_query_convert_eq_convert_random_oracle_query), this lets us
    transfer any program built from these primitives. -/
def Program.transfer {α : Type} (p q : Program state α) : Prop :=
  (p >>= fun a => convert >>= fun _ => pure a) = (convert >>= fun _ => q)

/-- **Reflexivity on RO-disjoint programs — countability-free** (subtask 4). The `Footprint`
    analogue of `transfer_refl_of_inRange_compl`: a program whose probabilistic footprint avoids the
    RO table commutes with `convert` (via `commute_of_disjoint_footprint`, no `[Countable]`), so transfers
    to itself.  The `ᶜ`-form makes the disjointness `le_refl`. -/
lemma Program.transfer_refl_of_inFootprint_compl
    {α : Type} {p : Program state α}
    (hp : p.inFootprint (random_oracle_state.footprint)ᶜ) :
    Program.transfer p p := by
  show (p >>= fun a => convert >>= fun _ => pure a) = (convert >>= fun _ => p)
  have h_commute : (p >>= fun a => convert >>= fun b => pure (a, b))
                 = (convert >>= fun b => p >>= fun a => pure (a, b)) :=
    Program.commute_of_disjoint_footprint hp convert_inFootprint_ro (le_refl _)
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

/-- Any program in `v.footprint`, for a `v` disjoint from `random_oracle_state`, transfers to itself
    — the countability-free `Footprint` analogue of `transfer_of_inRange_disjoint`. -/
lemma Program.transfer_of_inFootprint_disjoint {α : Type}
    (p : Program state α) {β : Type} (v : Lens β state)
    [disjoint v random_oracle_state]
    (hp : p.inFootprint v.footprint) :
    Program.transfer p p :=
  Program.transfer_refl_of_inFootprint_compl
    (Program.inFootprint_mono hp
      (Lens.footprint_le_compl_of_disjoint v random_oracle_state))

/-- `Program.set v x` transfers to itself when `v` is disjoint from `random_oracle_state`.
    Countability-free (subtask 4): via the `Footprint` transfer-reflexivity. -/
lemma Program.transfer_set_of_disjoint_ro {α : Type}
    (v : Lens α state) [disjoint v random_oracle_state] (x : α) :
    Program.transfer (Program.set v x) (Program.set v x) :=
  Program.transfer_of_inFootprint_disjoint _ v (Program.inFootprint_set v x)

/-- `Program.get v` transfers to itself when `v` is disjoint from `random_oracle_state`.
    Countability-free (subtask 4). -/
lemma Program.transfer_get_of_disjoint_ro {α : Type}
    (v : Lens α state) [disjoint v random_oracle_state] :
    Program.transfer (Program.get v) (Program.get v) :=
  Program.transfer_of_inFootprint_disjoint _ v (Program.inFootprint_get v)

/-- `Program.uniform` transfers to itself (it doesn't touch state at all).
    Countability-free (subtask 4). -/
lemma Program.transfer_uniform {α : Type} [Fintype α] [Nonempty α] :
    Program.transfer (Program.uniform : Program state α) Program.uniform :=
  Program.transfer_refl_of_inFootprint_compl
    (Program.inFootprint_mono Program.inFootprint_uniform bot_le)

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
  rw [lazy_init_convert_eq_random_oracle_init]
  exact convert_random_oracle_init.symm

/-- `lazy_query x` transfers to `random_oracle_query x`. This is `lazy_query_convert_eq_convert_random_oracle_query`
    restated in the transfer language. -/
lemma Program.transfer_lazy_query (x : input) :
    Program.transfer (lazy_query x) (random_oracle_query x) :=
  lazy_query_convert_eq_convert_random_oracle_query x

/-! ### Closure under `while_loop`

The transfer relation is preserved by `while_loop`: if the body transfers
and the condition is RO-disjoint, then the loops transfer. The proof is
Kleene-style — couple every finite iterate of the lazy and eager loops
via an intermediate `Ψ_iter` whose else-branch is `convert`, then take
the ωSup. Internalises what was previously the wrapper-layer
`loop_kleene_lazy`/`loop_kleene_eager`/`loop_coupling` argument.
-/

/-- The intermediate iteration: same shape as `while_iteration` for the lazy
    body, but with `convert` in the else branch (representing
    "loop terminates, then convert"). -/
private noncomputable def transfer_while_Ψ_iter
    (cond : Program state Bool) (body_lazy : Program state Unit) :
    (Unit → Program state Unit) →𝒄 (Unit → Program state Unit) :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Unit → Program state Unit) => fun () =>
    do if ← cond then body_lazy; fp ()
       else convert

/-- Kleene induction on the lazy side: at every finite iterate, the lazy
    iterate composed with `convert` equals the same iterate of `Ψ_iter`. -/
private lemma transfer_while_kleene_lazy
    (cond : Program state Bool) (body_lazy : Program state Unit) :
    ∀ n : ℕ,
    (((while_iteration cond body_lazy)^[n]
      (⊥ : Unit → Program state Unit)) () >>= (fun _ => convert))
    = ((transfer_while_Ψ_iter cond body_lazy)^[n]
        (⊥ : Unit → Program state Unit)) () := by
  intro n
  induction n with
  | zero =>
    change ((⊥ : Unit → Program state Unit) () >>= fun _ => convert)
         = (⊥ : Unit → Program state Unit) ()
    change ((⊥ : Program state Unit) >>= fun _ => convert) = (⊥ : Program state Unit)
    exact Program.bot_bind _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (((cond) >>= fun b =>
              if b = true then
                body_lazy >>= fun _ =>
                  ((while_iteration cond body_lazy)^[n] ⊥) ()
              else (pure () : Program state Unit)) >>= fun _ => convert)
        = (cond) >>= fun b =>
              if b = true then
                body_lazy >>= fun _ =>
                  ((transfer_while_Ψ_iter cond body_lazy)^[n] ⊥) ()
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

/-- Kleene induction on the eager side: `convert` prepended to each eager
    iterate equals the same iterate of `Ψ_iter`. -/
private lemma transfer_while_kleene_eager
    {cond : Program state Bool}
    (h_cond : cond.inRange random_oracle_state.compl.range)
    {body_lazy body_eager : Program state Unit}
    (h_body : (body_lazy >>= fun _ : Unit => convert)
            = (convert >>= fun _ : Unit => body_eager)) :
    ∀ n : ℕ,
    convert >>= (fun _ => ((while_iteration cond body_eager)^[n]
      (⊥ : Unit → Program state Unit)) ())
    = ((transfer_while_Ψ_iter cond body_lazy)^[n]
        (⊥ : Unit → Program state Unit)) () := by
  -- Helper: `cond` (RO-disjoint) commutes with `convert` in continuation form.
  have h_cond_commutes : ∀ {β : Type} (k : Bool → Program state β),
      (cond >>= fun b => convert >>= fun _ => k b)
      = (convert >>= fun _ => cond >>= k) := by
    intro β k
    have h_disj : random_oracle_state.compl.range ≤ (random_oracle_state.range)ᶜ :=
      le_of_eq (DetermFootprint.complement_range _)
    have h_pair : (cond >>= fun b => convert >>= fun u => pure (b, u))
                = (convert >>= fun u => cond >>= fun b => pure (b, u)) :=
      Program.commute_of_disjoint_lens h_cond convert_inRange_ro h_disj
    -- Translate the pair-output commutation into the continuation form.
    have hL : (cond >>= fun b => convert >>= fun _ => k b)
            = (cond >>= fun b => convert >>= fun u => pure (b, u))
                >>= fun bu : Bool × Unit => k bu.1 := by
      simp_rw [Program.bind_assoc]
      congr 1; funext b; congr 1; funext u
      rw [Program.pure_bind]
    have hR : (convert >>= fun _ => cond >>= k)
            = (convert >>= fun u => cond >>= fun b => pure (b, u))
                >>= fun bu : Bool × Unit => k bu.1 := by
      simp_rw [Program.bind_assoc]
      congr 1; funext u; congr 1; funext b
      rw [Program.pure_bind]
    rw [hL, hR, h_pair]
  intro n
  induction n with
  | zero =>
    change (convert >>= fun _ => (⊥ : Unit → Program state Unit) ())
         = (⊥ : Unit → Program state Unit) ()
    change (convert >>= fun _ => (⊥ : Program state Unit)) = (⊥ : Program state Unit)
    exact Program.bind_bot _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (convert >>= fun _ => (cond) >>= fun b =>
              if b = true then
                body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) ()
              else (pure () : Program state Unit))
        = (cond) >>= fun b =>
              if b = true then
                body_lazy >>= fun _ =>
                  ((transfer_while_Ψ_iter cond body_lazy)^[n] ⊥) ()
              else convert
    -- Push `convert` past `cond` using the commutation lemma.
    rw [show (convert >>= fun _ => (cond) >>=
              fun b => if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) ()
                else (pure () : Program state Unit))
            = ((cond) >>= fun b => convert >>= fun _ =>
                if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) ()
                else (pure () : Program state Unit)) from
        (h_cond_commutes _).symm]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      -- LHS: convert >>= body_eager >>= F_eager^[n] ⊥ ()
      -- Use h_body to swap convert and body.
      rw [← Program.bind_assoc]
      rw [show (convert >>= fun _ : Unit => body_eager)
              = (body_lazy >>= fun _ : Unit => convert) from h_body.symm]
      rw [Program.bind_assoc]
      congr 1; funext _
      exact ih
    · simp only [h, if_false]
      exact Program.bind_pure _

/-- **Transfer is preserved by `while_loop`.** If the body transfers (lazy
    to eager) and the condition is RO-disjoint, then the lazy and eager
    while-loops transfer.

    Internalises the Kleene argument that was previously specific to
    `oracle_loop` in `Wrapper.lean`. Any RO-based while-loop construction
    inherits the lazy = eager equivalence by this closure law plus the
    base-case body transfer. -/
theorem Program.transfer_while_loop
    {cond : Program state Bool}
    (h_cond : cond.inRange random_oracle_state.compl.range)
    {body_lazy body_eager : Program state Unit}
    (h_body : Program.transfer body_lazy body_eager) :
    Program.transfer (while_loop cond body_lazy) (while_loop cond body_eager) := by
  -- Convert the transfer hypothesis on body to the bind form:
  --   body_lazy >>= convert = convert >>= body_eager.
  have h_body_bind : (body_lazy >>= fun _ : Unit => convert)
                  = (convert >>= fun _ : Unit => body_eager) := by
    have h := h_body
    show (body_lazy >>= fun _ : Unit => convert) = (convert >>= fun _ : Unit => body_eager)
    calc (body_lazy >>= fun _ : Unit => convert)
        = (body_lazy >>= fun u : Unit =>
              convert >>= fun _ : Unit => (Pure.pure u : Program state Unit)) := by
          congr 1; funext u
          show convert = convert >>= fun _ : Unit => Pure.pure u
          rw [show (Pure.pure u : Program state Unit) = (Pure.pure () : Program state Unit) from rfl]
          exact (Program.bind_pure _).symm
      _ = (convert >>= fun _ : Unit => body_eager) := h
  -- Goal: Program.transfer (while_loop cond body_lazy) (while_loop cond body_eager).
  -- Unfold to: (while_loop cond body_lazy >>= λu. convert >>= pure u)
  --          = (convert >>= while_loop cond body_eager).
  show (while_loop cond body_lazy >>= fun u : Unit =>
          convert >>= fun _ : Unit => (Pure.pure u : Program state Unit))
      = (convert >>= fun _ : Unit => while_loop cond body_eager)
  -- For Unit-valued LHS, simplify (λu. convert >>= pure u) = convert.
  rw [show (fun u : Unit => convert >>= fun _ : Unit => (Pure.pure u : Program state Unit))
          = (fun _ : Unit => convert) from by
        funext u
        rw [show (Pure.pure u : Program state Unit) = (Pure.pure () : Program state Unit) from rfl]
        exact Program.bind_pure _]
  -- Goal reduces to:
  --   (while_loop cond body_lazy >>= λ_. convert) = (convert >>= while_loop cond body_eager).
  -- This is the abstract loop_coupling. Proof by Kleene ωSup.
  let F_lazy := while_iteration cond body_lazy
  let F_eager := while_iteration cond body_eager
  have hL_chain : ∀ n, ((F_lazy^[n] ⊥ : Unit → Program state Unit) () >>= (fun _ => convert))
                     = ((transfer_while_Ψ_iter cond body_lazy)^[n] ⊥
                         : Unit → Program state Unit) () :=
    transfer_while_kleene_lazy cond body_lazy
  have hE_chain : ∀ n, convert >>= (fun _ => (F_eager^[n] ⊥ : Unit → Program state Unit) ())
                     = ((transfer_while_Ψ_iter cond body_lazy)^[n] ⊥
                         : Unit → Program state Unit) () :=
    transfer_while_kleene_eager h_cond h_body_bind
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

/-! ## Enriched transfer: RO-invariant projections of state

The basic `transfer_wp_value` only delivers wp-equality for posts that
ignore the state. But `convert` only writes `random_oracle_state` — so
*any* projection of state that is invariant under `random_oracle_state.set`
is automatically preserved by `convert`. This means we can transfer
postconditions that depend on (value, RO-invariant state projection).

These enriched lemmas recover the full strength of the wrapper-style
`oracle_loop_wp_lazy_eq_random_oracle` and its marginal/compl/glob
companions, without rebuilding the Kleene argument.
-/

/-- `convert` preserves any state projection `G : state → ENNReal` that is
    invariant under writes to `random_oracle_state`. Because `convert` only
    samples a fresh RO function and writes it, an RO-invariant `G` is constant
    along the convert trajectory, and `convert`'s total mass is 1. -/
lemma convert_wp_state_const_of_ro_invariant
    (G : state → ENNReal)
    (hG_inv : ∀ σ x, G (random_oracle_state.set x σ) = G σ)
    (σ : state) :
    convert.wp (fun aσ : Unit × state => G aσ.2) σ = G σ := by
  rw [convert_wp_eq]
  simp_rw [hG_inv]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN_pos : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hN_top : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_div_cancel hN_pos hN_top]

/-- Same as `convert_wp_state_const_of_ro_invariant`, parameterised over the
    value coordinate. Used in `transfer_wp_ro_invariant` below to absorb the
    `convert` step in the LHS of the transfer relation. -/
lemma convert_wp_value_state_of_ro_invariant {α : Type}
    (F : α × state → ENNReal)
    (hF_inv : ∀ a σ x, F (a, random_oracle_state.set x σ) = F (a, σ))
    (a : α) (σ : state) :
    convert.wp (fun aσ_c : Unit × state => F (a, aσ_c.2)) σ = F (a, σ) :=
  convert_wp_state_const_of_ro_invariant (fun σ' => F (a, σ')) (hF_inv a) σ

/-- **Transfer at the wp level for RO-invariant postconditions**.
    Strict strengthening of `transfer_wp_value`: instead of requiring the
    post to ignore state entirely, only requires it to be invariant under
    writes to `random_oracle_state`.

    Captures the wrapper-style `oracle_loop_wp_lazy_eq_random_oracle`. -/
theorem Program.transfer_wp_ro_invariant {α : Type}
    {p q : Program state α}
    (h_transfer : Program.transfer p q)
    (h_absorb : (convert >>= fun _ => q) = q)
    (F : α × state → ENNReal)
    (hF_inv : ∀ a σ x, F (a, random_oracle_state.set x σ) = F (a, σ))
    (σ₀ : state) :
    p.wp F σ₀ = q.wp F σ₀ := by
  -- Master equation from transfer + absorb.
  have h_eq : (p >>= fun a => convert >>= fun _ => (Pure.pure a : Program state α)) = q := by
    rw [h_transfer, h_absorb]
  have h_wp := congrArg (fun (r : Program state α) => r.wp F σ₀) h_eq
  rw [← h_wp]
  -- Goal: p.wp F σ₀ = (p >>= a => convert >>= pure a).wp F σ₀.
  rw [wp_bind]
  congr 1
  funext aσ_p
  obtain ⟨a, σ_p⟩ := aσ_p
  show F (a, σ_p)
      = (convert >>= fun _ => (Pure.pure a : Program state α)).wp F σ_p
  rw [wp_bind, wp_pure]
  -- Goal: F (a, σ_p) = convert.wp (fun aσ_c : Unit × state => F (a, aσ_c.2)) σ_p.
  exact (convert_wp_value_state_of_ro_invariant F hF_inv a σ_p).symm

/-- **Marginal at the (value × RO-invariant projection) level**.

    Strict strengthening of `transfer_value_marginal`: instead of projecting
    to just the value, we additionally include any RO-invariant projection
    `h : state → β`. Captures the wrapper-style
    `oracle_loop_marginal_lazy_eq_random_oracle` family. -/
theorem Program.transfer_marginal_ro_invariant {α β : Type}
    {p q : Program state α}
    (h_transfer : Program.transfer p q)
    (h_absorb : (convert >>= fun _ => q) = q)
    (h : state → β)
    (h_inv : ∀ σ x, h (random_oracle_state.set x σ) = h σ)
    (σ₀ : state) :
    (p σ₀ >>= fun aσ : α × state => (Pure.pure (aσ.1, h aσ.2) : SubProbability (α × β)))
  = (q σ₀ >>= fun aσ : α × state => (Pure.pure (aσ.1, h aσ.2) : SubProbability (α × β))) := by
  apply Subtype.ext
  letI : MeasurableSpace (α × β) := ⊤
  letI : MeasurableSpace (α × state) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  show MeasureTheory.Measure.bind (p σ₀).1 (fun aσ : α × state =>
          (@MeasureTheory.Measure.dirac (α × β) ⊤ (aσ.1, h aσ.2))) A
     = MeasureTheory.Measure.bind (q σ₀).1 (fun aσ : α × state =>
          (@MeasureTheory.Measure.dirac (α × β) ⊤ (aσ.1, h aσ.2))) A
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
      MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  -- Apply transfer_wp_ro_invariant with F = (fun aσ => dirac (aσ.1, h aσ.2) A).
  exact Program.transfer_wp_ro_invariant h_transfer h_absorb
    (fun aσ : α × state =>
      (@MeasureTheory.Measure.dirac (α × β) ⊤ (aσ.1, h aσ.2)) A)
    (by intro a σ x; simp only; rw [h_inv]) σ₀
