import PlonkLean.RO.Basic

/-! ## Phase 6 — General lazy/eager transfer relation

The existing `oracle_loop_wp_lazy_eq_random_oracle` is for `oracle_loop` specifically. Below we abstract the
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
  rw [lazy_init_convert_eq_random_oracle_init]
  exact convert_random_oracle_init.symm

/-- `lazy_query x` transfers to `random_oracle_query x`. This is `lazy_query_convert_eq_convert_random_oracle_query`
    restated in the transfer language. -/
lemma Program.transfer_lazy_query (x : input) :
    Program.transfer (lazy_query x) (random_oracle_query x) :=
  lazy_query_convert_eq_convert_random_oracle_query x

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

