import GaudisCrypt.Lib.RO.Basic
import GaudisCrypt.Lib.RO.Transfer

/-!
# Oracle loops

Scratch state and loop primitives for adversary-driven oracle protocols.

* Scratch state: `want_more`, `oracle_input`, `oracle_output`,
  `adversary_result` — the per-step variables shared between the
  adversary and the loop infrastructure. All disjoint from
  `random_oracle_state`.

* The three oracle-loop variants, sharing the same body shape:
  - `oracle_step` — one iteration.
  - `oracle_loop_n` — `q` iterations (static query budget).
  - `oracle_loop` — unbounded iteration via `while_loop` and `want_more`.

* Their transfer / `inRange` / linear-bound / indicator-step lemmas.

* Key-level RO reasoning for `lazy_query inp >>= set oracle_output`
  (the "deferred sampling" combinator).
-/

/-! ## Scratch state -/

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

/-! ## `lazy_query + set oracle_output` — the "deferred sampling" combinator

The combined step "query the oracle on `inp`, store the result in
`oracle_output`" is the unit of work performed in every oracle-loop
body. We collect its key-level properties here. -/

/-- Pushing `convert` past the `let inp ← get oracle_input; let v ← lazy_query inp;
    set oracle_output v` piece. -/
theorem query_set_convert_eq :
    ((Program.get oracle_input >>= fun inp =>
      lazy_query inp >>= fun v =>
      Program.set oracle_output v) >>= fun _ => convert)
  = (convert >>= fun _ =>
      Program.get oracle_input >>= fun inp =>
      random_oracle_query inp >>= fun v =>
      Program.set oracle_output v) := by
  simp_rw [Program.bind_assoc, convert_commutes_set,
           lazy_query_convert_cont_eq_convert_random_oracle_query]
  exact convert_commutes_get oracle_input _

/-- `(lazy_query inp >>= set oracle_output)` is in `L.compl.range` for any
    lens `L` disjoint from both `random_oracle_state` and `oracle_output`.
    Useful for `wp_strengthen_lens_preserved` arguments downstream. -/
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

/-! ### Unbounded `oracle_loop`

The `while_loop` variant: the adversary may continue indefinitely,
terminating by clearing `want_more`. Strictly more general than
`oracle_loop_n` (which fixes the query budget upfront). The lazy = eager
equivalence is proved in `PlonkLean.RO.ROEquiv` via the transfer
framework's `while_loop` closure law. -/

/-- Unbounded "adversary + oracle call" loop. The adversary decides via
    the `want_more` flag whether to continue or stop. Returns the value
    of `adversary_result`. -/
noncomputable def oracle_loop (adv : Program state Unit)
    (init : Program state Unit)
    (oracle : input → Program state output) : Program state Bool := do
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

/-- The lazy form of `oracle_loop`'s while-loop body. -/
noncomputable def loop_body_lazy (adv : Program state Unit) : Program state Unit := do
  adv
  if ← Program.get want_more then
    Program.set oracle_output (← lazy_query (← Program.get oracle_input))
  else
    skip

/-- The eager form of `oracle_loop`'s while-loop body. -/
noncomputable def loop_body_eager (adv : Program state Unit) : Program state Unit := do
  adv
  if ← Program.get want_more then
    Program.set oracle_output (← random_oracle_query (← Program.get oracle_input))
  else
    skip

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

/-- The static-budget oracle loop is the bounded loop combinator applied to a
    single oracle step. Lets generic `loop_n` lemmas apply to `oracle_loop_n`. -/
lemma oracle_loop_n_eq_loop_n
    (adv : Program state Unit) (oracle : input → Program state output) (q : ℕ) :
    oracle_loop_n adv q oracle = loop_n q (oracle_step adv oracle) := by
  induction q with
  | zero => rfl
  | succ n ih =>
    show oracle_step adv oracle >>= (fun _ => oracle_loop_n adv n oracle)
       = oracle_step adv oracle >>= fun _ => loop_n n (oracle_step adv oracle)
    rw [ih]
