import PlonkLean.RO

/-!
# One-wayness of the random oracle

A 101-crypto example mirroring `CollisionResistance.lean`. The OW game:

1. Sample challenge input `x ← uniform`.
2. Compute `y := oracle(x)` and publish `y` via `ow_challenge_y`.
3. Run the adversary `ow_adv` for `q` rounds with oracle access; the adversary
   writes its candidate preimage to `ow_response`.
4. Check whether `oracle(ow_response) = y`.

The high-level claims:

* `ow_transfer` — the win-bit distribution is identical under lazy and eager RO.
* `ow_lazy_bound` — the lazy win probability is at most `(q + 2) / |output|`
  (the `+2` accounts for the initial challenge query and the final verification
  query, on top of the `q` adversary rounds).
* `ow_eager_bound` — the same bound, via `ow_transfer`.

The bound is **linear** in `q` (not quadratic like CR's birthday bound), because
each `lazy_query` has at most `1 / |output|` chance of producing the fixed
challenge value `y`.
-/

/-- The challenge value `y` published to the adversary (= `oracle(x)` for a
    random `x`). -/
axiom ow_challenge_y : Variable output

/-- The original challenge input `x` (kept in state for the bound analysis). -/
axiom ow_challenge_x : Variable input

/-- The adversary's response: its candidate preimage of the challenge. -/
axiom ow_response : Variable input

/-- Disjointness: game-specific variables don't alias the random oracle. -/
axiom disjoint_ow_challenge_y_ro : disjoint ow_challenge_y random_oracle_state
axiom disjoint_ow_challenge_x_ro : disjoint ow_challenge_x random_oracle_state
axiom disjoint_ow_response_ro : disjoint ow_response random_oracle_state

/-- Game-specific variables are disjoint from the loop's scratch variables.
    Needed so that `ow_loop_body`'s `Program.get oracle_input` /
    `Program.set oracle_output` / `random_oracle_state` operations preserve
    `ow_challenge_y` (and similarly for `ow_response`). -/
axiom disjoint_oracle_input_ow_challenge_y : disjoint oracle_input ow_challenge_y
axiom disjoint_oracle_output_ow_challenge_y : disjoint oracle_output ow_challenge_y
axiom disjoint_ro_ow_challenge_y : disjoint random_oracle_state ow_challenge_y
axiom disjoint_oracle_input_ow_response : disjoint oracle_input ow_response
axiom disjoint_oracle_output_ow_response : disjoint oracle_output ow_response
axiom disjoint_ro_ow_response : disjoint random_oracle_state ow_response

attribute [instance] disjoint_ow_challenge_y_ro disjoint_ow_challenge_x_ro
                     disjoint_ow_response_ro
                     disjoint_oracle_input_ow_challenge_y
                     disjoint_oracle_output_ow_challenge_y
                     disjoint_ro_ow_challenge_y
                     disjoint_oracle_input_ow_response
                     disjoint_oracle_output_ow_response
                     disjoint_ro_ow_response

/-- DecidableEq on `output` (needed for the win-bit). Same trick as CR. -/
noncomputable instance : DecidableEq output := Classical.decEq output

/-! ## Game definition (parameterized over the adversary) -/

section OWParam

variable (ow_adv : Program state Unit)

/-- One round of the OW loop body: the adversary computes (and writes
    `oracle_input`), then we run one oracle query. Same shape as
    `cr_loop_body`. -/
noncomputable def ow_loop_body (oracle : input → Program state output) :
    Program state Unit := do
  ow_adv
  Program.set oracle_output (← oracle (← Program.get oracle_input))

/-- Run the adversary-and-query loop for `q` rounds. -/
noncomputable def ow_loop : ℕ → (input → Program state output) → Program state Unit
  | 0,     _      => pure ()
  | n + 1, oracle => do
      ow_loop_body ow_adv oracle
      ow_loop n oracle

/-- **The OW experiment** parameterised by query budget `q`, init, and oracle.

    Sample `x`, set `y := oracle(x)`, publish `y`, run adversary for `q` rounds,
    read the adversary's response, and check whether `oracle(response) = y`. -/
noncomputable def ow_experiment (q : ℕ)
    (init : Program state Unit)
    (oracle : input → Program state output) : Program state Bool := do
  init
  let x ← Program.uniform
  Program.set ow_challenge_x x
  let y ← oracle x
  Program.set ow_challenge_y y
  ow_loop ow_adv q oracle
  let resp ← Program.get ow_response
  let y_check ← oracle resp
  pure (decide (y_check = y))

/-! ## Phase 2 — Transfer (lazy = eager)

Mirrors `cr_transfer` from `CollisionResistance.lean`. -/

variable (h_ow_adv : ow_adv.inRange random_oracle_state.compl.range)
variable (h_ow_adv_chal_y : ow_adv.inRange ow_challenge_y.compl.range)

include h_ow_adv in
/-- `ow_adv` transfers to itself: it doesn't touch RO. -/
private lemma transfer_ow_adv : Program.transfer ow_adv ow_adv :=
  Program.transfer_refl_of_inRange_compl h_ow_adv

include h_ow_adv in
/-- One iteration of `ow_loop_body` transfers from lazy to eager. -/
private lemma transfer_ow_loop_body :
    Program.transfer (ow_loop_body ow_adv lazy_query)
                     (ow_loop_body ow_adv random_oracle_query) := by
  show Program.transfer
    (ow_adv >>= fun _ => Program.get oracle_input >>= fun inp =>
      lazy_query inp >>= fun y => Program.set oracle_output y)
    (ow_adv >>= fun _ => Program.get oracle_input >>= fun inp =>
      random_oracle_query inp >>= fun y => Program.set oracle_output y)
  apply Program.transfer_bind (transfer_ow_adv ow_adv h_ow_adv)
  intro _
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ oracle_input (Program.inRange_get _))
  intro inp
  apply Program.transfer_bind (Program.transfer_lazy_query inp)
  intro y
  exact Program.transfer_of_inRange_disjoint _ oracle_output (Program.inRange_set _ _)

include h_ow_adv in
/-- `ow_loop q` transfers from lazy to eager, by induction on `q`. -/
private lemma transfer_ow_loop (q : ℕ) :
    Program.transfer (ow_loop ow_adv q lazy_query) (ow_loop ow_adv q random_oracle_query) := by
  induction q with
  | zero => exact Program.transfer_pure ()
  | succ n ih =>
    show Program.transfer
      (ow_loop_body ow_adv lazy_query >>= fun _ => ow_loop ow_adv n lazy_query)
      (ow_loop_body ow_adv random_oracle_query >>=
        fun _ => ow_loop ow_adv n random_oracle_query)
    exact Program.transfer_bind (transfer_ow_loop_body ow_adv h_ow_adv) (fun _ => ih)

include h_ow_adv in
/-- The full `ow_experiment q` transfers from lazy to eager. -/
private lemma transfer_ow_experiment (q : ℕ) :
    Program.transfer
      (ow_experiment ow_adv q lazy_init lazy_query)
      (ow_experiment ow_adv q random_oracle_init random_oracle_query) := by
  show Program.transfer
    (lazy_init >>= fun _ =>
      Program.uniform >>= fun x =>
        Program.set ow_challenge_x x >>= fun _ =>
          lazy_query x >>= fun y =>
            Program.set ow_challenge_y y >>= fun _ =>
              ow_loop ow_adv q lazy_query >>= fun _ =>
                Program.get ow_response >>= fun resp =>
                  lazy_query resp >>= fun y_check =>
                    (pure (decide (y_check = y)) : Program state Bool))
    (random_oracle_init >>= fun _ =>
      Program.uniform >>= fun x =>
        Program.set ow_challenge_x x >>= fun _ =>
          random_oracle_query x >>= fun y =>
            Program.set ow_challenge_y y >>= fun _ =>
              ow_loop ow_adv q random_oracle_query >>= fun _ =>
                Program.get ow_response >>= fun resp =>
                  random_oracle_query resp >>= fun y_check =>
                    (pure (decide (y_check = y)) : Program state Bool))
  apply Program.transfer_bind Program.transfer_lazy_init
  intro _
  apply Program.transfer_bind
    (Program.transfer_refl_of_inRange_compl
      (Program.inRange_mono Program.inRange_uniform bot_le))
  intro x
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ ow_challenge_x (Program.inRange_set _ _))
  intro _
  apply Program.transfer_bind (Program.transfer_lazy_query x)
  intro y
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ ow_challenge_y (Program.inRange_set _ _))
  intro _
  apply Program.transfer_bind (transfer_ow_loop ow_adv h_ow_adv q)
  intro _
  apply Program.transfer_bind
    (Program.transfer_of_inRange_disjoint _ ow_response (Program.inRange_get _))
  intro resp
  apply Program.transfer_bind (Program.transfer_lazy_query resp)
  intro y_check
  exact Program.transfer_pure _

/-- `convert` is absorbed by the eager `ow_experiment` (it starts with
    `random_oracle_init`). -/
private lemma convert_ow_experiment_eager (q : ℕ) :
    (convert >>= fun _ =>
      ow_experiment ow_adv q random_oracle_init random_oracle_query)
    = ow_experiment ow_adv q random_oracle_init random_oracle_query := by
  set rest : Program state Bool :=
    Program.uniform >>= fun x =>
      Program.set ow_challenge_x x >>= fun _ =>
        random_oracle_query x >>= fun y =>
          Program.set ow_challenge_y y >>= fun _ =>
            ow_loop ow_adv q random_oracle_query >>= fun _ =>
              Program.get ow_response >>= fun resp =>
                random_oracle_query resp >>= fun y_check =>
                  (pure (decide (y_check = y)) : Program state Bool) with hrest
  show (convert >>= fun _ => random_oracle_init >>= fun _ => rest)
      = (random_oracle_init >>= fun _ => rest)
  rw [← Program.bind_assoc, convert_random_oracle_init]

include h_ow_adv in
/-- **Transfer theorem**: the marginal distribution of the win-bit is identical
    under lazy and eager random oracle. -/
theorem ow_transfer (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool))
    =
    (ow_experiment ow_adv q random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state => (pure bσ.1 : SubProbability Bool)) :=
  Program.transfer_value_marginal (transfer_ow_experiment ow_adv h_ow_adv q)
    (convert_ow_experiment_eager ow_adv q) σ₀

/-! ## Phase 3 — Bookkeeping: win implies preimage in RO

State predicate: at the end of the experiment, if `result = true`, then
`RO[ow_response] = some ow_challenge_y`. This is the OW analog of
`cr_true_implies_collision_wp`. -/

/-- The "is a preimage" state predicate: `RO σ (ow_response σ) = some (ow_challenge_y σ)`. -/
def is_preimage (σ : state) : Prop :=
  random_oracle_state.get σ (ow_response.get σ) = some (ow_challenge_y.get σ)

noncomputable instance : DecidablePred is_preimage :=
  fun _ => Classical.propDecidable _

/-- 0/1-valued indicator that `ow_response` is a preimage of `ow_challenge_y`
    in the random oracle. -/
noncomputable def preimage_indicator (σ : state) : ENNReal :=
  if is_preimage σ then 1 else 0

include h_ow_adv_chal_y in
/-- `ow_loop_body` preserves `ow_challenge_y`. -/
private lemma ow_loop_body_inRange_chal_y_compl :
    (ow_loop_body ow_adv lazy_query).inRange ow_challenge_y.compl.range := by
  show (ow_adv >>= fun _ =>
        Program.get oracle_input >>= fun inp =>
          lazy_query inp >>= fun y =>
            Program.set oracle_output y).inRange ow_challenge_y.compl.range
  refine Program.inRange_bind h_ow_adv_chal_y ?_
  intro _
  refine Program.inRange_bind
    (Program.inRange_mono (Program.inRange_get _)
      (Lens.range_le_compl_of_disjoint oracle_input ow_challenge_y)) ?_
  intro inp
  refine Program.inRange_bind ?_ ?_
  · exact Program.inRange_mono (lazy_query_inRange_ro inp)
      (Lens.range_le_compl_of_disjoint random_oracle_state ow_challenge_y)
  · intro y
    exact Program.inRange_mono (Program.inRange_set _ _)
      (Lens.range_le_compl_of_disjoint oracle_output ow_challenge_y)

include h_ow_adv_chal_y in
/-- `ow_loop q` preserves `ow_challenge_y`. -/
private lemma ow_loop_inRange_chal_y_compl (q : ℕ) :
    (ow_loop ow_adv q lazy_query).inRange ow_challenge_y.compl.range := by
  induction q with
  | zero => exact Program.inRange_pure _ _
  | succ n ih =>
    show (ow_loop_body ow_adv lazy_query >>= fun _ =>
          ow_loop ow_adv n lazy_query).inRange _
    exact Program.inRange_bind
      (ow_loop_body_inRange_chal_y_compl ow_adv h_ow_adv_chal_y) (fun _ => ih)

include h_ow_adv h_ow_adv_chal_y in
/-- **Bookkeeping**: if the experiment's result bit is `true`, then the final
    random oracle has `ow_response` as a preimage of `ow_challenge_y`.

    **Status: infrastructure complete, proof body still sorry.**

    Infrastructure now in place (this session):
    * `lazy_query_inRange_ro` in `RO.lean` — `lazy_query`'s writes are confined
      to the random oracle.
    * `ow_loop_body_inRange_chal_y_compl`, `ow_loop_inRange_chal_y_compl` —
      the loop preserves `ow_challenge_y` (uses `h_ow_adv_chal_y` plus the
      `disjoint_*_ow_challenge_y` axioms).
    * `h_ow_adv_chal_y` — the new hypothesis that the adversary preserves the
      challenge value.
    * `disjoint_*_ow_challenge_y` and `disjoint_*_ow_response` axioms — enough
      pairwise disjointness to push preservation through all the framework
      reads/writes.

    What remains: the wp invariant threading itself (~80–100 lines). The
    cleanest implementation would add `Program.wp_strengthen_lens_preserved`
    to `ProgramRange.lean` first — a general lemma saying that for any
    `p.inRange L.compl.range`, `p.wp F σ = p.wp (fun aσ' => if L.get aσ'.2 =
    L.get σ then F aσ' else 0) σ`. With that helper, the OW bookkeeping
    reduces to a 5-step strengthen-and-descend (mirroring CR's
    `cr_true_implies_collision_wp`):

    1. Strengthen `ow_loop` with `ow_challenge_y` preservation
       (using `ow_loop_inRange_chal_y_compl`).
    2. Strengthen the final `lazy_query resp` with `writes_output`,
       `preserves_disjoint` for `ow_response`, and `preserves_disjoint` for
       `ow_challenge_y`.
    3. Propagate via `Program.wp_le_wp_of_le` through `lazy_init`, `uniform`,
       `set ow_challenge_x`, `lazy_query x`, `set ow_challenge_y` (all
       trivially), and the strengthened `ow_loop` / `get ow_response`.
    4. At the leaf, `split_ifs` on the strengthening conditions + the
       `decide`. In the all-true branch, derive `is_preimage σ_final` from
       the threaded `y_check = y_orig` plus the preservation invariants.
    5. Other branches: 0 ≤ preimage_indicator. -/
lemma ow_true_implies_preimage_wp (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ₀
    ≤ (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => preimage_indicator bσ.2) σ₀ := by
  sorry

/-! ## Phase 4 — Probability bound on preimage_indicator

The bookkeeping lemma reduces `P[win]` to `P[preimage_indicator at end]`,
which we now bound by `(q + 2) / |output|`. Decomposed into layers
analogous to CR's Layer A–D, but with a *linear* bound instead of quadratic
(since each `lazy_query` has at most `1/|output|` chance of producing the
fixed challenge value, rather than `RO_size/|output|`).

**Layer A_OW** (per-query bound): each `lazy_query` bumps the expected
"useful preimage" indicator by at most `1/|output|`. The "useful preimage"
is a preimage of `ow_challenge_y` other than `ow_challenge_x` — i.e., a
preimage the adversary actually "found" rather than the trivially-cached
challenge entry.

**Layer C_OW** (loop accumulation): by induction on `q`, `ow_loop q` bumps
the useful_preimage indicator by ≤ `q / |output|`.

**Layer D_OW** (full composition): combine the initial `lazy_query` (which
defines `y` and contributes the trivial preimage `x_orig`), the loop, and
the final `lazy_query` (which contributes one more potential preimage).
Total: `P[preimage_indicator at end] ≤ 1/|input| + (q+1)/|output|`, where
the `1/|input|` accounts for the adversary guessing `x_orig` and the
`(q+1)/|output|` is the union bound over `q+1` fresh `lazy_query` calls
that could match `y`.

For the clean `(q+2)/|output|` statement below, we assume `|input| ≥ |output|`
via an axiom (standard hash-function assumption). -/

/-- Standard hash-function assumption: the input space is at least as large
    as the output space. -/
axiom card_input_ge_output : Fintype.card output ≤ Fintype.card input

include h_ow_adv in
/-- **Layer D_OW**: probability bound on `preimage_indicator` at the end of
    the experiment.

    Proof would proceed by:
    1. Define `useful_preimage σ := ∃ x' ≠ ow_challenge_x σ, RO σ x' = some (ow_challenge_y σ)`.
    2. Show: each fresh `lazy_query x'` (with `x' ≠ ow_challenge_x`) bumps
       `useful_preimage_indicator` by ≤ `1/|output|` (Layer A_OW).
    3. By induction on `q`: `ow_loop q` bumps by ≤ `q/|output|` (Layer C_OW).
    4. Combine: total bound on useful_preimage = `(q+1)/|output|`.
    5. Decompose preimage_indicator = (resp = ow_challenge_x case) +
       (useful_preimage case). The first ≤ 1/|input| ≤ 1/|output|. -/
private lemma ow_preimage_bound (q : ℕ) (σ₀ : state) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => preimage_indicator bσ.2) σ₀
    ≤ ((q + 2) : ENNReal) / Fintype.card output := by
  sorry

include h_ow_adv h_ow_adv_chal_y in
/-- **Birthday-style bound** for the lazy one-wayness experiment.
    Composes the bookkeeping lemma (`ow_true_implies_preimage_wp`) with the
    probability bound (`ow_preimage_bound`). -/
theorem ow_lazy_bound (q : ℕ) (σ₀ : state) :
    ((ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ ((q + 2) : ENNReal) / Fintype.card output :=
  le_trans (ow_true_implies_preimage_wp ow_adv h_ow_adv h_ow_adv_chal_y q σ₀)
    (ow_preimage_bound ow_adv h_ow_adv q σ₀)

include h_ow_adv in
/-- **Transfer of `ow_transfer` from the SubProb marginal level to the
    `wp` level**, for postconditions that depend only on the result bit. -/
lemma ow_transfer_wp_of_bit (q : ℕ) (σ₀ : state) (G : Bool → ENNReal) :
    (ow_experiment ow_adv q lazy_init lazy_query).wp
        (fun bσ : Bool × state => G bσ.1) σ₀
    = (ow_experiment ow_adv q random_oracle_init random_oracle_query).wp
        (fun bσ : Bool × state => G bσ.1) σ₀ := by
  have h_wp_to_marg : ∀ (p : Program state Bool) (σ : state),
      p.wp (fun bσ : Bool × state => G bσ.1) σ
        = (p σ >>= fun bσ : Bool × state =>
            (pure bσ.1 : SubProbability Bool)).expected G := by
    intro p σ
    change (p σ).expected (fun bσ : Bool × state => G bσ.1)
         = (p σ >>= fun bσ : Bool × state =>
              (pure bσ.1 : SubProbability Bool)).expected G
    rw [SubProbability.expected_bind]
    congr 1
    funext bσ
    exact (expected_pure _).symm
  rw [h_wp_to_marg, h_wp_to_marg, ow_transfer ow_adv h_ow_adv]

include h_ow_adv h_ow_adv_chal_y in
/-- One-wayness bound for the eager (true random oracle) game, obtained by
    transferring `ow_lazy_bound` via `ow_transfer`. -/
theorem ow_eager_bound (q : ℕ) (σ₀ : state) :
    ((ow_experiment ow_adv q random_oracle_init random_oracle_query).wp
        (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0)) σ₀
    ≤ ((q + 2) : ENNReal) / Fintype.card output := by
  rw [← ow_transfer_wp_of_bit ow_adv h_ow_adv q σ₀
        (fun b => if b then (1 : ENNReal) else 0)]
  exact ow_lazy_bound ow_adv h_ow_adv h_ow_adv_chal_y q σ₀

end OWParam
