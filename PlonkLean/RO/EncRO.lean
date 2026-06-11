import PlonkLean.RO.OneWayness_GameHop.Definitions
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment
import PlonkLean.RO.OneWayness_GameHop.UpToBad
import PlonkLean.RO.OneWayness_GameHop.Game1

/-!
# IND-security of the hashed one-time pad

The encryption `Enc(k, m) = H(k) ⊕ m` with `H` a random oracle and key
`k ← input` is left-or-right indistinguishable: an adversary making at
most `q` oracle queries cannot tell an encryption of `m₀` from one of
`m₁`, beyond its chance of querying the key:

```
|Pr[A : guess | enc m₀] − Pr[A : guess | enc m₁]| ≤ 2 (q + 1) / |input|
```

## Proof, by game hopping

The challenger samples the key `k`, computes `H(k)` (a fresh uniform value
on the empty cache), publishes the ciphertext `c = H(k) ⊕ m_b`, then runs
the adversary's query loop. The two worlds differ only in `m_b`.

* **Preprogramming** (`enc_game_eq_pre`): `H(k)` on the empty oracle is a
  fresh `uniform` written into `RO[k]`, exposing the sample that the OTP
  coupling acts on.
* **One-time-pad coupling + up-to-bad** (`enc_game_relE`): couple the key
  samples by identity and the masks by the bijection `hk ↦ hk + (m₀ − m₁)`,
  so the *published ciphertexts coincide* (`hk + m₀ = (hk + m₀ − m₁) + m₁`).
  The two runs then differ only at `RO[k]` — exactly the OW up-to-bad
  invariant `InvUB k hk` — so the shared loop body relates by the OW core
  `body_relE`, and the guesses agree until the adversary queries `k`.
* **Bad bound** (Stage 2, *outstanding*): `Pr[adversary queries k] ≤
  (q+1)/|input|`. This is a deferred-sampling reduction to the
  `guess_experiment` framework: the key's sampling commutes past the
  adversary loop (the published ciphertext `c = H(k) + m` is independent
  of `k`, so the queries are independent of `k`). Structurally the same
  chain as the OW bad-event bound; not yet ported here.

We reuse `ow_challenge_x` as the **key register** and `chal_x_queried_gh`
as the **"queried the key" flag**, so `lazy_query_tracked` and the entire
OW up-to-bad core (`body_relE`, `InvUB`, …) apply verbatim.

## Status

Stage 1 is complete (`enc_guess_le`): the indistinguishability bound up to
the bad event, proved by the OTP coupling + up-to-bad reuse. Stage 2 (the
quantitative bad bound) is documented above and outstanding. Composing the
two gives the headline `2(q+1)/|output|`-style bound. -/

/-- A commutative group structure on the output type, modelling the
    one-time-pad mask (e.g. bitwise XOR). Axiomatized on the opaque
    `output`, consistent with its other instances. -/
axiom outputCommGroup : AddCommGroup output
attribute [instance] outputCommGroup

/-- The published ciphertext, readable by the adversary. -/
axiom chal_c : Variable output
/-- The adversary's guess bit. -/
axiom guess_var : Variable Bool

axiom disjoint_chal_c_ro : disjoint chal_c random_oracle_state
axiom disjoint_chal_c_chal_x : disjoint chal_c ow_challenge_x
axiom disjoint_chal_c_flag : disjoint chal_c chal_x_queried_gh
axiom disjoint_chal_c_oracle_input : disjoint chal_c oracle_input
axiom disjoint_chal_c_oracle_output : disjoint chal_c oracle_output
axiom disjoint_guess_ro : disjoint guess_var random_oracle_state
axiom disjoint_guess_chal_x : disjoint guess_var ow_challenge_x
axiom disjoint_guess_flag : disjoint guess_var chal_x_queried_gh
axiom disjoint_guess_chal_c : disjoint guess_var chal_c

attribute [instance] disjoint_chal_c_ro disjoint_chal_c_chal_x
  disjoint_chal_c_flag disjoint_chal_c_oracle_input
  disjoint_chal_c_oracle_output disjoint_guess_ro disjoint_guess_chal_x
  disjoint_guess_flag disjoint_guess_chal_c

instance : disjoint random_oracle_state chal_c := disjoint_chal_c_ro.symm
instance : disjoint ow_challenge_x chal_c := disjoint_chal_c_chal_x.symm
instance : disjoint chal_x_queried_gh chal_c := disjoint_chal_c_flag.symm
instance : disjoint oracle_input chal_c := disjoint_chal_c_oracle_input.symm
instance : disjoint oracle_output chal_c := disjoint_chal_c_oracle_output.symm
instance : disjoint random_oracle_state guess_var := disjoint_guess_ro.symm
instance : disjoint ow_challenge_x guess_var := disjoint_guess_chal_x.symm
instance : disjoint chal_x_queried_gh guess_var := disjoint_guess_flag.symm
instance : disjoint chal_c guess_var := disjoint_guess_chal_c.symm

section EncRO

variable (enc_adv : Program state Unit)

/-- The IND game: sample key, compute `H(key)` (the challenger's own,
    *untracked* query), publish `H(key) ⊕ m`, initialize the
    "queried the key" flag, run the adversary's tracked query loop, read
    its guess. The result bit is the adversary's guess. -/
noncomputable def enc_game (m : output) (q : ℕ) : Program state Bool := do
  lazy_init
  let k ← Program.uniform
  Program.set ow_challenge_x k
  let hk ← lazy_query k
  Program.set chal_x_queried_gh false
  Program.set chal_c (hk + m)
  oracle_loop_n enc_adv q lazy_query_tracked
  Program.get guess_var

/-- The preprogrammed form: `H(key)` on the empty oracle is a fresh
    `uniform` sample written into `RO[key]`. -/
noncomputable def enc_game_pre (m : output) (q : ℕ) : Program state Bool := do
  lazy_init
  let k ← Program.uniform
  Program.set ow_challenge_x k
  let hk ← Program.uniform
  Program.set random_oracle_state (fun j => if j = k then some hk else none)
  Program.set chal_x_queried_gh false
  Program.set chal_c (hk + m)
  oracle_loop_n enc_adv q lazy_query_tracked
  Program.get guess_var

/-! ## The win indicator and bad event -/

/-- Result indicator: the adversary's guess fired. -/
private def winI (bσ : Bool × state) : ENNReal := if bσ.1 then 1 else 0

/-- Bad event: the adversary queried the key. -/
private def badP (σ : state) : Prop := chal_x_queried_gh.get σ = true

/-- The up-to-bad post: the bad flags agree, and on good runs the guesses
    agree. -/
private def encPost (bσ₁ bσ₂ : Bool × state) : Prop :=
  chal_x_queried_gh.get bσ₁.2 = chal_x_queried_gh.get bσ₂.2
  ∧ (chal_x_queried_gh.get bσ₁.2 = false → bσ₁.1 = bσ₂.1)

end EncRO

/-! ## Stage 1: indistinguishability up to the bad event

The two encryption worlds, after preprogramming, are related by one
`relE` judgment whose post is `encPost`. The loop reuses the OW up-to-bad
body coupling `body_relE` verbatim. -/

section EncStage1

variable (enc_adv : Program state Unit)
variable (h_RO : enc_adv.inRange random_oracle_state.compl.range)
variable (h_flag : enc_adv.inRange chal_x_queried_gh.compl.range)
variable (h_cx : enc_adv.inRange ow_challenge_x.compl.range)
variable (h_mass : ∀ σ, enc_adv.wp (fun _ => (1 : ENNReal)) σ = 1)

/-- Reading the guess through the `RO[k]`-overwrite is invisible. -/
private lemma guess_get_insRO (k : input) (y : output) (σ : state) :
    guess_var.get (insRO k y σ) = guess_var.get σ :=
  get_insRO guess_var k y σ

include h_RO h_flag h_cx h_mass in
/-- The shared tail (adversary loop + read guess): from `InvUB k y` it
    lands in `encPost`. The loop is `body_relE`; the ending is `get_get`
    plus the overwrite-invisibility of the guess. -/
private lemma enc_tail_relE (k : input) (y : output) (q : ℕ) :
    (loop_n q (oracle_step enc_adv lazy_query_tracked) >>= fun _ : Unit =>
      Program.get guess_var).relE
    (loop_n q (oracle_step enc_adv lazy_query_tracked) >>= fun _ : Unit =>
      Program.get guess_var)
    (InvUB k y) encPost := by
  refine Program.relE.bind (Mid := fun u v : Unit × state => InvUB k y u.2 v.2)
    (Program.relE.loop_n (body_relE enc_adv h_RO h_flag h_cx h_mass k y) q)
    (fun _ _ => ?_)
  refine Program.relE.get_get ?_
  intro σ₁ σ₂ hinv
  dsimp only at hinv
  obtain ⟨hfeq, hgood⟩ := hinv
  refine ⟨hfeq, fun hf => ?_⟩
  obtain ⟨_, hσ⟩ := hgood hf
  have h : guess_var.get σ₁ = guess_var.get σ₂ := by
    rw [hσ]; exact guess_get_insRO k y σ₂
  exact h

include h_RO h_flag h_cx h_mass in
/-- **The one-time-pad coupling**: from the common post-prefix state
    (key `= k`, oracle empty), the two worlds relate at `encPost`. The
    fresh mask is coupled by `hk ↦ hk + (m₀ − m₁)`, making the published
    ciphertexts coincide; the runs then differ only at `RO[k]`. -/
private lemma enc_otp_tail_relE (m₀ m₁ : output) (k : input) (q : ℕ) :
    ((Program.uniform : Program state output) >>= fun hk =>
      Program.set random_oracle_state (fun j => if j = k then some hk else none)
        >>= fun _ => Program.set chal_x_queried_gh false >>= fun _ =>
      Program.set chal_c (hk + m₀) >>= fun _ =>
      oracle_loop_n enc_adv q lazy_query_tracked >>= fun _ =>
      Program.get guess_var).relE
    ((Program.uniform : Program state output) >>= fun hk =>
      Program.set random_oracle_state (fun j => if j = k then some hk else none)
        >>= fun _ => Program.set chal_x_queried_gh false >>= fun _ =>
      Program.set chal_c (hk + m₁) >>= fun _ =>
      oracle_loop_n enc_adv q lazy_query_tracked >>= fun _ =>
      Program.get guess_var)
    (fun σ₁ σ₂ => σ₁ = σ₂ ∧ ow_challenge_x.get σ₂ = k) encPost := by
  haveI : disjoint random_oracle_state chal_x_queried_gh :=
    disjoint_chal_x_queried_gh_ro.symm
  -- couple the masks: hk₁ = hk₀ + (m₀ − m₁)
  refine Program.relE.bind
    (Mid := fun u v : output × state =>
      v.1 = u.1 + (m₀ - m₁) ∧ v.2 = u.2 ∧ ow_challenge_x.get u.2 = k)
    (Program.relE.uniform_bij (Equiv.addRight (m₀ - m₁)) ?_) (fun hk₀ hk₁ => ?_)
  · rintro hk σ₁ σ₂ ⟨rfl, hkey⟩
    exact ⟨rfl, rfl, hkey⟩
  · -- the three sets establish `InvUB k hk₀`, then `enc_tail_relE`
    rw [oracle_loop_n_eq_loop_n]
    -- the shared state equation: after the sets, the runs differ only at RO[k]
    have hstate : hk₁ = hk₀ + (m₀ - m₁) → ∀ τ : state, ow_challenge_x.get τ = k →
        chal_c.set (hk₀ + m₀) (chal_x_queried_gh.set false
          (random_oracle_state.set (fun j => if j = k then some hk₀ else none) τ))
        = insRO k hk₀ (chal_c.set (hk₁ + m₁) (chal_x_queried_gh.set false
          (random_oracle_state.set (fun j => if j = k then some hk₁ else none) τ)))
        ∧ ow_challenge_x.get (chal_c.set (hk₁ + m₁) (chal_x_queried_gh.set false
            (random_oracle_state.set (fun j => if j = k then some hk₁ else none) τ))) = k
        ∧ chal_x_queried_gh.get (chal_c.set (hk₁ + m₁) (chal_x_queried_gh.set false
            (random_oracle_state.set (fun j => if j = k then some hk₁ else none) τ)))
            = false := by
      intro hhk' τ hkey
      have hcc : hk₁ + m₁ = hk₀ + m₀ := by rw [hhk']; abel
      refine ⟨?_, ?_, ?_⟩
      · rw [hcc]
        unfold insRO
        simp only [Lens.get_of_disjoint_set random_oracle_state chal_c,
          Lens.get_of_disjoint_set random_oracle_state chal_x_queried_gh,
          random_oracle_state.set_get]
        rw [show (fun j => if j = k then some hk₀
                  else if j = k then some hk₁ else none)
              = (fun j => if j = k then some hk₀ else none) from by
            funext j; by_cases hj : j = k <;> simp [hj]]
        rw [(inferInstance : disjoint random_oracle_state chal_c).commute,
            (inferInstance : disjoint random_oracle_state chal_x_queried_gh).commute,
            random_oracle_state.set_set]
      · rw [Lens.get_of_disjoint_set ow_challenge_x chal_c,
            Lens.get_of_disjoint_set ow_challenge_x chal_x_queried_gh,
            Lens.get_of_disjoint_set ow_challenge_x random_oracle_state]
        exact hkey
      · rw [Lens.get_of_disjoint_set chal_x_queried_gh chal_c,
            chal_x_queried_gh.set_get]
    constructor
    · intro F G hFG τ₁ τ₂ hpre
      obtain ⟨hhk', hσ, hkey⟩ := hpre
      rw [show τ₂ = τ₁ from hσ]
      rw [Program.wp_set_seq, Program.wp_set_seq, Program.wp_set_seq,
          Program.wp_set_seq, Program.wp_set_seq, Program.wp_set_seq]
      obtain ⟨heq, hkey', hf'⟩ := hstate hhk' τ₁ hkey
      exact (enc_tail_relE enc_adv h_RO h_flag h_cx h_mass k hk₀ q).1 F G hFG _ _
        (invUB_of_good hf' hkey' heq)
    · intro F G hFG τ₂ τ₁ hpre
      obtain ⟨hhk', hσ, hkey⟩ := hpre
      rw [show τ₂ = τ₁ from hσ]
      rw [Program.wp_set_seq, Program.wp_set_seq, Program.wp_set_seq,
          Program.wp_set_seq, Program.wp_set_seq, Program.wp_set_seq]
      obtain ⟨heq, hkey', hf'⟩ := hstate hhk' τ₁ hkey
      exact (enc_tail_relE enc_adv h_RO h_flag h_cx h_mass k hk₀ q).2 F G hFG _ _
        (invUB_of_good hf' hkey' heq)

include h_RO h_flag h_cx h_mass in
/-- **The game-level coupling**: the two preprogrammed worlds relate at
    `encPost` — flags agree, and on good runs the guesses agree. Peels the
    shared prefix (`lazy_init`, key sample, `set key`) and applies the OTP
    tail. -/
theorem enc_game_pre_relE (m₀ m₁ : output) (q : ℕ) :
    (enc_game_pre enc_adv m₀ q).relE (enc_game_pre enc_adv m₁ q) Eq encPost := by
  constructor
  · intro F G hFG σ σ' hpre
    cases hpre
    unfold enc_game_pre lazy_init
    rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
    rw [Program.wp_uniform_seq]; conv_rhs => rw [Program.wp_uniform_seq]
    refine Finset.sum_le_sum fun k _ => ENNReal.div_le_div_right ?_ _
    rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
    exact (enc_otp_tail_relE enc_adv h_RO h_flag h_cx h_mass m₀ m₁ k q).1
      F G hFG _ _ ⟨rfl, ow_challenge_x.set_get _ _⟩
  · intro F G hFG σ σ' hpre
    cases hpre
    unfold enc_game_pre lazy_init
    rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
    rw [Program.wp_uniform_seq]; conv_rhs => rw [Program.wp_uniform_seq]
    refine Finset.sum_le_sum fun k _ => ENNReal.div_le_div_right ?_ _
    rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
    exact (enc_otp_tail_relE enc_adv h_RO h_flag h_cx h_mass m₀ m₁ k q).2
      F G hFG _ _ ⟨rfl, ow_challenge_x.set_get _ _⟩

end EncStage1

/-! ## The preprogramming mini-hop -/

section EncMiniHop

variable (enc_adv : Program state Unit)

/-- `H(key)` on the empty oracle is a fresh `uniform` written into `RO[key]`:
    `enc_game` and `enc_game_pre` have equal wp. -/
theorem enc_game_wp_eq_pre (m : output) (q : ℕ)
    (F : Bool × state → ENNReal) (σ : state) :
    (enc_game enc_adv m q).wp F σ = (enc_game_pre enc_adv m q).wp F σ := by
  unfold enc_game enc_game_pre lazy_init
  rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
  rw [Program.wp_uniform_seq]; conv_rhs => rw [Program.wp_uniform_seq]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
  -- at σ_k = ow_challenge_x.set k (RO.set (fun _ => none) σ): RO is empty
  set σ_k : state := ow_challenge_x.set k (random_oracle_state.set (fun _ => none) σ)
    with hσk
  have h_empty : random_oracle_state.get σ_k = fun _ => none := by
    rw [hσk, Lens.get_of_disjoint_set random_oracle_state ow_challenge_x,
        random_oracle_state.set_get]
  rw [wp_bind, lazy_query_on_totally_empty_RO k σ_k h_empty]
  simp only [wp_bind, wp_uniform, wp_set, wp_pure]

end EncMiniHop

/-! ## Stage 1 result: indistinguishability up to the bad event -/

section EncIndist

variable (enc_adv : Program state Unit)
variable (h_RO : enc_adv.inRange random_oracle_state.compl.range)
variable (h_flag : enc_adv.inRange chal_x_queried_gh.compl.range)
variable (h_cx : enc_adv.inRange ow_challenge_x.compl.range)
variable (h_mass : ∀ σ, enc_adv.wp (fun _ => (1 : ENNReal)) σ = 1)

include h_RO h_flag h_cx h_mass in
/-- **One-sided up-to-bad bound**: the guess probability in world `m₀` is
    at most that in world `m₁` plus the chance the adversary queries the
    key. (`enc_game_pre`-level; the mini-hop transfers it to `enc_game`.) -/
theorem enc_guess_le_pre (m₀ m₁ : output) (q : ℕ) (σ : state) :
    (enc_game_pre enc_adv m₀ q).wp (fun bσ => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (enc_game_pre enc_adv m₁ q).wp (fun bσ => if bσ.1 then (1 : ENNReal) else 0) σ
      + (enc_game_pre enc_adv m₀ q).wp
          (fun bσ => if chal_x_queried_gh.get bσ.2 = true then
            (if bσ.1 then (1 : ENNReal) else 0) else 0) σ := by
  refine Program.relE.up_to_bad (bad := fun s => chal_x_queried_gh.get s = true)
    (fun bσ => if bσ.1 then (1 : ENNReal) else 0)
    (enc_game_pre_relE enc_adv h_RO h_flag h_cx h_mass m₀ m₁ q)
    (fun u v h => by dsimp only; rw [h.1]) ?_ σ
  intro u v h hbad
  have hf : chal_x_queried_gh.get u.2 = false := Bool.not_eq_true _ |>.mp hbad
  dsimp only
  rw [h.2 hf]

include h_RO h_flag h_cx h_mass in
/-- **Indistinguishability up to the bad event** (at the `enc_game` level).
    The guess probability in world `m₀` exceeds that in world `m₁` by at
    most the chance the adversary queries the key. -/
theorem enc_guess_le (m₀ m₁ : output) (q : ℕ) (σ : state) :
    (enc_game enc_adv m₀ q).wp (fun bσ => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ (enc_game enc_adv m₁ q).wp (fun bσ => if bσ.1 then (1 : ENNReal) else 0) σ
      + (enc_game enc_adv m₀ q).wp
          (fun bσ => if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ := by
  rw [enc_game_wp_eq_pre, enc_game_wp_eq_pre, enc_game_wp_eq_pre]
  refine le_trans (enc_guess_le_pre enc_adv h_RO h_flag h_cx h_mass m₀ m₁ q σ) ?_
  gcongr
  apply Program.wp_le_wp_of_le
  intro bσ
  by_cases hb : chal_x_queried_gh.get bσ.2 = true
  · rw [if_pos hb]; split_ifs <;> simp
  · rw [if_neg hb, if_neg hb]

end EncIndist

/-! ## Stage 2: bounding the bad event

`Pr[adversary queries the key] ≤ (q+1)/|input|`. We drop the `RO[key]`
preprogramming (the runs are identical until the key is queried), reindex
the mask to a fresh independent ciphertext, and bound by a
`guess_experiment` built from the OW `body_game_1`/`final_game_1` — for
which `game_1_correspondence` already supplies the schema inequality. -/

section EncBad

variable (enc_adv : Program state Unit)

/-- The game with `H(key)` *not* preprogrammed into `RO[key]`: a lazy query
    to the key would sample fresh. Identical to `enc_game_pre` until the
    key is queried (the bad event). -/
noncomputable def enc_game_nopre (m : output) (q : ℕ) : Program state Bool := do
  lazy_init
  let k ← Program.uniform
  Program.set ow_challenge_x k
  let hk ← Program.uniform
  Program.set chal_x_queried_gh false
  Program.set chal_c (hk + m)
  oracle_loop_n enc_adv q lazy_query_tracked
  Program.get guess_var

variable (h_RO : enc_adv.inRange random_oracle_state.compl.range)
variable (h_flag : enc_adv.inRange chal_x_queried_gh.compl.range)
variable (h_cx : enc_adv.inRange ow_challenge_x.compl.range)
variable (h_mass : ∀ σ, enc_adv.wp (fun _ => (1 : ENNReal)) σ = 1)

/-- State algebra: after the (differing) preprogramming step, the
    preprogrammed run sits at `InvUB k hk` over the lazy run. -/
private lemma enc_bad_invUB (k : input) (hk m : output) (s : state) :
    InvUB k hk
      (chal_c.set (hk + m) (chal_x_queried_gh.set false
        (random_oracle_state.set (fun j => if j = k then some hk else none)
          (ow_challenge_x.set k (random_oracle_state.set (fun _ => none) s)))))
      (chal_c.set (hk + m) (chal_x_queried_gh.set false
        (ow_challenge_x.set k (random_oracle_state.set (fun _ => none) s)))) := by
  haveI : disjoint random_oracle_state chal_x_queried_gh :=
    disjoint_chal_x_queried_gh_ro.symm
  refine invUB_of_good ?_ ?_ ?_
  · rw [Lens.get_of_disjoint_set chal_x_queried_gh chal_c, chal_x_queried_gh.set_get]
  · rw [Lens.get_of_disjoint_set ow_challenge_x chal_c,
        Lens.get_of_disjoint_set ow_challenge_x chal_x_queried_gh,
        ow_challenge_x.set_get]
  · unfold insRO
    simp only [Lens.get_of_disjoint_set random_oracle_state chal_c,
      Lens.get_of_disjoint_set random_oracle_state chal_x_queried_gh,
      Lens.get_of_disjoint_set random_oracle_state ow_challenge_x,
      random_oracle_state.set_get]
    rw [(inferInstance : disjoint random_oracle_state chal_c).commute,
        (inferInstance : disjoint random_oracle_state chal_x_queried_gh).commute]

include h_RO h_flag h_cx h_mass in
/-- **Dropping the preprogramming is invisible to the bad event.** The two
    games differ only by `set RO[key]`, so they sit at `InvUB`, and their
    bad flags agree (`relE.bad_eq`). -/
theorem enc_pre_bad_eq_nopre (m : output) (q : ℕ) (σ : state) :
    (enc_game_pre enc_adv m q).wp
        (fun bσ => if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ
    = (enc_game_nopre enc_adv m q).wp
        (fun bσ => if chal_x_queried_gh.get bσ.2 = true then (1 : ENNReal) else 0) σ := by
  have hrel : (enc_game_pre enc_adv m q).relE (enc_game_nopre enc_adv m q) Eq encPost := by
    constructor
    · intro F G hFG σ₁ σ₂ hpre
      subst hpre
      unfold enc_game_pre enc_game_nopre lazy_init
      rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
      rw [Program.wp_uniform_seq]; conv_rhs => rw [Program.wp_uniform_seq]
      refine Finset.sum_le_sum fun k _ => ENNReal.div_le_div_right ?_ _
      rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
      rw [Program.wp_uniform_seq]; conv_rhs => rw [Program.wp_uniform_seq]
      refine Finset.sum_le_sum fun hk _ => ENNReal.div_le_div_right ?_ _
      rw [Program.wp_set_seq, Program.wp_set_seq, Program.wp_set_seq]
      conv_rhs => rw [Program.wp_set_seq, Program.wp_set_seq]
      rw [oracle_loop_n_eq_loop_n]
      exact (enc_tail_relE enc_adv h_RO h_flag h_cx h_mass k hk q).1 F G hFG _ _
        (enc_bad_invUB k hk m _)
    · intro F G hFG σ₂ σ₁ hpre
      subst hpre
      unfold enc_game_pre enc_game_nopre lazy_init
      rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
      rw [Program.wp_uniform_seq]; conv_rhs => rw [Program.wp_uniform_seq]
      refine Finset.sum_le_sum fun k _ => ENNReal.div_le_div_right ?_ _
      rw [Program.wp_set_seq]; conv_rhs => rw [Program.wp_set_seq]
      rw [Program.wp_uniform_seq]; conv_rhs => rw [Program.wp_uniform_seq]
      refine Finset.sum_le_sum fun hk _ => ENNReal.div_le_div_right ?_ _
      conv_lhs => rw [Program.wp_set_seq, Program.wp_set_seq]
      rw [Program.wp_set_seq, Program.wp_set_seq, Program.wp_set_seq]
      rw [oracle_loop_n_eq_loop_n]
      exact (enc_tail_relE enc_adv h_RO h_flag h_cx h_mass k hk q).2 F G hFG _ _
        (enc_bad_invUB k hk m _)
  exact Program.relE.bad_eq (bad := fun s => chal_x_queried_gh.get s = true)
    hrel (fun u v h => by dsimp only; rw [h.1]) σ

/-- The env of the bad-event guess experiment: lazy oracle, then publish a
    fresh uniform ciphertext (the mask reindex makes `m` disappear). -/
noncomputable def env_c : Program state Unit := do
  lazy_init
  let c ← Program.uniform
  Program.set chal_c c

include h_cx h_flag in
/-- **The guess-experiment bound** for the bad event: the adversary hits
    the uniform key with probability `≤ (q+1)/|input|`. Reuses OW's
    `game_1_correspondence` (env-generic) + the generic interim bound. -/
theorem gexp_env_c_bound
    (h_qi : enc_adv.inRange queries_input.compl.range)
    (q : ℕ) (σ : state) :
    (guess_experiment env_c Program.uniform ow_challenge_x chal_x_queried_gh
        (body_game_1 enc_adv) final_game_1 q).wp
      (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ
    ≤ ((q + 1) : ENNReal) / Fintype.card input := by
  refine le_trans (guess_experiment_le_interim_assumption env_c ow_challenge_x
    chal_x_queried_gh queries_input (body_game_1 enc_adv) final_game_1
    (body_recording_game_1 enc_adv) final_recording_game_1 q
    (game_1_correspondence enc_adv h_cx h_flag h_qi q) σ) ?_
  apply guess_experiment_interim_wp_bound
  intro σ'
  have h_post_eq : (fun aσ : Unit × state =>
        ((queries_input.get aσ.2).length : ENNReal) / Fintype.card input)
      = fun aσ : Unit × state => (Fintype.card input : ENNReal)⁻¹ *
            ((queries_input.get aσ.2).length : ENNReal) := by
    funext aσ; rw [div_eq_mul_inv, mul_comm]
  rw [h_post_eq, Program.wp_const_mul]
  rw [show ((q + 1 : ℕ) : ENNReal) / Fintype.card input
        = (Fintype.card input : ENNReal)⁻¹ * ((q + 1 : ℕ) : ENNReal) from by
      rw [div_eq_mul_inv, mul_comm]]
  refine mul_le_mul' (le_refl _) ?_
  have h_inner : ∀ σ₀ : state,
      (Program.set queries_input [] >>= fun _ =>
        loop_n q (body_recording_game_1 enc_adv) >>= fun _ =>
        final_recording_game_1).wp
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal)) σ₀
      ≤ ((q + 1 : ℕ) : ENNReal) := by
    intro σ₀
    rw [wp_bind, wp_set]
    set σ_init := queries_input.set [] σ₀ with σ_init_def
    have h_qs_init : (queries_input.get σ_init).length = 0 := by
      simp [σ_init_def, Lens.set_get]
    rw [wp_bind]
    refine le_trans (Program.wp_le_wp_of_le _ _
        (fun aσ : Unit × state =>
          ((queries_input.get aσ.2).length : ENNReal) + 1)
        (fun _ => final_recording_game_1_qs_length_bump _) σ_init) ?_
    rw [Program.wp_add (loop_n q (body_recording_game_1 enc_adv))
        (fun aσ : Unit × state => ((queries_input.get aσ.2).length : ENNReal))
        (fun _ : Unit × state => (1 : ENNReal))]
    refine le_trans (add_le_add (loop_n_wp_linear_bound (body_recording_game_1 enc_adv)
        (fun σ => ((queries_input.get σ).length : ENNReal)) 1
        (fun σ_body => body_recording_game_1_qs_length_bump enc_adv h_qi σ_body)
        q σ_init) (Program.wp_const_le _ _ _)) ?_
    rw [h_qs_init]
    push_cast; ring_nf; rfl
  -- peel env_c (lazy_init; uniform c; set chal_c c), all queries_input-preserving
  unfold env_c lazy_init
  simp only [Program.bind_assoc]
  rw [Program.wp_set_seq, Program.wp_uniform_seq]
  refine le_trans (Finset.sum_le_sum (fun c _ =>
    ENNReal.div_le_div_right
      (by rw [Program.wp_set_seq]; exact h_inner _) _))
    (le_of_eq (sum_const_div_card _))

end EncBad
