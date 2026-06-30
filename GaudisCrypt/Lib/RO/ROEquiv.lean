import GaudisCrypt.Lib.RO.Basic
import GaudisCrypt.Lib.RO.Transfer
import GaudisCrypt.Lib.RO.OracleLoop

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

/-! ## Phase 4 — Oracle loops parameterised by an adversary

Below, `adv` and `h_adv` are *parameters* (via a `variable` declaration), not
axioms. Every `oracle_loop`-style definition and `adv_conv_eq_conv_adv`–`oracle_loop_wp_lazy_eq_random_oracle*`-style
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


include h_adv in
theorem adv_conv_eq_conv_adv : adv_conv adv = conv_adv adv := by
  change (adv >>= fun _ => convert) = (convert >>= fun _ => adv)
  -- Disjointness of the lens-complement with the lens itself (an equality, hence ≤).
  have h_disj : random_oracle_state.compl.range ≤ (random_oracle_state.range)ᶜ :=
    le_of_eq (DetermFootprint.complement_range _)
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
  -- Step 4: bind_assoc reverse, then adv_conv_eq_conv_adv, then bind_assoc.
  rw [← Program.bind_assoc,
      show (adv >>= fun _ => convert) = (convert >>= fun _ => adv) from adv_conv_eq_conv_adv adv h_adv,
      Program.bind_assoc]
  rfl

/-! The `oracle_loop`, `loop_body_lazy`, and `loop_body_eager` definitions
    now live in `PlonkLean.RO.OracleLoop` alongside `oracle_step` and
    `oracle_loop_n`. The lazy = eager proof for `oracle_loop` (below) uses
    them via explicit `adv` arguments. -/

include h_adv in
/-- The transfer-form of the body equality: the lazy and eager loop bodies
    are related by `Program.transfer`. Derived from `body_convert_eq` by
    converting the Unit-valued bind form to the transfer form. -/
private lemma transfer_loop_body :
    Program.transfer (loop_body_lazy adv) (loop_body_eager adv) := by
  show ((loop_body_lazy adv) >>= fun u : Unit =>
         convert >>= fun _ : Unit => (Pure.pure u : Program state Unit))
      = (convert >>= fun _ : Unit => loop_body_eager adv)
  -- For Unit-valued, (λu. convert >>= pure u) = (λ_. convert).
  rw [show (fun u : Unit => convert >>= fun _ : Unit => (Pure.pure u : Program state Unit))
          = (fun _ : Unit => convert) from by
        funext u
        rw [show (Pure.pure u : Program state Unit) = (Pure.pure () : Program state Unit) from rfl]
        exact Program.bind_pure _]
  -- Now it's the bind form, which is body_convert_eq via definitional unfolding.
  exact body_convert_eq adv h_adv

include h_adv in
/-- **The full `oracle_loop` transfer**: lazy and eager `oracle_loop`s
    transfer to each other, built via the transfer framework (no Kleene
    plumbing in this file).

    The proof is a `Program.transfer_bind` chain over the four components
    of `oracle_loop` (set want_more, init, while_loop, get adversary_result).
    The `while_loop` component is discharged by `Program.transfer_while_loop`,
    which contains the Kleene argument in abstract form. -/
theorem Program.transfer_oracle_loop :
    Program.transfer
      (oracle_loop adv lazy_init lazy_query)
      (oracle_loop adv random_oracle_init random_oracle_query) := by
  unfold oracle_loop
  refine Program.transfer_bind (Program.transfer_set_of_disjoint_ro want_more true) ?_
  intro _
  refine Program.transfer_bind Program.transfer_lazy_init ?_
  intro _
  refine Program.transfer_bind ?_ ?_
  · -- while_loop transfers via the closure law.
    refine Program.transfer_while_loop
      (Program.get_inRange_compl_of_disjoint want_more random_oracle_state) ?_
    exact transfer_loop_body adv h_adv
  intro _
  exact Program.transfer_get_of_disjoint_ro adversary_result

/-- `convert` is absorbed by the eager `oracle_loop`. The loop starts with
    `Program.set want_more true >>= random_oracle_init >>= ...`, so we push
    `convert` past the (RO-disjoint) `set want_more true` and then absorb
    it via `convert_bind_random_oracle_init_bind`. -/
lemma convert_bind_oracle_loop_eager :
    (convert >>= fun _ : Unit =>
        oracle_loop adv random_oracle_init random_oracle_query)
    = oracle_loop adv random_oracle_init random_oracle_query := by
  unfold oracle_loop
  rw [← Program.bind_assoc]
  rw [show (convert >>= fun _ : Unit => Program.set want_more true)
        = (Program.set want_more true >>= fun _ : Unit => convert)
      from (convert_commutes_set want_more true).symm]
  rw [Program.bind_assoc]
  rw [convert_bind_random_oracle_init_bind]

include h_adv in
/-- The foundational lazy = eager equation for `oracle_loop`: the lazy loop
    composed with `convert` equals the eager loop. Derived from
    `Program.transfer_oracle_loop` plus convert-absorption by the eager
    loop. (This used to be `claim_4`, proved directly via Kleene in this
    file; now the Kleene argument lives in
    `Program.transfer_while_loop` and this theorem is a corollary.) -/
theorem oracle_loop_lazy_convert_eq_random_oracle_loop :
    (oracle_loop adv lazy_init lazy_query >>= fun b => convert >>= fun _ => pure b)
  = oracle_loop adv random_oracle_init random_oracle_query := by
  have h_transfer := Program.transfer_oracle_loop adv h_adv
  show (oracle_loop adv lazy_init lazy_query >>= fun b =>
          convert >>= fun _ : Unit => (Pure.pure b : Program state Bool))
      = oracle_loop adv random_oracle_init random_oracle_query
  rw [h_transfer]
  exact convert_bind_oracle_loop_eager adv


include h_adv in
/-- **wp-level lazy/eager equivalence for `oracle_loop`**: for any
    postcondition `F` invariant under writes to `random_oracle_state`,
    the wp's of the lazy and eager `oracle_loop` agree. Specialisation
    of `Program.transfer_wp_ro_invariant` to `Program.transfer_oracle_loop`. -/
theorem oracle_loop_wp_lazy_eq_random_oracle
    (F : Bool × state → ENNReal)
    (hF_inv : ∀ (b : Bool) (σ : state) (x : input → Option output),
        F (b, random_oracle_state.set x σ) = F (b, σ)) :
    (oracle_loop adv lazy_init lazy_query).wp F
    = (oracle_loop adv random_oracle_init random_oracle_query).wp F := by
  funext σ₀
  exact Program.transfer_wp_ro_invariant
    (Program.transfer_oracle_loop adv h_adv)
    (convert_bind_oracle_loop_eager adv) F hF_inv σ₀

include h_adv in
/-- **SubProb-marginal lazy/eager equivalence**: for any RO-invariant
    projection `h : state → β`, the joint `(bit, h σ)` distribution agrees
    under lazy and eager `oracle_loop`. Specialisation of
    `Program.transfer_marginal_ro_invariant`. -/
theorem oracle_loop_marginal_lazy_eq_random_oracle {β : Type}
    (h : state → β)
    (h_inv : ∀ (σ : state) (x : input → Option output),
        h (random_oracle_state.set x σ) = h σ)
    (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state => (Pure.pure (bσ.1, h bσ.2) : SubProbability (Bool × β)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state => (Pure.pure (bσ.1, h bσ.2) : SubProbability (Bool × β))) :=
  Program.transfer_marginal_ro_invariant
    (Program.transfer_oracle_loop adv h_adv)
    (convert_bind_oracle_loop_eager adv) h h_inv σ₀

include h_adv in
/-- **Form (a) — lens-complement projection.** The joint distribution of
    (adv's bit, the entire non-RO part of state) agrees under lazy and
    eager. Specialisation via `random_oracle_state.compl.get`. -/
theorem oracle_loop_marginal_lazy_eq_random_oracle_compl (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (Pure.pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (Pure.pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid))) := by
  refine oracle_loop_marginal_lazy_eq_random_oracle adv h_adv
    random_oracle_state.compl.get ?_ σ₀
  intro σ x
  exact Quotient.sound ⟨random_oracle_state.get σ,
    (random_oracle_state.set_set σ x (random_oracle_state.get σ)).trans
      (random_oracle_state.get_set σ)⟩

include h_adv in
/-- **Form (b) — `Program.glob` projection.** The joint distribution of
    (adv's bit, what `adv` can see/modify) is identical under lazy and
    eager. Specialisation via `(Program.glob adv).get`. -/
theorem oracle_loop_marginal_lazy_eq_random_oracle_glob (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (Pure.pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (Pure.pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals))) := by
  refine oracle_loop_marginal_lazy_eq_random_oracle adv h_adv
    (Program.glob adv).get ?_ σ₀
  intro σ x
  apply Quotient.sound
  change Relation.EqvGen
      (fun s s' : state => ∃ f ∈ ((adv.range)ᶜ : DetermFootprint state).updates, f s = s')
      (random_oracle_state.set x σ) σ
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  refine ⟨random_oracle_state.set x, ?_, rfl⟩
  have h_in_ro : random_oracle_state.set x ∈ random_oracle_state.range.updates := by
    refine ⟨Function.const _ x, Set.mem_univ _, ?_⟩
    funext σ'
    simp [Lens.liftFunction]
  have hadv_le : adv.range ≤ random_oracle_state.compl.range :=
    sInf_le h_adv
  have h_le : random_oracle_state.range ≤ (adv.range)ᶜ := by
    have hflip : (random_oracle_state.compl.range)ᶜ ≤ (adv.range)ᶜ := by
      change (Submonoid.centralizer random_oracle_state.compl.range.updates).carrier
           ⊆ (Submonoid.centralizer adv.range.updates).carrier
      exact Submonoid.centralizer_le hadv_le
    rwa [DetermFootprint.complement_range, DetermFootprint.compl_compl] at hflip
  exact h_le h_in_ro

end AdvParam
