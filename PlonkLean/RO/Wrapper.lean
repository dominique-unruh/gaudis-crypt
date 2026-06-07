import PlonkLean.RO.Basic

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
Proof sketch of `oracle_loop_lazy_convert_eq_random_oracle_loop`:
The sequence of calls of `oracle_loop lazy_init lazy_query` must look something like

1. `lazy_init; adv; lazy_query; ... adv; lazy_query`

This is equivalent (up to `random_oracle_state`) to

2. `lazy_init; adv; lazy_query; ... adv; lazy_query; convert`

Using `adv_conv_eq_conv_adv` we can convert last two calls into `eager_query` and get

3. `lazy_init; adv; lazy_query; ...  lazy_query ;adv; convert; eager_query`

Using `lazy_query_conv_eq_conv_random_oracle` move `convert` to the front

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
theorem oracle_loop_lazy_convert_eq_random_oracle_loop :
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
  -- Step 3: regroup `lazy_init >>= _ => convert` and apply lazy_init_convert_eq_random_oracle_init.
  rw [show (∀ (L : Program state Unit) (K : Program state Bool),
        (L >>= fun _ => convert >>= fun _ => K) = ((L >>= fun _ => convert) >>= fun _ => K))
        from fun L K => (Program.bind_assoc _ _ _).symm]
  rw [show (lazy_init >>= fun _ => convert) = random_oracle_init from lazy_init_convert_eq_random_oracle_init]

include h_adv in
/-- `oracle_loop_wp_lazy_eq_random_oracle`: the lazy and eager oracle loops agree on every postcondition that is
    invariant under writes to `random_oracle_state` (i.e., every postcondition that only
    depends on the *non-RO* part of state).

    Intuitively: an adversary that observes only its own global variables (none of which
    are the random oracle's internal state) cannot tell lazy from eager. -/
theorem oracle_loop_wp_lazy_eq_random_oracle (F : Bool × state → ENNReal)
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
  have h4_wp := congr_arg (fun prog : Program state Bool => prog.wp F) (oracle_loop_lazy_convert_eq_random_oracle_loop adv h_adv)
  simp only at h4_wp
  rw [wp_bind] at h4_wp
  have h_eq : (fun (bσ : Bool × state) =>
                  (convert >>= fun _ : Unit => (pure bσ.1 : Program state Bool)).wp F bσ.2)
            = (fun (bσ : Bool × state) => F (bσ.1, bσ.2)) := by
    funext bσ; exact h_convert bσ.1 bσ.2
  rw [h_eq] at h4_wp
  exact h4_wp

include h_adv in
/-- **SubProb-level form of `oracle_loop_wp_lazy_eq_random_oracle`**: for any projection `h : state → β` of
    state that is invariant under writes to `random_oracle_state` (i.e., `h` only
    sees the *non-RO* part of state), the lazy and eager oracle loops produce the
    same distribution over `Bool × β`.

    This is the "lazy oracle is indistinguishable from eager oracle by the
    adversary's observable variables" statement: an adversary that observes only
    `h σ` (which doesn't depend on the RO's internal state) sees identical
    distributions in both worlds. -/
theorem oracle_loop_marginal_lazy_eq_random_oracle {β : Type} (h : state → β)
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
  exact congr_fun (oracle_loop_wp_lazy_eq_random_oracle adv h_adv
      (fun bσ : Bool × state =>
        (@MeasureTheory.Measure.dirac (Bool × β) ⊤ (bσ.1, h bσ.2)) A)
      (by intros b σ x; simp only; rw [h_inv])) σ₀

include h_adv in
/-- **Form (a) of `oracle_loop_wp_lazy_eq_random_oracle` — lens-complement projection**.

    The joint distribution of (adv's bit, the entire non-RO part of state) is
    identical under lazy and eager RO.

    `random_oracle_state.compl.get` is the lens-complement getter: it returns
    the equivalence class of σ modulo "differs only in RO content". This is
    the most concrete glob-style form — the returned type is a `Quotient` of
    state by the RO-equivalence, with no `Program.range` machinery involved. -/
theorem oracle_loop_marginal_lazy_eq_random_oracle_compl (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, random_oracle_state.compl.get bσ.2) :
            SubProbability (Bool × Quotient random_oracle_state.equal_outside_setoid))) := by
  refine oracle_loop_marginal_lazy_eq_random_oracle adv h_adv random_oracle_state.compl.get ?_ σ₀
  intro σ x
  exact Quotient.sound ⟨random_oracle_state.get σ,
    (random_oracle_state.set_set σ x (random_oracle_state.get σ)).trans
      (random_oracle_state.get_set σ)⟩

include h_adv in
/-- **Form (c) of `oracle_loop_wp_lazy_eq_random_oracle` — `Program.glob adv`**.

    The joint distribution of (adv's bit, what `adv` can see/modify) is
    identical under lazy and eager RO.

    This is the natural cryptographic indistinguishability statement:
    `(Program.glob adv).get bσ.2` is the equivalence class of `bσ.2` under
    `(adv.range)ᶜ`-orbits — i.e., "everything adv could possibly observe or
    affect", quotiented by symmetries outside adv's reach.

    Corollary of `oracle_loop_marginal_lazy_eq_random_oracle` applied to `(Program.glob adv).get`. The
    RO-invariance of this projection follows from `h_adv` via
    the inclusion `random_oracle_state.range ≤ (adv.range)ᶜ`. -/
theorem oracle_loop_marginal_lazy_eq_random_oracle_glob (σ₀ : state) :
    (oracle_loop adv lazy_init lazy_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals)))
    =
    (oracle_loop adv random_oracle_init random_oracle_query σ₀ >>=
        fun bσ : Bool × state =>
          (pure (bσ.1, (Program.glob adv).get bσ.2) :
            SubProbability (Bool × adv.Globals))) := by
  refine oracle_loop_marginal_lazy_eq_random_oracle adv h_adv (Program.glob adv).get ?_ σ₀
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
