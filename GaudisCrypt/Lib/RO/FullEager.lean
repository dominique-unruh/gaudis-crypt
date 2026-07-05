import GaudisCrypt.Logic.EagerProc
import GaudisCrypt.Lib.RO.GlobTransfer

/-!
# FullEager: the lazy = eager theorem, PROM-style

An independent, EasyCrypt-style derivation of the whole-game lazy = eager
coupling, after the `FullEager` subtheory of EasyCrypt's `PROM.ec`.  The
headline is a chain of pRHL judgments in the eager calculus
(`GaudisCrypt.Logic.EagerRhl` / `EagerProc`):

| PROM.ec (`FullEager`)                   | here                                       |
|-----------------------------------------|--------------------------------------------|
| `resample` (`Iter` over `Unknown`)       | `convert` (one uniform function draw)      |
| `eager_init`, `eager_get` (eager rnd)    | `eager_init`, `eager_query` (native)       |
| `eager_D` (`eager proc` on abstract `D`) | `eager_D` (via the `eager_call` rule)      |
| `D <: FRO_Distinguisher {-FRO}`          | `hdisj : FVP.fvP_proc A ≤ (RO.footprint)ᶜ` |
| `RO_LRO : ={glob D} ==> ={res, glob D}`  | `RO_LRO_glob`                              |

**Dependency policy.**  The per-operation eager lemmas are proven *natively* on
the concrete RO programs — applied-form computations plus the resampling
bijection `uniform_bind_update` (the `eager rnd` content).  The derivation
imports **no** `transfer_*` claims and neither of the transfer-side body
inductions; the only adversary-crossing step is the calculus rule
`eager_call` (`Logic/EagerProc.lean`), whose soundness is the once-and-for-all
induction — the analogue of EasyCrypt's trusted `eager proc`.  The allowed
substrate is the footprint/confinement layer (the module-system analogue of
`{-FRO}`), the applied-form helpers, and the invariant machinery of
`GlobTransfer.lean` (all coupling-native), used for the `={glob A}`
precondition step exactly where EC's kernel threads `={glob D}`.
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs

/-! ## Applied forms of the RO primitives -/

/-- `random_oracle_query` applied: a deterministic table read. -/
lemma random_oracle_query_apply (inp : input) (σ : state) :
    random_oracle_query inp σ
      = (pure ((random_oracle_state.get σ inp).getD default, σ)
          : SubProbability (output × state)) := by
  unfold random_oracle_query
  rw [bind_apply, get_ro_apply, SubProbability.pure_bind]
  rfl

/-- `convert` applied: one uniform draw filling the table's holes. -/
lemma convert_apply (σ : state) :
    convert σ
      = (SubProbability.uniform : SubProbability (input → output)) >>= fun y =>
          (pure ((), random_oracle_state.set
              (fun x => some ((random_oracle_state.get σ x).getD (y x))) σ)
            : SubProbability (Unit × state)) := by
  unfold convert
  rw [bind_apply, get_ro_apply, SubProbability.pure_bind]
  simp only []
  rw [bind_apply, uniform_apply, SubProbability.bind_assoc]
  congr 1; funext y
  rw [SubProbability.pure_bind, set_ro_apply]

/-- `random_oracle_init` applied: one uniform draw of the full table. -/
lemma random_oracle_init_apply (σ : state) :
    random_oracle_init σ
      = (SubProbability.uniform : SubProbability (input → output)) >>= fun h =>
          (pure ((), random_oracle_state.set (fun x => some (h x)) σ)
            : SubProbability (Unit × state)) := by
  unfold random_oracle_init
  rw [bind_apply, uniform_apply, SubProbability.bind_assoc]
  congr 1; funext h
  rw [SubProbability.pure_bind]
  change (ProgramDenotation.set random_oracle_state fun x => some (h x)) σ = _
  rw [set_ro_apply]

/-! ## Uniform-sampling algebra (the `eager rnd` substance) -/

/-- The uniform sub-probability is a probability. -/
lemma uniform_mass {α : Type} [Fintype α] [Nonempty α] :
    (SubProbability.uniform : SubProbability α).1 Set.univ = 1 := by
  letI : MeasurableSpace α := ⊤
  change (PMF.uniformOfFintype α).toMeasure Set.univ = 1
  haveI := @PMF.toMeasure.isProbabilityMeasure α ⊤ (PMF.uniformOfFintype α)
  exact MeasureTheory.IsProbabilityMeasure.measure_univ

/-- A lossless sampling whose value is ignored collapses. -/
lemma SubProbability.bind_const {α β : Type} (ν : SubProbability α)
    (hν : ν.1 Set.univ = 1) (m : SubProbability β) :
    (ν >>= fun _ => m) = m := by
  refine SubProbability.ext_of_expected (fun F => ?_)
  rw [SubProbability.expected_bind]
  change (∫⁻ _, m.expected F ∂ν.1) = m.expected F
  rw [MeasureTheory.lintegral_const, hν, mul_one]

/-- **Resampling one coordinate of a uniform function is uniform** — the
    bijection behind EasyCrypt's `eager rnd`: drawing `v` uniformly and
    overwriting a uniformly drawn `y` at `inp` is a uniform draw. -/
lemma uniform_bind_update (inp : input) :
    ((SubProbability.uniform : SubProbability output) >>= fun v =>
      (SubProbability.uniform : SubProbability (input → output)) >>= fun y =>
        (pure (Function.update y inp v) : SubProbability (input → output)))
    = (SubProbability.uniform : SubProbability (input → output)) := by
  refine SubProbability.ext_of_expected (fun F => ?_)
  simp only [SubProbability.expected_bind, expected_pure, uniform_expected]
  have hO0 : (Fintype.card output : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hOt : (Fintype.card output : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hF0 : (Fintype.card (input → output) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have hFt : (Fintype.card (input → output) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc (∑ v : output, (∑ y : input → output, F (Function.update y inp v) /
              (Fintype.card (input → output) : ENNReal)) /
            (Fintype.card output : ENNReal))
      = (∑ v : output, ∑ y : input → output, F (Function.update y inp v)) /
          ((Fintype.card (input → output) : ENNReal) *
           (Fintype.card output : ENNReal)) := by
        simp_rw [div_eq_mul_inv]
        simp_rw [← Finset.sum_mul]
        rw [mul_assoc]
        congr 1
        exact (ENNReal.mul_inv (Or.inl hF0) (Or.inl hFt)).symm
    _ = ((Fintype.card output : ENNReal) * ∑ z : input → output, F z) /
          ((Fintype.card (input → output) : ENNReal) *
           (Fintype.card output : ENNReal)) := by
        rw [sum_update_eq_card_mul_sum]
    _ = (∑ z : input → output, F z) /
          (Fintype.card (input → output) : ENNReal) := by
        rw [mul_comm (Fintype.card (input → output) : ENNReal)
                     (Fintype.card output : ENNReal)]
        exact ENNReal.mul_div_mul_left _ _ hO0 hOt
    _ = ∑ z : input → output, F z / (Fintype.card (input → output) : ENNReal) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]

/-! ## Per-operation eager lemmas (PROM's `eager_init`, `eager_get`) -/

/-- **Eager init** (native): `convert; random_oracle_init ~ lazy_init; convert`
    — both sides are "sample a full fresh table over `σ`". -/
theorem eager_init :
    ProgramDenotation.eagerR convert convert (fun σ₁ σ₂ : state => σ₁ = σ₂)
      random_oracle_init lazy_init (fun u v : Unit × state => u = v) := by
  refine ProgramDenotation.eagerR_of_eq ?_
  funext σ
  have hL : (convert >>= fun _ => random_oracle_init) σ
      = (SubProbability.uniform : SubProbability (input → output)) >>= fun h =>
          pure ((), random_oracle_state.set (fun x => some (h x)) σ) := by
    rw [bind_apply, convert_apply, SubProbability.bind_assoc]
    have hinner : ∀ y : input → output,
        ((pure ((), random_oracle_state.set
            (fun x => some ((random_oracle_state.get σ x).getD (y x))) σ)
          : SubProbability (Unit × state)) >>= fun a => random_oracle_init a.2)
        = (SubProbability.uniform : SubProbability (input → output)) >>= fun h =>
            pure ((), random_oracle_state.set (fun x => some (h x)) σ) := by
      intro y
      rw [SubProbability.pure_bind]
      change random_oracle_init (random_oracle_state.set _ σ) = _
      rw [random_oracle_init_apply]
      congr 1; funext h
      rw [random_oracle_state.set_set]
    simp only [hinner]
    exact SubProbability.bind_const _ uniform_mass _
  have hR : (lazy_init >>= fun u => convert >>= fun _ => pure u) σ
      = (SubProbability.uniform : SubProbability (input → output)) >>= fun h =>
          pure ((), random_oracle_state.set (fun x => some (h x)) σ) := by
    rw [bind_apply, lazy_init_apply, SubProbability.pure_bind]
    change (convert >>= fun _ => pure ()) (random_oracle_state.set _ σ) = _
    rw [bind_apply, convert_apply, SubProbability.bind_assoc]
    congr 1; funext y
    rw [SubProbability.pure_bind]
    change (pure ((), random_oracle_state.set _ (random_oracle_state.set _ σ))
        : SubProbability (Unit × state)) = _
    simp only [random_oracle_state.set_get, Option.getD_none, random_oracle_state.set_set]
  exact hL.trans hR.symm

/-- **Eager query** (native): `convert; random_oracle_query x ~ lazy_query x; convert`.
    Cache hit: both sides read the shared cached value around the same fill.
    Cache miss: the fresh lazy sample and the fill coordinate are exchanged by
    the resampling bijection (`uniform_bind_update`). -/
theorem eager_query (x : input) :
    ProgramDenotation.eagerR convert convert (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (random_oracle_query x) (lazy_query x)
      (fun u v : output × state => u = v) := by
  refine ProgramDenotation.eagerR_of_eq ?_
  funext σ
  have hLshape : (convert >>= fun _ => random_oracle_query x) σ
      = (SubProbability.uniform : SubProbability (input → output)) >>= fun y =>
          pure (((fun x' => some ((random_oracle_state.get σ x').getD (y x'))) x).getD default,
            random_oracle_state.set
              (fun x' => some ((random_oracle_state.get σ x').getD (y x'))) σ) := by
    rw [bind_apply, convert_apply, SubProbability.bind_assoc]
    congr 1; funext y
    rw [SubProbability.pure_bind]
    change random_oracle_query x (random_oracle_state.set _ σ) = _
    rw [random_oracle_query_apply, random_oracle_state.set_get]
  cases hc : random_oracle_state.get σ x with
  | some x₀ =>
      -- hit: both sides return the cached value around the same fill
      have hL : (convert >>= fun _ => random_oracle_query x) σ
          = (SubProbability.uniform : SubProbability (input → output)) >>= fun y =>
              pure (x₀, random_oracle_state.set
                (fun x' => some ((random_oracle_state.get σ x').getD (y x'))) σ) := by
        rw [hLshape]
        congr 1; funext y
        simp only [hc, Option.getD_some]
      have hR : (lazy_query x >>= fun v => convert >>= fun _ => pure v) σ
          = (SubProbability.uniform : SubProbability (input → output)) >>= fun y =>
              pure (x₀, random_oracle_state.set
                (fun x' => some ((random_oracle_state.get σ x').getD (y x'))) σ) := by
        rw [bind_apply, lazy_query_apply_hit x hc, SubProbability.pure_bind]
        change (convert >>= fun _ => pure x₀) σ = _
        rw [bind_apply, convert_apply, SubProbability.bind_assoc]
        congr 1; funext y
        rw [SubProbability.pure_bind]
        rfl
      exact hL.trans hR.symm
  | none =>
      -- miss: exchange the fresh sample and the fill coordinate
      have hL : (convert >>= fun _ => random_oracle_query x) σ
          = (SubProbability.uniform : SubProbability (input → output)) >>= fun z =>
              pure (z x, random_oracle_state.set
                (fun x' => some ((random_oracle_state.get σ x').getD (z x'))) σ) := by
        rw [hLshape]
        congr 1; funext z
        simp only [hc, Option.getD_none, Option.getD_some]
      have hR : (lazy_query x >>= fun v => convert >>= fun _ => pure v) σ
          = ((SubProbability.uniform : SubProbability output) >>= fun v =>
              (SubProbability.uniform : SubProbability (input → output)) >>= fun y =>
                (pure (Function.update y x v) : SubProbability (input → output)))
            >>= fun z =>
              pure (z x, random_oracle_state.set
                (fun x' => some ((random_oracle_state.get σ x').getD (z x'))) σ) := by
        rw [bind_apply, lazy_query_apply_miss x hc, SubProbability.bind_assoc]
        rw [SubProbability.bind_assoc]
        congr 1; funext v
        rw [SubProbability.pure_bind, SubProbability.bind_assoc]
        change (convert >>= fun _ => pure v) (random_oracle_state.set _ σ) = _
        rw [bind_apply, convert_apply, SubProbability.bind_assoc]
        congr 1; funext y
        rw [SubProbability.pure_bind, SubProbability.pure_bind]
        change (pure (v, random_oracle_state.set _ (random_oracle_state.set _ σ))
            : SubProbability (output × state)) = _
        rw [random_oracle_state.set_set]
        -- align value and table with the updated function
        have hval : v = Function.update y x v x := (Function.update_self x v y).symm
        have htab : (fun x' => some ((random_oracle_state.get
              (random_oracle_state.set
                (fun x'' => if x'' = x then some v else random_oracle_state.get σ x'') σ)
              x').getD (y x')))
            = (fun x' => some ((random_oracle_state.get σ x').getD
                (Function.update y x v x'))) := by
          funext x'
          rw [random_oracle_state.set_get]
          by_cases hx' : x' = x
          · subst hx'
            simp only [hc, Option.getD_none, Function.update_self, if_true,
              Option.getD_some]
          · simp only [if_neg hx', Function.update_of_ne hx']
        rw [htab]
        rw [show (v, random_oracle_state.set (fun x' =>
              some ((random_oracle_state.get σ x').getD (Function.update y x v x'))) σ)
            = (Function.update y x v x, random_oracle_state.set (fun x' =>
              some ((random_oracle_state.get σ x').getD (Function.update y x v x'))) σ) from by
          rw [Function.update_self]]
      rw [hL, hR, uniform_bind_update]

/-! ## Kernel instantiation (PROM's `eager_D`) -/

/-- `Loc` (the footprint-discharged locality) is swap-locality for the lifted
    `convert` block. -/
theorem swapLoc_of_loc {holes : HoleSigs} {l : Type} :
    ∀ (A : StmtWithHoles holes l), Loc A →
      SwapLoc (ProgramDenotation.zoom ProcedureState.globalL convert) A
  | .skip, _ => trivial
  | .sample _ _, h => h
  | .call' _ _ _ _ _, h => h
  | .hole _ _ _, h => ⟨h.1, h.2⟩
  | .seq s1 s2, h => ⟨swapLoc_of_loc s1 h.1, swapLoc_of_loc s2 h.2⟩
  | .ifThenElse _ t e, h =>
      ⟨h.1, swapLoc_of_loc t h.2.1, swapLoc_of_loc e h.2.2⟩
  | .«while» _ t, h => ⟨h.1, swapLoc_of_loc t h.2⟩

/-- **`eager_D`**: the abstract adversary is eager for the resampler, from
    footprint disjointness alone — one application of the `eager_call` rule,
    with the per-hole case discharged by the native `eager_query`. -/
theorem eager_D {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.eagerR convert convert (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (procedureDenotation (A.instantiate RO_eager) args)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (fun u v : sig.ret × state => u = v) := by
  have hdisj' := fvP_proc_le_roLift_compl A hdisj
  refine eager_call RO_eager RO_lazy A args convert ?_ ?_ ?_
  · exact swapLoc_of_loc A.body
      (confinedP_loc (fvP_proc A) hdisj' roHole_paramType_countable A.body
        (confinedP_of_fv (fvP_proc A) roHole_paramType_countable A.body
          (fvP_stmt_body_le_fvP_proc A)))
  · exact stable_of_confinedP_footprint (fvP_proc A) hdisj'
      (get_confinedP_of_fv A.return_val (get_return_val_le_fvP_proc A))
  · intro sig' n x p hp hx
    cases n with
    | zero =>
        change ProgramDenotation.eagerR
            (ProgramDenotation.zoom ProcedureState.globalL convert)
            (ProgramDenotation.zoom ProcedureState.globalL convert)
            (fun σ₁ σ₂ => σ₁ = σ₂)
            (programDenotation (StmtWithHoles.call x RO_eager_proc p))
            (programDenotation (StmtWithHoles.call x RO_lazy_proc p))
            (fun u v => u = v)
        rw [denote_call, denote_call]
        refine ProgramDenotation.eagerR_seq (eagerR_self_of_transferBy hp) (fun args' => ?_)
        refine ProgramDenotation.eagerR_seq ?_ (fun ret => eagerR_self_of_transferBy (hx ret))
        rw [procDenotation_RO_eager, procDenotation_RO_lazy]
        exact ProgramDenotation.eagerR_zoom ProcedureState.globalL (eager_query args')
    | succ m => nomatch m

/-- The resampler is swallowed by the eager initialisation (native). -/
lemma convert_init_absorb {α : Type} (rest : ProgramDenotation state α) :
    (convert >>= fun _ : Unit => random_oracle_init >>= fun _ : Unit => rest)
      = (random_oracle_init >>= fun _ : Unit => rest) := by
  funext σ
  rw [bind_apply, convert_apply, SubProbability.bind_assoc]
  have hinner : ∀ y : input → output,
      ((pure ((), random_oracle_state.set
          (fun x => some ((random_oracle_state.get σ x).getD (y x))) σ)
        : SubProbability (Unit × state)) >>= fun a =>
          (random_oracle_init >>= fun _ : Unit => rest) a.2)
      = (random_oracle_init >>= fun _ : Unit => rest) σ := by
    intro y
    rw [SubProbability.pure_bind]
    change (random_oracle_init >>= fun _ : Unit => rest) (random_oracle_state.set _ σ) = _
    simp only [bind_apply, random_oracle_init_apply, SubProbability.bind_assoc,
      SubProbability.pure_bind, random_oracle_state.set_set]
  simp only [hinner]
  exact SubProbability.bind_const _ uniform_mass _

/-! ## The headline (PROM's `RO_LRO`) -/

/-- **`RO_LRO` with `={glob A}`**: the whole lazy and eager games couple from
    `={glob A}` initial states with equal results and `={glob A}` final states —
    a chain of pRHL judgments:

    1. the whole-game eager judgment: `eagerR_seq eager_init eager_D`;
    2. the leading resampler is swallowed by the eager initialisation
       (`convert_init_absorb`);
    3. the trailing resampler is absorbed into a direct coupling recording
       `={glob A}` on the finals (`prhl2_of_lossless_tail_proj`);
    4. the precondition relaxes to `={glob A}` by `prhl2.trans` with the
       same-program self-coupling and `conseq` (the invariant threading EC's
       kernel performs inside `eager proc`). -/
theorem RO_LRO_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => u.1 = v.1 ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) := by
  -- 1. the whole-game eager judgment
  have hgame := ProgramDenotation.eagerR_seq eager_init (fun _ => eager_D A args hdisj)
  -- 2. + 3. absorb the resampler on both ends
  have hE' : ((lazy_init >>= fun _ => procedureDenotation (A.instantiate RO_lazy) args)
        >>= fun a => convert >>= fun _ => pure a)
      = (random_oracle_init >>= fun _ =>
          procedureDenotation (A.instantiate RO_eager) args) :=
    (ProgramDenotation.eagerR_to_eq hgame).symm.trans (convert_init_absorb _)
  have hproduce := ProgramDenotation.prhl2_of_lossless_tail_proj (FVP.glob A).get
    convert_lossless
    (convert_satisfies_of_ro_invariant (FVP.glob A).get (glob_ro_set_invariant A hdisj))
    hE'
  -- 4. relax the precondition to `={glob A}`
  have h12 := ProgramDenotation.prhl2.trans
    (glob_self_coupling_lazy A args hdisj) hproduce
  refine h12.conseq (fun σ₁ σ₃ h => ⟨σ₃, h, rfl⟩) ?_
  rintro u v ⟨w, hw1, hw2⟩
  exact ⟨hw1.1.trans hw2.1, hw1.2.trans hw2.2⟩

/-- `Win`-form of `RO_LRO_glob`: any event decided by `A`'s output transfers
    between the lazy and eager games, with `={glob A}` throughout. -/
theorem RO_LRO_win {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (Win : sig.ret → Prop)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => (Win u.1 ↔ Win v.1) ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) :=
  (RO_LRO_glob A args hdisj).conseq
    (fun _ _ h => h) (fun _ _ h => ⟨by rw [h.1], h.2⟩)

end GaudisCrypt.Lib.RO.Instantiate
