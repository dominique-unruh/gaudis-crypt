import GaudisCrypt.Lib.RO.ROCouplingEquiv

/-!
# Worked example: the `glob` endpoint on a concrete adversary

This file is a concrete, worked **example** of the EasyCrypt-style relational lazy ≈ eager
endpoint `GaudisCrypt.Lib.RO.Instantiate.prhl_instantiate_of_glob`
(`ROCouplingEquiv.lean`).

We build a concrete adversary procedure `A_ex` that genuinely uses **all three** kinds of
memory the framework distinguishes:

* a **global** program variable `advG : Variable Nat` (read and written),
* a **local** variable (of type `Nat`, read and written), and
* the **oracle hole** (one `RO` query whose result is stored in a second local of type `output`).

The whole point of the endpoint is that the adversary's only assumption is a *checkable*
footprint-disjointness fact `FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ` — "`A` never
touches the oracle table".  We discharge that disjointness completely (no `sorry`, no new
`axiom`), which is the substance of the example: everything `A` touches (`advG`, its locals,
the hole plumbing) is provably disjoint from the random oracle.

The per-query lazy ≈ eager coupling `h` is left as a hypothesis, exactly as in the endpoint's
own statement — it is the framework's separate obligation, not proved standalone here.
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs

/-! ## Generic footprint helpers (chain footprints and their `globalL`-reduction) -/

/-- **A chained lens's footprint is bounded by the outer lift of the inner footprint.**  Each
    generator `diracKer ((L.chain v).liftFunction g)` equals `L.liftSubProbability (diracKer
    (v.liftFunction g))` (`chain_liftFunction_diracKer`), a member of the lifted image. -/
theorem chain_footprint_le_lift {a b c : Type} (L : Lens b c) (v : Lens a b) :
    (L.chain v).footprint ≤ Lens.liftFootprint L (v.footprint) := by
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨g, rfl⟩
  simp only [chain_liftFunction_diracKer]
  unfold Lens.liftFootprint
  rw [Footprint.from_updates]
  refine Set.subset_centralizer_centralizer ⟨diracKer (v.liftFunction g), ?_, rfl⟩
  exact (Footprint.from_le_iff (Set.range fun h : Function.End a => diracKer (v.liftFunction h))
    v.footprint).mp le_rfl ⟨g, rfl⟩

/-- **`fvP_reduce L` of a chained lens's footprint is bounded by the inner lens's footprint.**
    Combine `chain_footprint_le_lift` with `fvP_reduce`'s exact-left-inverse property
    (`FVP.fvP_reduce_extend`).  Needs `[Nonempty c]` for the extend/reduce round trip. -/
theorem reduce_chain_footprint_le {a b c : Type} [Nonempty c] (L : Lens b c) (v : Lens a b) :
    fvP_reduce L ((L.chain v).footprint) ≤ v.footprint := by
  refine le_trans (fvP_reduce_mono L (chain_footprint_le_lift L v)) ?_
  exact le_of_eq (FVP.fvP_reduce_extend L v.footprint)

/-- **The `L`-reduction of a footprint disjoint from `L.chain v` is disjoint from `v`** (the honest
    converse of `reduce_chain_le_compl`).  Each reduced generator `reduceSubProbability L (k, i, o)`
    commutes with every generator `diracKer (v.liftFunction g)` of `v.footprint`: the two Fubini
    identities (`reduceBaseGen_mul_left`/`_right`) turn the goal into commutation of
    `L.liftSubProbability (diracKer (v.liftFunction g))` (= the `L.chain v` generator, by
    `chain_liftFunction_diracKer`) with `k`, which
    `hdisj : R ≤ ((L.chain v).footprint)ᶜ` supplies. -/
theorem reduce_le_compl_of_chain {t s c : Type} (L : Lens s c) (v : Lens t s) {R : Footprint c}
    (hdisj : R ≤ ((L.chain v).footprint)ᶜ) :
    fvP_reduce L R ≤ (v.footprint)ᶜ := by
  -- It suffices that every reduced generator lies in `(v.footprint)ᶜ.updates`.
  rw [fvP_reduce_eq_from]
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨⟨k, i, o⟩, ⟨hk, -, -⟩, rfl⟩
  -- Membership in `(v.footprint)ᶜ.updates = centralizer (v.footprint.updates)`: commute with every
  -- `f ∈ v.footprint.updates`.  As `v.footprint.updates = C(C(v-gens))` and our element lies in
  -- `C(v-gens)`, any such `f` commutes with it.
  show Lens.reduceSubProbability L (k, i, o) ∈ (v.footprint)ᶜ.updates
  rw [Footprint.updates_eq_centralizer_compl (v.footprint)ᶜ, Footprint.compl_compl,
    Submonoid.mem_carrier, Submonoid.mem_centralizer_iff]
  intro f hf
  -- `hf : f ∈ v.footprint.updates = C(C(v-gens))`, so `f` commutes with everything in `C(v-gens)`.
  rw [show v.footprint.updates = Set.centralizer (Set.centralizer
      (Set.range fun g : Function.End t => diracKer (v.liftFunction g))) from by
        rw [show v.footprint = Footprint.from _ from rfl, Footprint.from_updates]] at hf
  refine (hf (Lens.reduceSubProbability L (k, i, o)) ?_).symm
  -- The reduced generator commutes with each `v`-generator, via the two Fubini identities.
  rw [Set.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  have hcomm : L.liftSubProbability (diracKer (v.liftFunction g)) * k
      = k * L.liftSubProbability (diracKer (v.liftFunction g)) := by
    have hgen : diracKer ((L.chain v).liftFunction g) ∈ ((L.chain v).footprint).updates :=
      (Footprint.from_le_iff (Set.range fun h : Function.End t =>
        diracKer ((L.chain v).liftFunction h)) ((L.chain v).footprint)).mp le_rfl ⟨g, rfl⟩
    rw [chain_liftFunction_diracKer] at hgen
    exact ((Submonoid.mem_centralizer_iff.mp (hdisj hk))
      (L.liftSubProbability (diracKer (v.liftFunction g))) hgen)
  rw [reduceBaseGen_mul_left, reduceBaseGen_mul_right, hcomm]

/-- **Two lenses chained through a common outer lens are disjoint when their inner lenses are.**
    The two chained overwrites both go through `L`; commutation reduces to
    `inA.set _ (inB.set _ ·) = inB.set _ (inA.set _ ·)` on the `L`-content, i.e. the inner
    `disjoint inA inB`. -/
instance disjoint_chain_common {m outer a b : Type} (L : Lens m outer) {inA : Lens a m}
    {inB : Lens b m} [hd : disjoint inA inB] :
    disjoint (Lens.chain L inA) (Lens.chain L inB) where
  commute s v w := by
    change L.set (inA.set v (L.get (L.set (inB.set w (L.get s)) s))) (L.set (inB.set w (L.get s)) s)
        = L.set (inB.set w (L.get (L.set (inA.set v (L.get s)) s))) (L.set (inA.set v (L.get s)) s)
    rw [L.set_get, L.set_get, L.set_set, L.set_set, hd.commute]

/-- **A lens chained through `L` is disjoint from one chained through a disjoint outer lens `M`.**
    Each chained overwrite preserves the other outer lens's `get`, so the two commute. -/
instance disjoint_chain_of_disjoint {mL mM outer a b : Type} {L : Lens mL outer} {M : Lens mM outer}
    {inA : Lens a mL} {inB : Lens b mM} [hd : disjoint L M] :
    disjoint (Lens.chain L inA) (Lens.chain M inB) where
  commute s v w := by
    haveI hds : disjoint M L := hd.symm
    change L.set (inA.set v (L.get (M.set (inB.set w (M.get s)) s))) (M.set (inB.set w (M.get s)) s)
        = M.set (inB.set w (M.get (L.set (inA.set v (L.get s)) s))) (L.set (inA.set v (L.get s)) s)
    rw [Lens.get_of_disjoint_set L M _ s, Lens.get_of_disjoint_set M L _ s, hd.commute]

/-- **Reading through a lens (post-composed with any `k`) has footprint bounded by the lens.**  Such
    a getter factors as `ProgramDenotation.get l >>= (pure ∘ k)`, so `footprint_bind_le` bounds it
    by `(get l).footprint ⊔ ⊥ ≤ l.footprint`.  Handles both a raw lens read and the wrapped getter
    that `StmtWithHoles.assign` builds. -/
theorem get_read_footprint_le {a s γ : Type} (l : Lens a s) (k : a → γ) :
    (ProgramDenotation.get (⟨fun st => k (l.get st)⟩ : Getter γ s)).footprint ≤ l.footprint := by
  have hEq : (ProgramDenotation.get (⟨fun st => k (l.get st)⟩ : Getter γ s))
      = ProgramDenotation.get l >>= fun x => (pure (k x) : ProgramDenotation s γ) := by
    funext st
    have hlhs : (ProgramDenotation.get (⟨fun st => k (l.get st)⟩ : Getter γ s)) st
        = pure (k (l.get st), st) := by
      change (pure (st, st) : SubProbability (s × s))
          >>= (fun p : s × s => (pure (k (l.get p.1), p.2) : SubProbability (γ × s)))
        = pure (k (l.get st), st)
      rw [SubProbability.pure_bind]
    rw [hlhs]
    change (pure (k (l.get st), st) : SubProbability (γ × s))
        = ProgramDenotation.get l st >>= fun w : a × s => pure (k w.1, w.2)
    rw [ProgramDenotation.get_apply, SubProbability.pure_bind]
  rw [hEq]
  refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
  · exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_get l)
  · refine iSup_le fun x => ?_
    exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure _ _)

/-! ## The concrete example -/

/-- The example's procedure signature: one `input` parameter, returns a `Nat`. -/
abbrev sigEx : ProcedureSignature := { params := [input], ret := Nat }

/-- The example's locals: a `Nat` scratch local and an `output` local receiving the oracle
    result.  So `localsEx.map (·.fst) = [Nat, output]`. -/
abbrev localsEx : List (Σ t : Type, Inhabited t) := [⟨Nat, inferInstance⟩, ⟨output, inferInstance⟩]

/-- The procedure state of the example. -/
abbrev stateEx : Type := (sigEx).LocalVariableState localsEx

/-- The `Nat` scratch local, viewed inside the procedure state (`.intoVars` at the first
    component of the vars tuple `Nat × output`). -/
def natLocalL : Lens Nat (ProcedureState stateEx) :=
  (Lens.fst : Lens Nat (Nat × output)).intoVars

/-- The `output` local receiving the oracle result (`.intoVars` at the second component). -/
def outLocalL : Lens output (ProcedureState stateEx) :=
  (Lens.snd : Lens output (Nat × output)).intoVars

/-- The `input` parameter, viewed inside the procedure state (`.intoParams`, params tuple is
    `input`). -/
def inParamL : Lens input (ProcedureState stateEx) :=
  (Lens.id (m := input)).intoParams

section

-- The example's global adversary variable (a `Nat` in the program state), assumed disjoint from
-- the random oracle — the *only* structural assumption on the adversary.
variable (advG : Variable Nat) [instDisj : disjoint advG random_oracle_state]

/-- The global variable `advG` viewed inside the procedure state. -/
noncomputable def advGL : Lens Nat (ProcedureState stateEx) :=
  ProcedureState.globalL.chain advG

/-- The example adversary body: copy the global into itself (touches `advG`), copy the `Nat`
    local into itself (touches a local), then query the oracle with the input parameter,
    storing the result in the `output` local (the single oracle hole). -/
noncomputable def bodyEx : StmtWithHoles roHoles stateEx :=
  StmtWithHoles.seq
    (StmtWithHoles.assign (advGL advG).toSetter (advGL advG).toGetter)
    (StmtWithHoles.seq
      (StmtWithHoles.assign natLocalL.toSetter natLocalL.toGetter)
      (StmtWithHoles.hole HoleIndex.zero outLocalL.toSetter inParamL.toGetter))

/-- The example adversary procedure: `bodyEx` with return value the `Nat` scratch local. -/
noncomputable def A_ex : ProcedureWithHoles roHoles sigEx :=
  { locals := localsEx
    body := bodyEx advG
    return_val := natLocalL.toGetter }

/-- The example invariant: the two states agree outside the oracle table.  With this,
    `hrefine`/`hstable` are trivial. -/
def P_ex : state → state → Prop :=
  fun g₁ g₂ => random_oracle_state.compl.get g₁ = random_oracle_state.compl.get g₂

/-! ### Discharging `FVP.fvP_proc A_ex ≤ (random_oracle_state.footprint)ᶜ`

Everything `A_ex` touches — the global `advG`, the two locals, and the input parameter — is a lens
disjoint from `roLift stateEx = globalL.chain random_oracle_state` (`advG` by hypothesis
`instDisj`, the locals/param through the `localL`/`globalL` split).  So the whole syntactic
footprint lands in `((roLift stateEx).footprint)ᶜ`; reducing through `globalL`
(`reduce_le_compl_of_chain`) then lands it in `(random_oracle_state.footprint)ᶜ`. -/

-- Each lens the body touches is disjoint from the oracle-table lens `roLift stateEx`.
include instDisj in
/-- The global adversary lens `advGL` is disjoint from the oracle-table lens `roLift stateEx`. -/
theorem advGL_disj_roLift : disjoint (advGL advG) (roLift stateEx) := by
  unfold advGL roLift
  exact disjoint_chain_common (inA := advG) (inB := random_oracle_state) (hd := instDisj)
    ProcedureState.globalL

theorem natLocalL_disj_roLift : disjoint natLocalL (roLift stateEx) := by
  unfold natLocalL roLift Lens.intoVars; exact disjoint_chain_of_disjoint

theorem outLocalL_disj_roLift : disjoint outLocalL (roLift stateEx) := by
  unfold outLocalL roLift Lens.intoVars; exact disjoint_chain_of_disjoint

theorem inParamL_disj_roLift : disjoint inParamL (roLift stateEx) := by
  unfold inParamL roLift Lens.intoParams; exact disjoint_chain_of_disjoint

/-- A lens read's footprint (raw or `assign`-wrapped) lands in `((roLift stateEx).footprint)ᶜ`. -/
theorem get_lens_le_roLift_compl {γ : Type} (l : Lens γ (ProcedureState stateEx))
    (hd : disjoint l (roLift stateEx)) (k : γ → SubProbability γ) :
    (ProgramDenotation.get (⟨fun st => k (l.get st)⟩ :
        Getter (SubProbability γ) (ProcedureState stateEx))).footprint
      ≤ ((roLift stateEx).footprint)ᶜ :=
  le_trans (get_read_footprint_le l k)
    (@Lens.footprint_le_compl_of_disjoint _ _ _ l (roLift stateEx) hd)

/-- A raw lens read lands in `((roLift stateEx).footprint)ᶜ`. -/
theorem get_le_roLift_compl {γ : Type} (l : Lens γ (ProcedureState stateEx))
    (hd : disjoint l (roLift stateEx)) :
    (ProgramDenotation.get l).footprint ≤ ((roLift stateEx).footprint)ᶜ :=
  le_trans (ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_get l))
    (@Lens.footprint_le_compl_of_disjoint _ _ _ l (roLift stateEx) hd)

/-- A lens write's family footprint lands in `((roLift stateEx).footprint)ᶜ`. -/
theorem set_le_roLift_compl {γ : Type} (l : Lens γ (ProcedureState stateEx))
    (hd : disjoint l (roLift stateEx)) :
    ProgramDenotation.footprint' (ProgramDenotation.set l) ≤ ((roLift stateEx).footprint)ᶜ := by
  refine iSup_le fun x => ?_
  exact le_trans
    (ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_set l x))
    (@Lens.footprint_le_compl_of_disjoint _ _ _ l (roLift stateEx) hd)

/-- The body's syntactic footprint is disjoint from the oracle table. -/
theorem fvP_stmt_bodyEx_le : FVP.fvP_stmt (bodyEx advG) ≤ ((roLift stateEx).footprint)ᶜ := by
  rw [show FVP.fvP_stmt (bodyEx advG) =
      (ProgramDenotation.footprint' (ProgramDenotation.set (advGL advG).toSetter) ⊔
        (ProgramDenotation.get (⟨fun st => pure ((advGL advG).toGetter.get st)⟩ :
          Getter (SubProbability Nat) (ProcedureState stateEx))).footprint) ⊔
      ((ProgramDenotation.footprint' (ProgramDenotation.set natLocalL.toSetter) ⊔
          (ProgramDenotation.get (⟨fun st => pure (natLocalL.toGetter.get st)⟩ :
            Getter (SubProbability Nat) (ProcedureState stateEx))).footprint) ⊔
        (ProgramDenotation.footprint' (ProgramDenotation.set outLocalL.toSetter) ⊔
          (ProgramDenotation.get inParamL.toGetter).footprint))
      from rfl]
  refine sup_le
    (sup_le (set_le_roLift_compl _ (advGL_disj_roLift advG))
      (get_lens_le_roLift_compl _ (advGL_disj_roLift advG) _))
    (sup_le
      (sup_le (set_le_roLift_compl _ natLocalL_disj_roLift)
        (get_lens_le_roLift_compl _ natLocalL_disj_roLift _))
      (sup_le (set_le_roLift_compl _ outLocalL_disj_roLift)
        (get_le_roLift_compl _ inParamL_disj_roLift)))

/-- **The example's footprint disjointness from the random oracle — fully discharged.** -/
theorem hdisj_ex : FVP.fvP_proc (A_ex advG) ≤ (random_oracle_state.footprint)ᶜ := by
  rw [show FVP.fvP_proc (A_ex advG) =
      fvP_reduce ProcedureState.globalL (FVP.fvP_stmt (bodyEx advG)) ⊔
        fvP_reduce ProcedureState.globalL
          ((ProgramDenotation.get (natLocalL.toGetter)).footprint)
      from rfl]
  refine sup_le ?_ ?_
  · exact reduce_le_compl_of_chain ProcedureState.globalL random_oracle_state
      (fvP_stmt_bodyEx_le advG)
  · exact reduce_le_compl_of_chain ProcedureState.globalL random_oracle_state
      (get_le_roLift_compl _ natLocalL_disj_roLift)

/-! ### The example invariant's endpoint premises are trivial

For the agree-outside-oracle invariant `P_ex`, the two `P`-side conditions of the endpoint hold by
`rfl`-level reasoning: `hrefine` *is* the invariant, and `hstable` reads off the target's
outside-oracle equality directly (the oracle-table hypotheses are not even needed). -/

/-- `P_ex` forces agreement on the non-oracle globals — this is literally `P_ex`. -/
theorem hrefine_ex (g₁ g₂ : state) (h : P_ex g₁ g₂) :
    random_oracle_state.compl.get g₁ = random_oracle_state.compl.get g₂ := h

/-- `P_ex` is determined by the oracle table: overwriting the non-oracle globals on both sides,
    while keeping each side's table, preserves it (here directly from the target agreement `hc`). -/
theorem hstable_ex (g₁ g₂ g₁' g₂' : state) (_ : P_ex g₁ g₂)
    (hc : random_oracle_state.compl.get g₁' = random_oracle_state.compl.get g₂')
    (_ : random_oracle_state.get g₁' = random_oracle_state.get g₁)
    (_ : random_oracle_state.get g₂' = random_oracle_state.get g₂) : P_ex g₁' g₂' := hc

/-- **The worked instantiation of `prhl_instantiate_of_glob`.**  For the concrete adversary `A_ex`
    (global `advG`, a `Nat` local, an `output` local for the oracle result, one oracle hole) and the
    agree-outside-oracle invariant `P_ex`, the eager and lazy instantiations couple under `P_ex`,
    given only the per-query lazy ≈ eager coupling `h`.  Every structural hypothesis of the endpoint
    — footprint disjointness (`hdisj_ex`) and the two `P`-side conditions (`hrefine_ex`,
    `hstable_ex`) — is discharged; `h` is a hypothesis, as in the endpoint's own statement. -/
theorem glob_example_instantiation (args : (sigEx).ParamType)
    (h : ∀ inp : input,
      ProgramDenotation.prhl2 P_ex (random_oracle_query inp) (lazy_query inp) (liftPost P_ex)) :
    ProgramDenotation.prhl2 P_ex
      (procedureDenotation ((A_ex advG).instantiate RO_eager) args)
      (procedureDenotation ((A_ex advG).instantiate RO_lazy) args)
      (liftPost P_ex) :=
  prhl_instantiate_of_glob (P := P_ex) (A_ex advG) args (hdisj_ex advG) hrefine_ex hstable_ex h

end

end GaudisCrypt.Lib.RO.Instantiate
