import GaudisCrypt.Lib.RO.ROCouplingEquiv
import GaudisCrypt.Lib.RO.TransferInstantiate
import GaudisCrypt.CounterExamples.IndistinguishableVsGlob

/-!
# Worked example: the `glob` endpoint on a concrete adversary

This file is a concrete, worked **example** of the EasyCrypt-style relational lazy ≈ eager
endpoint `GaudisCrypt.Lib.RO.Instantiate.prhl_instantiate_of_glob`
(`ROCouplingEquiv.lean`).

We build a concrete adversary procedure `A_ex` that genuinely uses **all three** kinds of
memory the framework distinguishes:

* a **global** program variable `advG : Variable Nat` (read and written),
* a **local** variable (of type `Nat`, read and written), and
* the **oracle holes** — `A_ex` queries the oracle at each of its two inputs `a`, `b` and stores
  the two answers in two `output` locals `r_a`, `r_b`, which it then returns.

The whole point of the endpoint is that the adversary's only assumption is a *checkable*
footprint-disjointness fact `FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ` — "`A` never
touches the oracle table".  We discharge that disjointness completely (no `sorry`, no new
`axiom`), which is the substance of the example: everything `A` touches (`advG`, its locals,
the hole plumbing) is provably disjoint from the random oracle.

The per-query lazy ≈ eager coupling `h` is left as a hypothesis, exactly as in the endpoint's
own statement — it is the framework's separate obligation, not proved standalone here.

## What the example concludes: a *correct* collision transfer

The invariant `P_ex` is the **genuine** lazy ≈ eager relation between the eager state `g₁` (full,
pre-sampled random function) and the lazy state `g₂` (partial, filled on demand): they agree
outside the oracle, the eager table is total, and the lazy table is a subset of the eager one.
This is what makes the per-query coupling `h` a *real, satisfiable* obligation.

The collision is stated on `A_ex`'s **output** — its two observed answers — and transferred by the
coupling's **result-equality**: `A_ex` found a collision (two distinct queried inputs with equal
answers) against the eager (real) oracle **iff** it did against the lazy one.

⚠ **Why not a table-level `Collides(g₁) ↔ Collides(g₂)` invariant?**  Because it is *false*: the
eager table is a total function `input → output`, which collides by construction (pigeonhole) while
the partial lazy table usually does not.  An `h` forcing `Collides(eager) ↔ Collides(lazy)` would be
unsatisfiable, making the whole theorem vacuous.  Putting the collision on the output and using the
real invariant fixes this.
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs

/-! ## Generic footprint helpers (chain footprints and their `globalL`-reduction) -/

/-- **A chained lens's footprint is bounded by the outer lift of the inner footprint.**  Each
    generator `(L.chain v).liftSubProbability κ` equals `L.liftSubProbability
    (v.liftSubProbability κ)` (`Lens.liftSubProbability_chain`), a member of the lifted image. -/
theorem chain_footprint_le_lift {a b c : Type} (L : Lens b c) (v : Lens a b) :
    (L.chain v).footprint ≤ Lens.liftFootprint L (v.footprint) := by
  refine (Footprint.from_le_iff _ _).mpr ?_
  rintro _ ⟨g, rfl⟩
  rw [Lens.liftSubProbability_chain]
  unfold Lens.liftFootprint
  rw [Footprint.from_updates]
  exact Set.subset_centralizer_centralizer
    ⟨v.liftSubProbability g, Mlocalized_in_footprint v g, rfl⟩

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
      (Set.range v.liftSubProbability)) from by
        rw [Lens.footprint, Footprint.from_updates]] at hf
  refine (hf (Lens.reduceSubProbability L (k, i, o)) ?_).symm
  -- The reduced generator commutes with each `v`-generator, via the two Fubini identities.
  rw [Set.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  have hcomm : L.liftSubProbability (v.liftSubProbability g) * k
      = k * L.liftSubProbability (v.liftSubProbability g) := by
    have hgen : (L.chain v).liftSubProbability g ∈ ((L.chain v).footprint).updates :=
      Mlocalized_in_footprint (L.chain v) g
    rw [Lens.liftSubProbability_chain] at hgen
    exact ((Submonoid.mem_centralizer_iff.mp (hdisj hk))
      (L.liftSubProbability (v.liftSubProbability g)) hgen)
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

/-- The example's procedure signature: **two** `input` parameters `a`, `b`, returning the **pair
    of oracle answers** `output × output` that `A_ex` observed for them.  The return being the two
    answers is the crux: the collision statement is read off the *result*, not off the table. -/
abbrev sigEx : ProcedureSignature := { params := [input, input], ret := output × output }

/-- The example's locals: a `Nat` scratch local and **two** `output` locals `r_a`, `r_b` receiving
    the two oracle answers.  So `localsEx.map (·.fst) = [Nat, output, output]`. -/
abbrev localsEx : List (Σ t : Type, Inhabited t) :=
  [⟨Nat, inferInstance⟩, ⟨output, inferInstance⟩, ⟨output, inferInstance⟩]

/-- The procedure state of the example. -/
abbrev stateEx : Type := (sigEx).LocalVariableState localsEx

/-- The `Nat` scratch local, viewed inside the procedure state (`.intoVars` at the first
    component of the vars tuple `Nat × (output × output)`). -/
def natLocalL : Lens Nat (ProcedureState stateEx) :=
  (Lens.fst : Lens Nat (Nat × output × output)).intoVars

/-- The first answer local `r_a` (`.intoVars` at the second-then-first component of
    `Nat × (output × output)`). -/
def raLocalL : Lens output (ProcedureState stateEx) :=
  ((Lens.snd : Lens (output × output) (Nat × output × output)).chain
    (Lens.fst : Lens output (output × output))).intoVars

/-- The second answer local `r_b` (`.intoVars` at the second-then-second component). -/
def rbLocalL : Lens output (ProcedureState stateEx) :=
  ((Lens.snd : Lens (output × output) (Nat × output × output)).chain
    (Lens.snd : Lens output (output × output))).intoVars

/-- The first `input` parameter `a`, viewed inside the procedure state (`.intoParams`, params tuple
    is `input × input`, so `Lens.fst`). -/
def aParamL : Lens input (ProcedureState stateEx) :=
  (Lens.fst : Lens input (input × input)).intoParams

/-- The second `input` parameter `b` (`.intoParams`, `Lens.snd`). -/
def bParamL : Lens input (ProcedureState stateEx) :=
  (Lens.snd : Lens input (input × input)).intoParams

/-- The return getter: read back the pair of observed answers `(r_a, r_b)`. -/
def retExG : Getter (output × output) (ProcedureState stateEx) :=
  ⟨fun ps => (raLocalL.get ps, rbLocalL.get ps)⟩

section

-- The example's global adversary variable (a `Nat` in the program state), assumed disjoint from
-- the random oracle — the *only* structural assumption on the adversary.
variable (advG : Variable Nat) [instDisj : disjoint advG random_oracle_state]

/-- The global variable `advG` viewed inside the procedure state. -/
noncomputable def advGL : Lens Nat (ProcedureState stateEx) :=
  ProcedureState.globalL.chain advG

/-- The example adversary body.  It exercises **global + local + oracle** memory:
    copy the global into itself (touches `advG`), query the oracle at parameter `a` storing the
    answer in local `r_a` (first oracle hole), query at `b` storing in `r_b` (second oracle hole),
    then read the global into the `Nat` scratch local (touches both a local and `advG`). -/
noncomputable def bodyEx : StmtWithHoles roHoles stateEx :=
  StmtWithHoles.seq
    (StmtWithHoles.assign (advGL advG).toSetter (advGL advG).toGetter)
    (StmtWithHoles.seq
      (StmtWithHoles.hole HoleIndex.zero raLocalL.toSetter aParamL.toGetter)
      (StmtWithHoles.seq
        (StmtWithHoles.hole HoleIndex.zero rbLocalL.toSetter bParamL.toGetter)
        (StmtWithHoles.assign natLocalL.toSetter (advGL advG).toGetter)))

/-- The example adversary procedure: `bodyEx` returning the observed answer pair `(r_a, r_b)`. -/
noncomputable def A_ex : ProcedureWithHoles roHoles sigEx :=
  { locals := localsEx
    body := bodyEx advG
    return_val := retExG }

/-- **The genuine lazy ≈ eager invariant.**  `P_ex g₁ g₂` relates the **eager** state `g₁` (whose
    oracle table is the full pre-sampled random function) to the **lazy** state `g₂` (whose oracle
    table is partial, filled on demand):

    1. they **agree outside the oracle** (`random_oracle_state.compl`);
    2. the eager table is **total** (every input has a defined answer — it was pre-sampled); and
    3. the lazy table is a **subset** of the eager one (every cached lazy answer matches eager).

    Conjuncts 2–3 are exactly the honest coupling of the eager and lazy oracles: after any query the
    eager side already knows the answer and the lazy side agrees wherever it has committed.  This is
    what makes the per-query hypothesis `h` (relating `random_oracle_query inp` to `lazy_query inp`)
    a *real, satisfiable* obligation.

    **Why a table-level collision invariant would be wrong** (the old, vacuous version): the eager
    table is a *total* function `input → output` and hence collides by construction whenever
    `card input > card output` (pigeonhole), while the partial lazy table usually does not — so
    `Collides(eager) ↔ Collides(lazy)` is false and any `h` forcing it is unsatisfiable. -/
def P_ex : state → state → Prop :=
  fun g₁ g₂ =>
    random_oracle_state.compl.get g₁ = random_oracle_state.compl.get g₂
    ∧ (∀ inp, (random_oracle_state.get g₁ inp).isSome)
    ∧ (∀ inp v, random_oracle_state.get g₂ inp = some v →
                random_oracle_state.get g₁ inp = some v)

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

theorem raLocalL_disj_roLift : disjoint raLocalL (roLift stateEx) := by
  unfold raLocalL roLift Lens.intoVars; exact disjoint_chain_of_disjoint

theorem rbLocalL_disj_roLift : disjoint rbLocalL (roLift stateEx) := by
  unfold rbLocalL roLift Lens.intoVars; exact disjoint_chain_of_disjoint

theorem aParamL_disj_roLift : disjoint aParamL (roLift stateEx) := by
  unfold aParamL roLift Lens.intoParams; exact disjoint_chain_of_disjoint

theorem bParamL_disj_roLift : disjoint bParamL (roLift stateEx) := by
  unfold bParamL roLift Lens.intoParams; exact disjoint_chain_of_disjoint

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

/-- The body's syntactic footprint is disjoint from the oracle table.  Two oracle holes just add one
    more `set/get` `sup` summand of the same shape as the single-hole case. -/
theorem fvP_stmt_bodyEx_le : FVP.fvP_stmt (bodyEx advG) ≤ ((roLift stateEx).footprint)ᶜ := by
  rw [show FVP.fvP_stmt (bodyEx advG) =
      (ProgramDenotation.footprint' (ProgramDenotation.set (advGL advG).toSetter) ⊔
        (ProgramDenotation.get (⟨fun st => pure ((advGL advG).toGetter.get st)⟩ :
          Getter (SubProbability Nat) (ProcedureState stateEx))).footprint) ⊔
      ((ProgramDenotation.footprint' (ProgramDenotation.set raLocalL.toSetter) ⊔
          (ProgramDenotation.get aParamL.toGetter).footprint) ⊔
        ((ProgramDenotation.footprint' (ProgramDenotation.set rbLocalL.toSetter) ⊔
            (ProgramDenotation.get bParamL.toGetter).footprint) ⊔
          (ProgramDenotation.footprint' (ProgramDenotation.set natLocalL.toSetter) ⊔
            (ProgramDenotation.get (⟨fun st => pure ((advGL advG).toGetter.get st)⟩ :
              Getter (SubProbability Nat) (ProcedureState stateEx))).footprint)))
      from rfl]
  refine sup_le
    (sup_le (set_le_roLift_compl _ (advGL_disj_roLift advG))
      (get_lens_le_roLift_compl _ (advGL_disj_roLift advG) _))
    (sup_le
      (sup_le (set_le_roLift_compl _ raLocalL_disj_roLift)
        (get_le_roLift_compl _ aParamL_disj_roLift))
      (sup_le
        (sup_le (set_le_roLift_compl _ rbLocalL_disj_roLift)
          (get_le_roLift_compl _ bParamL_disj_roLift))
        (sup_le (set_le_roLift_compl _ natLocalL_disj_roLift)
          (get_lens_le_roLift_compl _ (advGL_disj_roLift advG) _))))

/-- The return getter `retExG` (reading the two answer locals `r_a`, `r_b`) has footprint in
    `((roLift stateEx).footprint)ᶜ`.  It factors as `get raLocalL >>= get rbLocalL >>= pure ∘ pair`,
    so `footprint_bind_le` bounds it by `raLocalL.footprint ⊔ rbLocalL.footprint ⊔ ⊥`, both disjoint
    from the oracle. -/
theorem retExG_le_roLift_compl :
    (ProgramDenotation.get retExG).footprint ≤ ((roLift stateEx).footprint)ᶜ := by
  have hEq : (ProgramDenotation.get retExG)
      = ProgramDenotation.get raLocalL >>= fun a =>
          ProgramDenotation.get rbLocalL >>= fun b =>
            (pure (a, b) : ProgramDenotation (ProcedureState stateEx) (output × output)) := by
    funext st
    have hlhs : (ProgramDenotation.get retExG) st
        = pure ((raLocalL.get st, rbLocalL.get st), st) := by
      change (pure (st, st) : SubProbability (ProcedureState stateEx × ProcedureState stateEx))
          >>= (fun p => (pure (retExG.get p.1, p.2)
            : SubProbability ((output × output) × ProcedureState stateEx)))
        = pure ((raLocalL.get st, rbLocalL.get st), st)
      rw [SubProbability.pure_bind]; rfl
    rw [hlhs]
    change _ = ProgramDenotation.get raLocalL st >>= fun w : output × ProcedureState stateEx =>
      (ProgramDenotation.get rbLocalL w.2 >>= fun w' : output × ProcedureState stateEx =>
        pure ((w.1, w'.1), w'.2))
    rw [ProgramDenotation.get_apply, SubProbability.pure_bind, ProgramDenotation.get_apply,
      SubProbability.pure_bind]
  rw [hEq]
  refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
  · exact get_le_roLift_compl _ raLocalL_disj_roLift
  · refine iSup_le fun a => ?_
    refine le_trans (ProgramDenotation.footprint_bind_le _ _) (sup_le ?_ ?_)
    · exact get_le_roLift_compl _ rbLocalL_disj_roLift
    · refine iSup_le fun b => ?_
      exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure _ _)

/-- **The example's footprint disjointness from the random oracle — fully discharged.** -/
theorem hdisj_ex : FVP.fvP_proc (A_ex advG) ≤ (random_oracle_state.footprint)ᶜ := by
  rw [show FVP.fvP_proc (A_ex advG) =
      fvP_reduce ProcedureState.globalL (FVP.fvP_stmt (bodyEx advG)) ⊔
        fvP_reduce ProcedureState.globalL
          ((ProgramDenotation.get retExG).footprint)
      from rfl]
  refine sup_le ?_ ?_
  · exact reduce_le_compl_of_chain ProcedureState.globalL random_oracle_state
      (fvP_stmt_bodyEx_le advG)
  · exact reduce_le_compl_of_chain ProcedureState.globalL random_oracle_state
      retExG_le_roLift_compl

/-! ### The example invariant's endpoint premises

`hrefine` is the first conjunct of `P_ex`.  `hstable` keeps the outside-oracle agreement from its
own hypothesis and transports the eager-total/lazy⊆eager conjuncts along the table equalities. -/

/-- `P_ex` forces agreement on the non-oracle globals — the first conjunct of `P_ex`. -/
theorem hrefine_ex (g₁ g₂ : state) (h : P_ex g₁ g₂) :
    random_oracle_state.compl.get g₁ = random_oracle_state.compl.get g₂ := h.1

/-- `P_ex` is determined by the oracle table: overwriting the non-oracle globals on both sides while
    keeping each side's table preserves the outside agreement (`hc`), the eager-total conjunct and
    the lazy ⊆ eager conjunct (both transported along the table equalities `ho₁`/`ho₂`, since the
    oracle tables themselves are unchanged). -/
theorem hstable_ex (g₁ g₂ g₁' g₂' : state) (hP : P_ex g₁ g₂)
    (hc : random_oracle_state.compl.get g₁' = random_oracle_state.compl.get g₂')
    (ho₁ : random_oracle_state.get g₁' = random_oracle_state.get g₁)
    (ho₂ : random_oracle_state.get g₂' = random_oracle_state.get g₂) : P_ex g₁' g₂' :=
  ⟨hc, by rw [ho₁]; exact hP.2.1, by rw [ho₁, ho₂]; exact hP.2.2⟩

/-- **The worked instantiation of `prhl_instantiate_of_glob`.**  For the concrete adversary `A_ex`
    (global `advG`, a `Nat` local, two `output` locals for the two oracle answers, two oracle holes)
    and the genuine lazy ≈ eager invariant `P_ex`, the eager and lazy instantiations couple under
    `P_ex`, given only the per-query lazy ≈ eager coupling `h`.  Every structural hypothesis of the
    endpoint — footprint disjointness (`hdisj_ex`) and the two `P`-side conditions (`hrefine_ex`,
    `hstable_ex`) — is discharged; `h` is a hypothesis, as in the endpoint's own statement, and is
    now a *real* obligation because `P_ex` is satisfiable (see `P_ex`). -/
theorem glob_example_instantiation (args : (sigEx).ParamType)
    (h : ∀ inp : input,
      ProgramDenotation.prhl2 P_ex (random_oracle_query inp) (lazy_query inp) (liftPost P_ex)) :
    ProgramDenotation.prhl2 P_ex
      (procedureDenotation ((A_ex advG).instantiate RO_eager) args)
      (procedureDenotation ((A_ex advG).instantiate RO_lazy) args)
      (liftPost P_ex) :=
  prhl_instantiate_of_glob (P := P_ex) (A_ex advG) args (hdisj_ex advG) hrefine_ex hstable_ex h

/-- **Collision transfer, read off the coupling's result-equality.**  Running `A_ex` on inputs
    `(a, b)` returns the pair of oracle answers `A_ex` observed for `a` and `b`.  `liftPost P_ex`
    gives **equal results** on the two marginals (`u.1 = v.1`), so the *output-collision* event
    "`A_ex` queried two distinct inputs and got equal answers" — `a ≠ b ∧ u.1.1 = u.1.2` — holds
    against the **eager (real)** oracle exactly when it holds against the **lazy** one.

    Unlike a table-level `Collides ↔ Collides`, this is a *true* statement: it lives entirely on
    `A_ex`'s output, which the coupling equates, and never inspects the (differently-shaped)
    eager/lazy tables.  It is the abstract `output_win_transfer` specialized to `A_ex` with the
    win predicate `Win (r : output × output) := a ≠ b ∧ r.1 = r.2`. -/
theorem glob_example_collision_transfer (a b : input)
    (h : ∀ inp : input,
      ProgramDenotation.prhl2 P_ex (random_oracle_query inp) (lazy_query inp) (liftPost P_ex)) :
    ProgramDenotation.prhl2 P_ex
      (procedureDenotation ((A_ex advG).instantiate RO_eager) (a, b))
      (procedureDenotation ((A_ex advG).instantiate RO_lazy) (a, b))
      (fun u v => (a ≠ b ∧ u.1.1 = u.1.2) ↔ (a ≠ b ∧ v.1.1 = v.1.2)) :=
  output_win_transfer (P := P_ex) (A_ex advG) (a, b) (fun r => a ≠ b ∧ r.1 = r.2)
    (hdisj_ex advG) hrefine_ex hstable_ex h

/-- **End-to-end collision transfer for the worked adversary — no coupling hypothesis.**
    The per-query `h` of `glob_example_collision_transfer` is pointwise unsatisfiable for the
    genuine eager/lazy pair (a fixed eager entry cannot couple with a fresh lazy sample), so this
    is the honest form: at the **whole-game** level, with the initialisations included,
    `random_oracle_init` supplies the eager table's randomness and theorem 1 (the
    `convert`-sliding engine behind `output_win_transfer_games`) discharges everything.  The only
    remaining hypothesis is the structural footprint disjointness `hdisj_ex`.  The collision event
    on `A_ex`'s output transfers between the lazy and eager (real) games unconditionally. -/
theorem glob_example_collision_transfer_games (a b : input) :
    ProgramDenotation.prhl2 (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (do lazy_init; procedureDenotation ((A_ex advG).instantiate RO_lazy) (a, b))
      (do random_oracle_init; procedureDenotation ((A_ex advG).instantiate RO_eager) (a, b))
      (fun u v => (a ≠ b ∧ u.1.1 = u.1.2) ↔ (a ≠ b ∧ v.1.1 = v.1.2)) :=
  output_win_transfer_games (A_ex advG) (a, b) (fun r => a ≠ b ∧ r.1 = r.2) (hdisj_ex advG)

end

/-! ## Second worked example: the counterexample program `q`, in syntax

`CounterExamples/IndistinguishableVsGlob.lean` shows that the *minimal semantic* footprint of the
"asymmetric lazy flip" `q` separates observational indistinguishability from the touched getter.
Here the same program is written **syntactically** (`q_syn` — `if b then b ←$ ¾-bias else
b ←$ fair`), and for the region the syntax assigns it — `FVP.fvP_proc q_syn` — the two notions
provably **agree** (`qsyn_indistinguishable_iff_touched_getter_eq`), via the pointwise sandwich:
the region is bounded by `bVar`'s lens region (standard upper-bound assembly) and contains
`bVar`'s conditional-abort tests (a reduced read-slice of the `if`-condition). -/

section QSyn

variable (bVar : Variable Bool)

/-- The (trivial) signature of the syntactic `q` program: no parameters, `Unit` result. -/
def sigQ : ProcedureSignature := ⟨[], Unit⟩

/-- The (trivial) local state of `q_syn`. -/
instance : Nonempty (sigQ.LocalVariableState []) := ⟨⟨(), ()⟩⟩

/-- `bVar` viewed inside the (locals-free) procedure state. -/
noncomputable def bPS : Lens Bool (ProcedureState (sigQ.LocalVariableState [])) :=
  ProcedureState.globalL.chain bVar

/-- The ¾-biased sample expression (a constant distribution getter). -/
noncomputable def biasG : Getter (SubProbability Bool) (ProcedureState (sigQ.LocalVariableState [])) :=
  ⟨fun _ => toSubProbability GaudisCrypt.CounterExamples.biasPMF⟩

/-- The fair sample expression (a constant distribution getter). -/
noncomputable def flipG : Getter (SubProbability Bool) (ProcedureState (sigQ.LocalVariableState [])) :=
  ⟨fun _ => toSubProbability GaudisCrypt.CounterExamples.flipPMF⟩

/-- The body of the syntactic `q`: `if b then b ←$ ¾-bias else b ←$ fair`. -/
noncomputable def bodyQ : StmtWithHoles .empty (sigQ.LocalVariableState []) :=
  .ifThenElse (bPS bVar).toGetter
    (.sample (bPS bVar).toSetter biasG)
    (.sample (bPS bVar).toSetter flipG)

/-- The (trivial) return value of `q_syn`. -/
def retQ : Getter Unit (ProcedureState (sigQ.LocalVariableState [])) := ⟨fun _ => ()⟩

/-- **The counterexample program, in syntax** — its denotation's state action is exactly the
    abelian-footprint kernel `qKer` on the `bVar` component. -/
noncomputable def q_syn : ProcedureWithHoles .empty sigQ := ⟨[], bodyQ bVar, retQ⟩

/-- Reading a constant getter is `pure` (the leaf footprint of a constant is trivial). -/
private lemma get_const_eq_pure {γ : Type} (v : γ) :
    ProgramDenotation.get (⟨fun _ => v⟩ : Getter γ (ProcedureState (sigQ.LocalVariableState [])))
      = (pure v : ProgramDenotation (ProcedureState (sigQ.LocalVariableState [])) γ) := by
  funext st
  change (pure (st, st) : SubProbability (ProcedureState (sigQ.LocalVariableState []) ×
        ProcedureState (sigQ.LocalVariableState []))) >>=
      (fun w => (pure (v, w.2) : SubProbability (γ × ProcedureState (sigQ.LocalVariableState []))))
    = (pure (v, st) : SubProbability (γ × ProcedureState (sigQ.LocalVariableState [])))
  rw [SubProbability.pure_bind]

/-- **(ii) of the sandwich**: the syntactic region of `q_syn` is bounded by `bVar`'s lens region —
    every leaf reads/writes `bVar` (through `globalL`) or a constant, and the `globalL`-reduction
    of the chained region lands in `bVar.footprint`. -/
theorem fvP_qsyn_le : FVP.fvP_proc (q_syn bVar) ≤ bVar.footprint := by
  have hget : (ProgramDenotation.get (bPS bVar).toGetter).footprint ≤ (bPS bVar).footprint :=
    ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_get (bPS bVar))
  have hset : ProgramDenotation.footprint' (ProgramDenotation.set (bPS bVar).toSetter)
      ≤ (bPS bVar).footprint := by
    rw [ProgramDenotation.footprint']
    exact iSup_le fun ret =>
      ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_set _ ret)
  have hbias : (ProgramDenotation.get biasG).footprint ≤ (bPS bVar).footprint := by
    rw [show biasG = (⟨fun _ => toSubProbability GaudisCrypt.CounterExamples.biasPMF⟩ :
        Getter (SubProbability Bool) (ProcedureState (sigQ.LocalVariableState []))) from rfl,
      get_const_eq_pure]
    exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure _ _)
  have hflip : (ProgramDenotation.get flipG).footprint ≤ (bPS bVar).footprint := by
    rw [show flipG = (⟨fun _ => toSubProbability GaudisCrypt.CounterExamples.flipPMF⟩ :
        Getter (SubProbability Bool) (ProcedureState (sigQ.LocalVariableState []))) from rfl,
      get_const_eq_pure]
    exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure _ _)
  rw [show FVP.fvP_proc (q_syn bVar) =
      fvP_reduce ProcedureState.globalL (FVP.fvP_stmt (bodyQ bVar)) ⊔
        fvP_reduce ProcedureState.globalL ((ProgramDenotation.get retQ).footprint) from rfl]
  refine sup_le ?_ ?_
  · refine le_trans (fvP_reduce_mono _ ?_) (reduce_chain_footprint_le _ bVar)
    rw [show FVP.fvP_stmt (bodyQ bVar) =
        (ProgramDenotation.get (bPS bVar).toGetter).footprint ⊔
          ((ProgramDenotation.footprint' (ProgramDenotation.set (bPS bVar).toSetter) ⊔
              (ProgramDenotation.get biasG).footprint) ⊔
            (ProgramDenotation.footprint' (ProgramDenotation.set (bPS bVar).toSetter) ⊔
              (ProgramDenotation.get flipG).footprint)) from rfl]
    exact sup_le hget (sup_le (sup_le hset hbias) (sup_le hset hflip))
  · refine le_trans (fvP_reduce_mono _ ?_) (reduce_chain_footprint_le _ bVar)
    rw [show retQ = (⟨fun _ => ()⟩ :
        Getter Unit (ProcedureState (sigQ.LocalVariableState []))) from rfl, get_const_eq_pure]
    exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure _ _)

/-- **(i) of the sandwich**: `bVar`'s conditional-abort tests live in `q_syn`'s syntactic region.
    The `x₀`-slice of the `if`-condition read is the *chained* test `(bPS bVar).testKer x₀`;
    feeding the `globalL`-reduction a point input on the (trivial) locals and a constant-accept
    weight reduces it to the state-level test `bVar.testKer x₀`, which is therefore a *generator*
    of `fvP_reduce globalL (fvP_stmt bodyQ) ≤ FVP.fvP_proc q_syn`. -/
theorem testKer_mem_fvP_qsyn (x₀ : Bool) :
    bVar.testKer x₀ ∈ (FVP.fvP_proc (q_syn bVar)).updates := by
  classical
  have hgetst : ∀ st, ProgramDenotation.get (bPS bVar).toGetter st
      = (pure ((bPS bVar).get st, st) :
          SubProbability (Bool × ProcedureState (sigQ.LocalVariableState []))) := by
    intro st
    change (pure (st, st) : SubProbability (ProcedureState (sigQ.LocalVariableState []) ×
          ProcedureState (sigQ.LocalVariableState []))) >>=
        (fun w => (pure ((bPS bVar).get w.1, w.2) :
          SubProbability (Bool × ProcedureState (sigQ.LocalVariableState []))))
      = _
    rw [SubProbability.pure_bind]
  -- the chained test is a generator (an `x₀`-slice) of the condition-read leaf
  have h1 : (bPS bVar).testKer x₀ ∈
      ((ProgramDenotation.get (bPS bVar).toGetter).footprint).updates := by
    refine (Footprint.from_le_iff _ _).mp le_rfl ⟨x₀, ?_⟩
    funext st
    simp only [hgetst, SubProbability.pure_bind]
    by_cases h : (bPS bVar).get st = x₀
    · rw [if_pos h]
      exact (show (bPS bVar).testKer x₀ st = pure st from if_pos h).symm
    · rw [if_neg h]
      exact (show (bPS bVar).testKer x₀ st = ⊥ from if_neg h).symm
  -- transport into the body region
  have h2 : (bPS bVar).testKer x₀ ∈ (FVP.fvP_stmt (bodyQ bVar)).updates := by
    have hle : (ProgramDenotation.get (bPS bVar).toGetter).footprint
        ≤ FVP.fvP_stmt (bodyQ bVar) := by
      rw [show FVP.fvP_stmt (bodyQ bVar) =
          (ProgramDenotation.get (bPS bVar).toGetter).footprint ⊔
            ((ProgramDenotation.footprint' (ProgramDenotation.set (bPS bVar).toSetter) ⊔
                (ProgramDenotation.get biasG).footprint) ⊔
              (ProgramDenotation.footprint' (ProgramDenotation.set (bPS bVar).toSetter) ⊔
                (ProgramDenotation.get flipG).footprint)) from rfl]
      exact le_sup_left
    exact hle h1
  -- reduce the chained test to the state-level test
  obtain ⟨ps₀⟩ : Nonempty (ProcedureState (sigQ.LocalVariableState [])) := inferInstance
  have hne : Nonempty (ProcedureState (sigQ.LocalVariableState [])) := ⟨ps₀⟩
  set β₀ := (ProcedureState.globalL (l := sigQ.LocalVariableState [])).compl.get ps₀ with hβ₀
  have hinv : ∀ m : State,
      ProcedureState.globalL.get
        ((ProcedureState.globalL (l := sigQ.LocalVariableState [])).splitSpace.invFun (m, β₀))
      = m := by
    intro m
    simp only [Lens.splitSpace]
    rw [dif_pos hne]
    exact ProcedureState.globalL.set_get _ _
  have h3 : Lens.reduceSubProbability ProcedureState.globalL
      ((bPS bVar).testKer x₀, fun _ => (pure β₀ : SubProbability _),
        fun _ => (pure () : SubProbability Unit))
      = bVar.testKer x₀ := by
    funext m
    change ((pure β₀ : SubProbability _) >>= fun m' =>
        (bPS bVar).testKer x₀ (ProcedureState.globalL.splitSpace.invFun (m, m')) >>= fun m'' =>
          (pure () : SubProbability Unit) >>= fun _ =>
            (pure (ProcedureState.globalL.get m'') : SubProbability State))
      = bVar.testKer x₀ m
    rw [SubProbability.pure_bind]
    have hcond : (bPS bVar).get (ProcedureState.globalL.splitSpace.invFun (m, β₀)) = bVar.get m := by
      change bVar.get (ProcedureState.globalL.get
          (ProcedureState.globalL.splitSpace.invFun (m, β₀))) = bVar.get m
      rw [hinv m]
    by_cases h : bVar.get m = x₀
    · rw [show (bPS bVar).testKer x₀ (ProcedureState.globalL.splitSpace.invFun (m, β₀))
            = pure (ProcedureState.globalL.splitSpace.invFun (m, β₀))
          from if_pos (hcond.trans h), SubProbability.pure_bind, SubProbability.pure_bind,
        hinv m]
      exact (show bVar.testKer x₀ m = pure m from if_pos h).symm
    · rw [show (bPS bVar).testKer x₀ (ProcedureState.globalL.splitSpace.invFun (m, β₀))
            = ⊥ from if_neg (fun hc => h (hcond.symm.trans hc)), SubProbability.bot_bind]
      exact (show bVar.testKer x₀ m = ⊥ from if_neg h).symm
  -- generator membership in the reduction, then into `fvP_proc`
  have h4 : bVar.testKer x₀
      ∈ (fvP_reduce ProcedureState.globalL (FVP.fvP_stmt (bodyQ bVar))).updates := by
    refine (Footprint.from_le_iff _ _).mp le_rfl ?_
    exact ⟨((bPS bVar).testKer x₀, fun _ => (pure β₀ : SubProbability _),
        fun _ => (pure () : SubProbability Unit)),
      ⟨h2, Set.mem_univ _, Set.mem_univ _⟩, h3⟩
  have h5 : fvP_reduce ProcedureState.globalL (FVP.fvP_stmt (bodyQ bVar))
      ≤ FVP.fvP_proc (q_syn bVar) := by
    rw [show FVP.fvP_proc (q_syn bVar) =
        fvP_reduce ProcedureState.globalL (FVP.fvP_stmt (bodyQ bVar)) ⊔
          fvP_reduce ProcedureState.globalL ((ProgramDenotation.get retQ).footprint) from rfl]
    exact le_sup_left
  exact h5 h4

/-- **For the region syntax assigns to the counterexample program, the notions agree**:
    observational indistinguishability through `FVP.fvP_proc q_syn` *is* touched-getter equality.
    Instance of the pointwise sandwich — contrast with the *minimal semantic* footprint of the
    same program, where the two notions provably differ
    (`CounterExamples.exists_indistinguishable_touched_getter_ne`). -/
theorem qsyn_indistinguishable_iff_touched_getter_eq (σ σ' : State) :
    (FVP.fvP_proc (q_syn bVar)).indistinguishable σ σ' ↔
      (FVP.fvP_proc (q_syn bVar)).touched_getter.get σ
        = (FVP.fvP_proc (q_syn bVar)).touched_getter.get σ' :=
  Footprint.indistinguishable_iff_touched_getter_eq_of_sandwich
    (testKer_mem_fvP_qsyn bVar) (fvP_qsyn_le bVar) σ σ'

/-- The concrete form: `q_syn`'s tests see exactly the variable `bVar`. -/
theorem qsyn_indistinguishable_iff_get_eq (σ σ' : State) :
    (FVP.fvP_proc (q_syn bVar)).indistinguishable σ σ' ↔ bVar.get σ = bVar.get σ' :=
  ⟨fun h => Footprint.get_eq_of_indistinguishable_of_testKer_mem (testKer_mem_fvP_qsyn bVar) h,
    fun h => (qsyn_indistinguishable_iff_touched_getter_eq bVar σ σ').mpr
      (Footprint.touched_getter_eq_of_le (fvP_qsyn_le bVar)
        ((bVar.footprint_touched_getter_eq_iff σ σ').mpr h))⟩

/-- **`glob q_syn = b`** (EasyCrypt's `glob Q = {b}`), stated with the touched getter: the
    touched getter of the region syntax assigns to `q_syn` induces **the same equivalence on
    states** as reading the variable `bVar` — kernel equality of the two getters, which is the
    only identification `={glob ·}`-style reasoning ever consumes (their codomains differ, so
    literal equality is ill-typed).  Proved *observationally*: both sides are the
    indistinguishability relation of the region. -/
theorem qsyn_touched_getter_eq_iff_get_eq (σ σ' : State) :
    (FVP.fvP_proc (q_syn bVar)).touched_getter.get σ
        = (FVP.fvP_proc (q_syn bVar)).touched_getter.get σ'
      ↔ bVar.get σ = bVar.get σ' :=
  (qsyn_indistinguishable_iff_touched_getter_eq bVar σ σ').symm.trans
    (qsyn_indistinguishable_iff_get_eq bVar σ σ')

end QSyn

end GaudisCrypt.Lib.RO.Instantiate
