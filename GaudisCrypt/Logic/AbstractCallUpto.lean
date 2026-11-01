import GaudisCrypt.Logic.AbstractCall
import GaudisCrypt.Logic.PRHL2Upto
import GaudisCrypt.Logic.PHoare

/-!
# The up-to-bad abstract call rule (EasyCrypt's `call (: bad, invP, invQ)`)

EasyCrypt's abstract call rule has an up-to-bad form (`equivF_abs_upto`, `src/phl/ecPhlFun.ml`):
the two oracle instantiations need agree only until a bad event on the right, after which the
runs are unrelated except for an invariant `invQ`.  `prhlProc_abstract_call_upto` (procedure with
holes) and `prhlProc_abstract_call_upto_module` (module) are that rule.

The coupling (`prhl2_body_upto`) is built by induction over the adversary's code, with the
invariant `uptoInv`: before the bad event, the runs are synchronized as in the plain abstract call
rule (`syncInv`: `={glob}`, `invP`, equal locals); after it, the two runs of what remains couple
independently (`ProgramDenotation.prhl2.product`), each side keeping a unary invariant
(`satisfies_inv_of_confined`).  An independent coupling needs both remainders to be lossless:
the induction carries "this statement is lossless here" (`ProgramDenotation.LosslessAt`), which
the adversary's losslessness gives at the start and `LosslessAt.of_bind` passes on to almost every
intermediate state.  A loop switches to the independent coupling at the start of an iteration
(`ProgramDenotation.prhl2.while_upto`, `Logic/PRHL2Upto.lean`), since after the bad event the
two guards need not agree.
-/

namespace GaudisCrypt

/-- The mass of a sub-probability is the sum of its atoms. -/
lemma SubProbability.mass_eq_tsum {T : Type u} (μ : SubProbability T) :
    μ.1 Set.univ = ∑' t, μ.1 {t} := by
  rw [μ.2.2 Set.univ, tsum_subtype Set.univ (fun t => μ.1 {t}), Set.indicator_univ]

lemma SubProbability.mass_eq_expected {T : Type u} (μ : SubProbability T) :
    μ.1 Set.univ = μ.expected (fun _ => 1) := by
  unfold SubProbability.expected
  rw [MeasureTheory.lintegral_one]

/-- The mass of a bind: the continuation's masses, weighted by the atoms. -/
lemma SubProbability.mass_bind {α β : Type u} (μ : SubProbability α) (f : α → SubProbability β) :
    (μ >>= f).1 Set.univ = ∑' t, (f t).1 Set.univ * μ.1 {t} := by
  rw [SubProbability.mass_eq_expected, SubProbability.expected_bind,
    SubProbability.expected_eq_tsum]
  simp only [← SubProbability.mass_eq_expected]

/-- **A lossless bind**: its first part is lossless, and its continuation is lossless at every
atom of the first part. -/
lemma SubProbability.lossless_of_bind {α β : Type u} {μ : SubProbability α}
    {f : α → SubProbability β} (h : (μ >>= f).1 Set.univ = 1) :
    μ.1 Set.univ = 1 ∧ μ.satisfies (fun t => (f t).1 Set.univ = 1) := by
  rw [SubProbability.mass_bind] at h
  have hm : ∀ t, (f t).1 Set.univ ≤ 1 := fun t => (f t).2.1
  have hle : ∑' t, (f t).1 Set.univ * μ.1 {t} ≤ ∑' t, μ.1 {t} :=
    ENNReal.tsum_le_tsum fun t => mul_le_of_le_one_left' (hm t)
  have hsum : ∑' t, μ.1 {t} = 1 :=
    le_antisymm (SubProbability.tsum_singleton_le_one μ) (h.symm.le.trans hle)
  refine ⟨(SubProbability.mass_eq_tsum μ).trans hsum, fun t₀ ht₀ => ?_⟩
  by_contra hne
  have hlt : (f t₀).1 Set.univ < 1 := lt_of_le_of_ne (hm t₀) hne
  have hfin : μ.1 {t₀} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((MeasureTheory.measure_mono (Set.subset_univ _)).trans μ.2.1)
  have hstrict : (f t₀).1 Set.univ * μ.1 {t₀} < μ.1 {t₀} := by
    have := ENNReal.mul_lt_mul_right ht₀ hfin hlt
    rwa [mul_one, mul_comm] at this
  have : ∑' t, (f t).1 Set.univ * μ.1 {t} < ∑' t, μ.1 {t} :=
    ENNReal.tsum_lt_tsum (by rw [h]; exact ENNReal.one_ne_top)
      (fun t => mul_le_of_le_one_left' (hm t)) hstrict
  rw [h, hsum] at this
  exact lt_irrefl _ this

/-- `c` runs without loss from `σ`. -/
def ProgramDenotation.LosslessAt {s : Type u} {α : Type v} (c : ProgramDenotation s α) (σ : s) :
    Prop :=
  (c σ).1 Set.univ = 1

/-- A program lossless at `σ` followed by `k`: lossless at `σ`, and `k` is lossless at every
outcome. -/
theorem ProgramDenotation.LosslessAt.of_bind {s : Type u} {α β : Type v}
    {c : ProgramDenotation s α} {k : α → ProgramDenotation s β} {σ : s}
    (h : (c >>= k).LosslessAt σ) :
    c.LosslessAt σ ∧ (c σ).satisfies (fun x => (k x.1).LosslessAt x.2) := by
  have h' : (c σ >>= fun r => k r.1 r.2).1 Set.univ = 1 := h
  exact SubProbability.lossless_of_bind h'

/-- Running a lossless sub-probability first does not change the expectation of what follows. -/
lemma SubProbability.bind_const_of_lossless {α β : Type u} (μ : SubProbability α)
    (hμ : μ.1 Set.univ = 1) (ν : SubProbability β) : (μ >>= fun _ => ν) = ν := by
  refine SubProbability.ext_of_expected (fun F => ?_)
  rw [SubProbability.expected_bind]
  unfold SubProbability.expected
  rw [MeasureTheory.lintegral_const, hμ, mul_one]

/-- **The product coupling**: two runs, lossless at the related states, couple independently;
the postcondition must hold for every pair of outcomes. -/
theorem ProgramDenotation.prhl2.product {s₁ s₂ : Type (max u v)} {α β : Type v}
    {A : s₁ → s₂ → Prop} {c : ProgramDenotation s₁ α} {d : ProgramDenotation s₂ β}
    {B : α × s₁ → β × s₂ → Prop}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → c.LosslessAt σ₁ ∧ d.LosslessAt σ₂ ∧
      ∀ x y, (c σ₁).1 {x} ≠ 0 → (d σ₂).1 {y} ≠ 0 → B x y) :
    ProgramDenotation.prhl2 A c d B := by
  intro σ₁ σ₂ hA
  obtain ⟨hc, hd, hB⟩ := h σ₁ σ₂ hA
  refine ⟨c σ₁ >>= fun x => d σ₂ >>= fun y => pure (x, y), ?_, ?_, ?_⟩
  · rw [SubProbability.bind_assoc]
    simp only [SubProbability.bind_assoc, SubProbability.pure_bind]
    simp only [SubProbability.bind_const_pure _ hd]
    exact SubProbability.bind_pure _
  · rw [SubProbability.bind_assoc]
    simp only [SubProbability.bind_assoc, SubProbability.pure_bind, SubProbability.bind_pure]
    exact SubProbability.bind_const_of_lossless _ hc _
  · exact SubProbability.satisfies_bind _ fun x hx => SubProbability.satisfies_bind _
      fun y hy => SubProbability.satisfies_pure _ _ (hB x y hx hy)

/-! ## One side at a time: invariants of the `L`-content -/

open GaudisCrypt.Lib.RO.Instantiate

section Unary

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-- The diagonal invariant: equal states, and `Inv` of the `L`-content. -/
def diagInv (Inv : Ω → Prop) (g₁ g₂ : VariableAssignment) : Prop :=
  g₁ = g₂ ∧ Inv (L.get g₁)

/-- A run confined to a region outside `L` keeps the `L`-content. -/
theorem satisfies_lens_eq_of_confined {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ) {γ : Type}
    {p : ProgramDenotation ProgramState γ} (hp : p.inFootprint (fvP_proc A))
    (ps : ProgramState) :
    (p ps).satisfies (fun xs => L.get xs.2.globals = L.get ps.globals) := by
  have hSle : (ProgramState.globalL.chain L).footprint ≤ (fvP_proc A)ᶜ :=
    (Footprint.le_compl_comm _ _).mp (fvP_proc_le_chain_compl L A hdisj)
  intro xs hxs
  exact (Lens.footprint_touched_getter_eq_iff (ProgramState.globalL.chain L) _ _).mp
    (inFootprint_preserves_touched hp hSle (Lens.footprint_hasReset _ ps) xs hxs)

/-- The adversary's own steps keep the diagonal invariant. -/
theorem footprintCompat_diagInv {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    (Inv : Ω → Prop) : FootprintCompat (diagInv L Inv) (fvP_proc A) := by
  intro γ p hp ps₁ ps₂ hpre
  obtain ⟨⟨hg, hI⟩, hloc⟩ := hpre
  have hps : ps₁ = ps₂ := by cases ps₁; cases ps₂; simp_all
  subst hps
  refine ⟨p ps₁ >>= fun x => pure (x, x), ?_, ?_, ?_⟩
  · simp only [SubProbability.bind_assoc, SubProbability.pure_bind, SubProbability.bind_pure]
  · simp only [SubProbability.bind_assoc, SubProbability.pure_bind, SubProbability.bind_pure]
  · refine SubProbability.satisfies_bind _ fun x hx => SubProbability.satisfies_pure _ _ ?_
    have hL := satisfies_lens_eq_of_confined L A hdisj hp ps₁ x hx
    exact ⟨rfl, ⟨rfl, by rw [hL]; exact hI⟩, rfl⟩

/-- **Unary invariance**: a statement confined to what `A` may touch, with oracles that keep
`Inv` of the `L`-content, keeps it. -/
theorem satisfies_inv_of_confined {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (inst : holes.Instantiation) (Inv : Ω → Prop)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType)
      (g : VariableAssignment), Inv (L.get g) →
      (procedureDenotation (inst.lookup n) a g).satisfies (fun x => Inv (L.get x.2)))
    (s : StmtWithHoles holes) (hs : ConfinedP (fvP_proc A) s) (ps : ProgramState)
    (hps : Inv (L.get ps.globals)) :
    (programDenotation (s.instantiate inst) ps).satisfies
      (fun x => Inv (L.get x.2.globals)) := by
  have hloc := confinedP_locP (fvP_proc A) (footprintCompat_diagInv L A hdisj Inv) hc s hs
  have hdiag : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (a : sig'.ParamType),
      ProgramDenotation.prhl2 (diagInv L Inv) (procedureDenotation (inst.lookup n) a)
        (procedureDenotation (inst.lookup n) a) (liftPost (diagInv L Inv)) := by
    intro sig' n a g₁ g₂ ⟨hg, hI⟩
    subst hg
    refine ⟨procedureDenotation (inst.lookup n) a g₁ >>= fun x => pure (x, x), ?_, ?_, ?_⟩
    · simp only [SubProbability.bind_assoc, SubProbability.pure_bind, SubProbability.bind_pure]
    · simp only [SubProbability.bind_assoc, SubProbability.pure_bind, SubProbability.bind_pure]
    · exact SubProbability.satisfies_bind _ fun x hx =>
        SubProbability.satisfies_pure _ _ ⟨rfl, rfl, horacle n a g₁ hI x hx⟩
  obtain ⟨μ, hm1, _, hsat⟩ := body_prhl2_gen s inst inst hloc
    (fun n x p hp hx => hhole_of_prhl2 inst inst hdiag n x p hp hx) ps ps ⟨⟨rfl, hps⟩, rfl⟩
  rw [← hm1]
  exact SubProbability.satisfies_bind _ fun w hw =>
    SubProbability.satisfies_pure _ _ (hsat w hw).2.1.2

end Unary

/-- A coupling whose marginals satisfy `U₁`, `U₂` satisfies them on its support. -/
theorem ProgramDenotation.prhl2.strengthen {s₁ s₂ : Type (max u v)} {α β : Type v}
    {A : s₁ → s₂ → Prop} {c : ProgramDenotation s₁ α} {d : ProgramDenotation s₂ β}
    {B : α × s₁ → β × s₂ → Prop} {U₁ : α × s₁ → Prop} {U₂ : β × s₂ → Prop}
    (h : ProgramDenotation.prhl2 A c d B)
    (hu : ∀ σ₁ σ₂, A σ₁ σ₂ → (c σ₁).satisfies U₁ ∧ (d σ₂).satisfies U₂) :
    ProgramDenotation.prhl2 A c d (fun u v => B u v ∧ U₁ u ∧ U₂ v) := by
  intro σ₁ σ₂ hA
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ₁ σ₂ hA
  have h1 : μ.satisfies (fun w => U₁ w.1) :=
    coupling_satisfies_fst (by rw [hm1]; exact (hu σ₁ σ₂ hA).1)
  have h2 : μ.satisfies (fun w => U₂ w.2) :=
    coupling_satisfies_snd (by rw [hm2]; exact (hu σ₁ σ₂ hA).2)
  exact ⟨μ, hm1, hm2, fun w hw => ⟨hsat w hw, h1 w hw, h2 w hw⟩⟩

theorem ProgramDenotation.set_losslessAt {s : Type u} {a : Type v} (x : Setter a s) (r : a)
    (σ : s) : (ProgramDenotation.set x r).LosslessAt σ := by
  letI : MeasurableSpace (Unit × s) := ⊤
  exact MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ ((), x.set r σ))

/-- A loop lossless at `σ`: at the guard's outcome, the rest (`body; loop` or nothing) is
lossless. -/
theorem ProgramDenotation.LosslessAt.while_unroll {s : Type u}
    {cond : ProgramDenotation s Bool} {body : ProgramDenotation s Unit} {σ : s}
    (h : (GaudisCrypt.while_loop cond body).LosslessAt σ) :
    (cond σ).satisfies (fun x => (if x.1 then (body >>= fun _ => GaudisCrypt.while_loop cond body)
      else pure ()).LosslessAt x.2) := by
  rw [GaudisCrypt.while_unroll] at h
  exact (ProgramDenotation.LosslessAt.of_bind h).2

/-! ## The up-to-bad induction -/

section Upto

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-- Before the bad event: `={glob}` on `F`, `I` on the `L`-contents, and not `bad` on the right
(EasyCrypt's `!bad{2} /\ ={glob A} /\ invP`). -/
abbrev syncInv (F : Footprint VariableAssignment) (I : Ω → Ω → Prop) (bad : Ω → Prop) :
    VariableAssignment → VariableAssignment → Prop :=
  globInvF L F (fun ω₁ ω₂ => I ω₁ ω₂ ∧ ¬ bad ω₂)

/-- After the bad event: `bad` on the right, and `Q` on the `L`-contents (EasyCrypt's
`bad{2} /\ invQ`). -/
abbrev badInv (bad : Ω → Prop) (Q : Ω → Ω → Prop) (g₁ g₂ : VariableAssignment) : Prop :=
  bad (L.get g₂) ∧ Q (L.get g₁) (L.get g₂)

/-- The invariant of the up-to-bad induction, on procedure states. -/
abbrev uptoInv (F : Footprint VariableAssignment) (I : Ω → Ω → Prop) (bad : Ω → Prop)
    (Q : Ω → Ω → Prop) (ps₁ ps₂ : ProgramState) : Prop :=
  badInv L bad Q ps₁.globals ps₂.globals ∨ liftRel (syncInv L F I bad) ps₁ ps₂

variable {holes : HoleSigs} {sig : ProcedureSignature} (A : ProcedureWithHoles holes sig)
  (inst₁ inst₂ : holes.Instantiation) (bad : Ω → Prop) (Q : Ω → Ω → Prop)

/-- **After the bad event**: the two runs of any statement of `A`, lossless at the related
states, couple independently; the left keeps `Q` against the right's state, the right keeps
`bad` and `Q`. -/
theorem prhl2_badInv_product (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (hQ₁ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₂ : Ω), bad ω₂ → Q (L.get g) ω₂ →
      (procedureDenotation (inst₁.lookup n) a g).satisfies (fun x => Q (L.get x.2) ω₂))
    (hQ₂ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₁ : Ω), bad (L.get g) → Q ω₁ (L.get g) →
      (procedureDenotation (inst₂.lookup n) a g).satisfies
        (fun x => bad (L.get x.2) ∧ Q ω₁ (L.get x.2)))
    (s : StmtWithHoles holes) (hs : ConfinedP (fvP_proc A) s) :
    ProgramDenotation.prhl2
      (fun ps₁ ps₂ => badInv L bad Q ps₁.globals ps₂.globals ∧
        (programDenotation (s.instantiate inst₁)).LosslessAt ps₁ ∧
        (programDenotation (s.instantiate inst₂)).LosslessAt ps₂)
      (programDenotation (s.instantiate inst₁)) (programDenotation (s.instantiate inst₂))
      (fun u v => badInv L bad Q u.2.globals v.2.globals) := by
  refine ProgramDenotation.prhl2.product fun ps₁ ps₂ ⟨⟨hb, hq⟩, hl₁, hl₂⟩ => ⟨hl₁, hl₂, ?_⟩
  intro x y hx hy
  have h1 := satisfies_inv_of_confined L A hdisj hc inst₁ (fun ω => Q ω (L.get ps₂.globals))
    (fun n a g hg => hQ₁ n a g _ hb hg) s hs ps₁ hq x hx
  exact satisfies_inv_of_confined L A hdisj hc inst₂
    (fun ω => bad ω ∧ Q (L.get x.2.globals) ω)
    (fun n a g hg => hQ₂ n a g _ hg.1 hg.2) s hs ps₂ ⟨hb, h1⟩ y hy

variable (F : Footprint VariableAssignment) (I : Ω → Ω → Prop)

/-- Before a statement, the bad event happened (`prhl2_badInv_product`) or not: it suffices to
treat the synchronized case. -/
theorem prhl2_upto_split (hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (hQ₁ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₂ : Ω), bad ω₂ → Q (L.get g) ω₂ →
      (procedureDenotation (inst₁.lookup n) a g).satisfies (fun x => Q (L.get x.2) ω₂))
    (hQ₂ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₁ : Ω), bad (L.get g) → Q ω₁ (L.get g) →
      (procedureDenotation (inst₂.lookup n) a g).satisfies
        (fun x => bad (L.get x.2) ∧ Q ω₁ (L.get x.2)))
    (s : StmtWithHoles holes) (hs : ConfinedP (fvP_proc A) s)
    (hsync : ProgramDenotation.prhl2
        (fun ps₁ ps₂ => (uptoInv L F I bad Q ps₁ ps₂ ∧
          (programDenotation (s.instantiate inst₁)).LosslessAt ps₁ ∧
          (programDenotation (s.instantiate inst₂)).LosslessAt ps₂) ∧
          ¬ badInv L bad Q ps₁.globals ps₂.globals)
        (programDenotation (s.instantiate inst₁)) (programDenotation (s.instantiate inst₂))
        (fun u v => uptoInv L F I bad Q u.2 v.2)) :
    ProgramDenotation.prhl2
      (fun ps₁ ps₂ => uptoInv L F I bad Q ps₁ ps₂ ∧
        (programDenotation (s.instantiate inst₁)).LosslessAt ps₁ ∧
        (programDenotation (s.instantiate inst₂)).LosslessAt ps₂)
      (programDenotation (s.instantiate inst₁)) (programDenotation (s.instantiate inst₂))
      (fun u v => uptoInv L F I bad Q u.2 v.2) := by
  refine ProgramDenotation.prhl2.case
    (fun ps₁ ps₂ => badInv L bad Q ps₁.globals ps₂.globals) ?_ hsync
  exact (prhl2_badInv_product L A inst₁ inst₂ bad Q hdisj hc hQ₁ hQ₂ s hs).conseq
    (fun _ _ h => ⟨h.2, h.1.2⟩) (fun _ _ h => Or.inl h)

/-- **The up-to-bad induction** (the body of EasyCrypt's `call (: bad, invP, invQ)` for an
abstract procedure): every statement of `A`, lossless at the related states, keeps `uptoInv`.
Before the bad event the two runs are synchronized (`={glob}`, `invP`, equal locals) and the
oracle calls are coupled by `horacle`; after it, they couple independently
(`prhl2_badInv_product`); a loop switches to that at the start of an iteration
(`prhl2.while_upto`). -/
theorem prhl2_body_upto (hAF : FVP.fvP_proc A ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (horacle : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType),
      ProgramDenotation.prhl2 (syncInv L F I bad) (procedureDenotation (inst₁.lookup n) a)
        (procedureDenotation (inst₂.lookup n) a)
        (fun u v => badInv L bad Q u.2 v.2 ∨ (u.1 = v.1 ∧ syncInv L F I bad u.2 v.2)))
    (hQ₁ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₂ : Ω), bad ω₂ → Q (L.get g) ω₂ →
      (procedureDenotation (inst₁.lookup n) a g).satisfies (fun x => Q (L.get x.2) ω₂))
    (hQ₂ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₁ : Ω), bad (L.get g) → Q ω₁ (L.get g) →
      (procedureDenotation (inst₂.lookup n) a g).satisfies
        (fun x => bad (L.get x.2) ∧ Q ω₁ (L.get x.2))) :
    ∀ (s : StmtWithHoles holes), ConfinedP (fvP_proc A) s →
    ProgramDenotation.prhl2
      (fun ps₁ ps₂ => uptoInv L F I bad Q ps₁ ps₂ ∧
        (programDenotation (s.instantiate inst₁)).LosslessAt ps₁ ∧
        (programDenotation (s.instantiate inst₂)).LosslessAt ps₂)
      (programDenotation (s.instantiate inst₁)) (programDenotation (s.instantiate inst₂))
      (fun u v => uptoInv L F I bad Q u.2 v.2)
  | .skip, hs => by
      refine prhl2_upto_split L A inst₁ inst₂ bad Q F I (hAF.trans hFL) hc hQ₁ hQ₂ _ hs ?_
      simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
      exact ProgramDenotation.prhl2.pure_pure fun _ _ h => Or.inr (h.1.1.resolve_left h.2)
  | .sample x e, hs => by
      have hl : LocP (syncInv L F I bad) _ := confinedP_locP (fvP_proc A)
        (footprintCompat_globInvF L A F hAF hFL (fun ω₁ ω₂ => I ω₁ ω₂ ∧ ¬ bad ω₂)) hc _ hs
      refine prhl2_upto_split L A inst₁ inst₂ bad Q F I (hAF.trans hFL) hc hQ₁ hQ₂ _ hs ?_
      simp only [StmtWithHoles.instantiate]
      exact hl.conseq (fun _ _ h => h.1.1.resolve_left h.2) (fun _ _ h => Or.inr h.2)
  | .call' x ns hl hn b r p, hs => by
      have hl : LocP (syncInv L F I bad) _ := confinedP_locP (fvP_proc A)
        (footprintCompat_globInvF L A F hAF hFL (fun ω₁ ω₂ => I ω₁ ω₂ ∧ ¬ bad ω₂)) hc _ hs
      refine prhl2_upto_split L A inst₁ inst₂ bad Q F I (hAF.trans hFL) hc hQ₁ hQ₂ _ hs ?_
      simp only [StmtWithHoles.instantiate]
      exact hl.conseq (fun _ _ h => h.1.1.resolve_left h.2) (fun _ _ h => Or.inr h.2)
  | .hole n x p, hs => by
      have hl : LocP (syncInv L F I bad) _ := confinedP_locP (fvP_proc A)
        (footprintCompat_globInvF L A F hAF hFL (fun ω₁ ω₂ => I ω₁ ω₂ ∧ ¬ bad ω₂)) hc _ hs
      have hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ := hAF.trans hFL
      refine prhl2_upto_split L A inst₁ inst₂ bad Q F I hdisj hc hQ₁ hQ₂ _ hs ?_
      simp only [StmtWithHoles.instantiate]
      rw [denote_call, denote_call]
      refine (ProgramDenotation.prhl2.bind hl.1 (fun args₁ args₂ => ?_)).conseq
        (fun _ _ h => h.1.1.resolve_left h.2) (fun _ _ h => h)
      intro σ₁ σ₂ hpre
      obtain ⟨hargs, hrel⟩ := hpre
      dsimp only at hargs
      subst hargs
      refine (ProgramDenotation.prhl2.bind (k₁ := fun ret => ProgramDenotation.set x ret)
        (k₂ := fun ret => ProgramDenotation.set x ret)
        (B := fun u v => uptoInv L F I bad Q u.2 v.2) (prhl2_zoom (horacle n args₁))
        (fun r₁ r₂ => ?_)) σ₁ σ₂ hrel
      rintro τ₁ τ₂ ⟨hB, hlocs⟩
      rcases hB with hb | ⟨hr, hsync⟩
      · -- after the bad event: the result writes keep the `L`-contents
        refine ProgramDenotation.prhl2.product
          (A := fun σ₁ σ₂ => badInv L bad Q σ₁.globals σ₂.globals)
          (c := ProgramDenotation.set x r₁) (d := ProgramDenotation.set x r₂)
          (B := fun u v => uptoInv L F I bad Q u.2 v.2)
          (fun σ₁ σ₂ h => ⟨ProgramDenotation.set_losslessAt _ _ _,
            ProgramDenotation.set_losslessAt _ _ _, fun u v hu hv => Or.inl ?_⟩) τ₁ τ₂ hb
        show badInv L bad Q u.2.globals v.2.globals
        unfold badInv
        rw [satisfies_lens_eq_of_confined L A hdisj (hs.2 r₁) σ₁ u hu,
          satisfies_lens_eq_of_confined L A hdisj (hs.2 r₂) σ₂ v hv]
        exact h
      · dsimp only at hr
        subst hr
        exact ((hl.2 r₁).conseq (B' := fun u v => uptoInv L F I bad Q u.2 v.2)
          (fun _ _ h => h) (fun _ _ h => Or.inr h.2)) τ₁ τ₂
          ⟨hsync, hlocs⟩
  | .seq a b, hs => by
      simp only [StmtWithHoles.instantiate, programDenotation]
      refine ProgramDenotation.prhl2.bind
        (((prhl2_body_upto hAF hFL hc horacle hQ₁ hQ₂ a hs.1).conseq
            (fun _ _ h => ⟨h.1, (ProgramDenotation.LosslessAt.of_bind h.2.1).1,
              (ProgramDenotation.LosslessAt.of_bind h.2.2).1⟩) (fun _ _ h => h)).strengthen
          (fun _ _ h => ⟨(ProgramDenotation.LosslessAt.of_bind h.2.1).2,
            (ProgramDenotation.LosslessAt.of_bind h.2.2).2⟩))
        (fun _ _ => (prhl2_body_upto hAF hFL hc horacle hQ₁ hQ₂ b hs.2).conseq
          (fun _ _ h => h) (fun _ _ h => h))
  | .ifThenElse c t e, hs => by
      have hl : LocP (syncInv L F I bad) _ := confinedP_locP (fvP_proc A)
        (footprintCompat_globInvF L A F hAF hFL (fun ω₁ ω₂ => I ω₁ ω₂ ∧ ¬ bad ω₂)) hc _ hs
      refine prhl2_upto_split L A inst₁ inst₂ bad Q F I (hAF.trans hFL) hc hQ₁ hQ₂ _ hs ?_
      simp only [StmtWithHoles.instantiate, programDenotation]
      refine ProgramDenotation.prhl2.bind
        ((hl.1.conseq (fun _ _ h => h.1.1.resolve_left h.2) (fun _ _ h => h)).strengthen
          (fun _ _ h => ⟨(ProgramDenotation.LosslessAt.of_bind h.1.2.1).2,
            (ProgramDenotation.LosslessAt.of_bind h.1.2.2).2⟩)) (fun b₁ b₂ => ?_)
      rintro τ₁ τ₂ ⟨⟨hbeq, hrel⟩, hl₁, hl₂⟩
      dsimp only at hbeq
      subst hbeq
      cases b₁
      · exact (prhl2_body_upto hAF hFL hc horacle hQ₁ hQ₂ e hs.2.2) τ₁ τ₂
          ⟨Or.inr hrel, hl₁, hl₂⟩
      · exact (prhl2_body_upto hAF hFL hc horacle hQ₁ hQ₂ t hs.2.1) τ₁ τ₂
          ⟨Or.inr hrel, hl₁, hl₂⟩
  | .while c t, hs => by
      have hl : LocP (syncInv L F I bad) _ := confinedP_locP (fvP_proc A)
        (footprintCompat_globInvF L A F hAF hFL (fun ω₁ ω₂ => I ω₁ ω₂ ∧ ¬ bad ω₂)) hc _ hs
      have hexit := prhl2_badInv_product L A inst₁ inst₂ bad Q (hAF.trans hFL) hc hQ₁ hQ₂ _ hs
      have iht := prhl2_body_upto hAF hFL hc horacle hQ₁ hQ₂ t hs.2
      simp only [StmtWithHoles.instantiate, programDenotation] at hexit ⊢
      refine (ProgramDenotation.prhl2.while_upto
        (Inv := fun ps₁ ps₂ => uptoInv L F I bad Q ps₁ ps₂ ∧
          (GaudisCrypt.while_loop (ProgramDenotation.get c)
            (programDenotation (t.instantiate inst₁))).LosslessAt ps₁ ∧
          (GaudisCrypt.while_loop (ProgramDenotation.get c)
            (programDenotation (t.instantiate inst₂))).LosslessAt ps₂)
        (Exit := fun ps₁ ps₂ => badInv L bad Q ps₁.globals ps₂.globals)
        (PostC := fun b ps₁ ps₂ => liftRel (syncInv L F I bad) ps₁ ps₂ ∧
          (if b then (programDenotation (t.instantiate inst₁) >>= fun _ =>
            GaudisCrypt.while_loop (ProgramDenotation.get c)
              (programDenotation (t.instantiate inst₁))) else pure ()).LosslessAt ps₁ ∧
          (if b then (programDenotation (t.instantiate inst₂) >>= fun _ =>
            GaudisCrypt.while_loop (ProgramDenotation.get c)
              (programDenotation (t.instantiate inst₂))) else pure ()).LosslessAt ps₂)
        (PostE := fun u v => badInv L bad Q u.2.globals v.2.globals) ?_ ?_ ?_).conseq
          (fun _ _ h => h) (fun _ _ h => h.elim (fun h => Or.inr h.1) Or.inl)
      · exact ((hl.1.conseq (fun _ _ h => h.1.1.resolve_left h.2) (fun _ _ h => h)).strengthen
          (fun _ _ h => ⟨h.1.2.1.while_unroll, h.1.2.2.while_unroll⟩)).conseq
          (fun _ _ h => h) (fun _ _ h => ⟨h.1.1, h.1.2, h.2.1, by rw [h.1.1]; exact h.2.2⟩)
      · exact ((iht.conseq (fun _ _ h => ⟨Or.inr h.1,
            (ProgramDenotation.LosslessAt.of_bind h.2.1).1,
            (ProgramDenotation.LosslessAt.of_bind h.2.2).1⟩) (fun _ _ h => h)).strengthen
          (fun _ _ h => ⟨(ProgramDenotation.LosslessAt.of_bind h.2.1).2,
            (ProgramDenotation.LosslessAt.of_bind h.2.2).2⟩)).conseq
          (fun _ _ h => h) (fun _ _ h => ⟨h.1, h.2.1, h.2.2⟩)
      · exact hexit.conseq (fun _ _ h => ⟨h.2, h.1.2⟩) (fun _ _ h => h)

end Upto

/-- A Hoare triple about a procedure, as the support of its runs. -/
theorem hoareProc.satisfies {sig : ProcedureSignature}
    {P : sig.ParamType → VariableAssignment → Prop} {p : Procedure sig}
    {B : sig.ret → VariableAssignment → Prop} (h : hoareProc P p B) {a : sig.ParamType}
    {g : VariableAssignment} (hP : P a g) :
    (procedureDenotation p a g).satisfies fun r => B r.1 r.2 := by
  intro u hu
  by_contra hB
  have h0 := SubProbability.ofEvent_eq_zero_of_subset (Set.singleton_subset_iff.mpr hB)
    (h a g hP)
  have hfin : (procedureDenotation p a g).1 {u} ≠ ⊤ :=
    (((MeasureTheory.measure_mono (Set.subset_univ _)).trans
      (procedureDenotation p a g).2.1).trans_lt ENNReal.one_lt_top).ne
  rw [SubProbability.ofEvent, ENNReal.toNNReal_eq_zero_iff] at h0
  exact hu (h0.resolve_right hfin)

/-- A lossless procedure is lossless from every state. -/
theorem Procedure.IsLossless.losslessAt {sig : ProcedureSignature} {p : Procedure sig}
    (h : p.IsLossless) (a : sig.ParamType) (g : VariableAssignment) :
    (procedureDenotation p a).LosslessAt g := by
  have h1 := h a g
  rw [ProgramDenotation.LosslessAt, SubProbability.mass_eq_expected]
  exact h1

section Rule

variable {Ω : Type} (L : Lens Ω VariableAssignment)

/-- **The up-to-bad abstract call rule** (EasyCrypt's `call (: bad, invP, invQ)` on an abstract
procedure, `equivF_abs_upto` in `src/phl/ecPhlFun.ml`), for an adversary given as a procedure
with holes:

```
  A lossless with the two instantiations of its oracles                      (EC: `islossless A`)
  equiv[ o₁ ~ o₂ : !bad{2} ∧ ={arg} ∧ ={glob} ∧ invP
                 ==> if bad{2} then invQ else ={res} ∧ ={glob} ∧ invP ]      (per oracle)
  ∀ &2, bad{2} → hoare[ o₁ : invQ ==> invQ ]                                  (per oracle)
  ∀ &1, hoare[ o₂ : bad ∧ invQ ==> bad ∧ invQ ]                               (per oracle)
  ──────────────────────────────────────────────────────────────────────────────────────────
  equiv[ A(o₁) ~ A(o₂) : if bad{2} then invQ else ={arg} ∧ ={glob} ∧ invP
                       ==> if bad{2} then invQ else ={res} ∧ ={glob} ∧ invP ]
```

`bad`, `invP`, `invQ` read the oracle region `L` (EasyCrypt rejects invariants on `glob A`);
`={glob}` is agreement on a region `F` containing `A`'s footprint, outside `L`.  EasyCrypt asks
the oracles to be lossless after the bad event (its `phoare … = 1`); here the adversary's
losslessness is asked with the two instantiations directly. -/
theorem prhlProc_abstract_call_upto {holes : HoleSigs} {sig : ProcedureSignature}
    (inst₁ inst₂ : holes.Instantiation) (A : ProcedureWithHoles holes sig)
    (F : Footprint VariableAssignment) (hAF : FVP.fvP_proc A ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (bad : Ω → Prop) (I Q : Ω → Ω → Prop)
    (hll₁ : (A.instantiate inst₁).IsLossless) (hll₂ : (A.instantiate inst₂).IsLossless)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ syncInv L F I bad g₁ g₂)
        (inst₁.lookup n) (inst₂.lookup n)
        (fun r₁ g₁ r₂ g₂ => badInv L bad Q g₁ g₂ ∨ (r₁ = r₂ ∧ syncInv L F I bad g₁ g₂)))
    (hQ₁ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (ω₂ : Ω), bad ω₂ →
      hoareProc (fun _ g => Q (L.get g) ω₂) (inst₁.lookup n) (fun _ g => Q (L.get g) ω₂))
    (hQ₂ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (ω₁ : Ω),
      hoareProc (fun _ g => bad (L.get g) ∧ Q ω₁ (L.get g)) (inst₂.lookup n)
        (fun _ g => bad (L.get g) ∧ Q ω₁ (L.get g))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => badInv L bad Q g₁ g₂ ∨ (a₁ = a₂ ∧ syncInv L F I bad g₁ g₂))
      (A.instantiate inst₁) (A.instantiate inst₂)
      (fun r₁ g₁ r₂ g₂ => badInv L bad Q g₁ g₂ ∨ (r₁ = r₂ ∧ syncInv L F I bad g₁ g₂)) := by
  have hdisj : FVP.fvP_proc A ≤ (L.footprint)ᶜ := hAF.trans hFL
  have hconf : ConfinedP (fvP_proc A) A.body :=
    confinedP_of_fv (fvP_proc A) hc A.body (fvP_stmt_body_le_fvP_proc A)
  have hsQ₁ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₂ : Ω), bad ω₂ → Q (L.get g) ω₂ →
      (procedureDenotation (inst₁.lookup n) a g).satisfies (fun x => Q (L.get x.2) ω₂) :=
    fun n _ _ ω₂ hb hq => (hQ₁ n ω₂ hb).satisfies hq
  have hsQ₂ : ∀ {sig'} (n : HoleIndex holes sig') (a : sig'.ParamType) (g : VariableAssignment)
      (ω₁ : Ω), bad (L.get g) → Q ω₁ (L.get g) →
      (procedureDenotation (inst₂.lookup n) a g).satisfies
        (fun x => bad (L.get x.2) ∧ Q ω₁ (L.get x.2)) :=
    fun n _ _ ω₁ hb hq => (hQ₂ n ω₁).satisfies ⟨hb, hq⟩
  -- the body is lossless where the procedure is
  have hbody : ∀ (inst : holes.Instantiation), (A.instantiate inst).IsLossless →
      ∀ a g, (programDenotation (A.body.instantiate inst)).LosslessAt ⟨g, A.initLocals a⟩ :=
    fun inst hll a g => (SubProbability.lossless_of_bind (hll.losslessAt a g)).1
  intro a₁ a₂
  refine ProgramDenotation.prhl2.case (fun g₁ g₂ => badInv L bad Q g₁ g₂) ?_ ?_
  · -- after the bad event: the two runs, independently
    refine ProgramDenotation.prhl2.product fun g₁ g₂ ⟨_, hb, hq⟩ =>
      ⟨hll₁.losslessAt a₁ g₁, hll₂.losslessAt a₂ g₂, fun x y hx hy => Or.inl ?_⟩
    have hx' : (procedureDenotation (A.instantiate inst₁) a₁ g₁).satisfies
        (fun x => Q (L.get x.2) (L.get g₂)) := by
      rw [procedureDenotation_eq_procWrap_gen]
      exact SubProbability.satisfies_hbind _ fun p hp => SubProbability.satisfies_pure _ _
        (satisfies_inv_of_confined L A hdisj hc inst₁ (fun ω => Q ω (L.get g₂))
          (fun n a g hg => hsQ₁ n a g _ hb hg) A.body hconf ⟨g₁, A.initLocals a₁⟩ hq p hp)
    have hy' : (procedureDenotation (A.instantiate inst₂) a₂ g₂).satisfies
        (fun y => bad (L.get y.2) ∧ Q (L.get x.2) (L.get y.2)) := by
      rw [procedureDenotation_eq_procWrap_gen]
      exact SubProbability.satisfies_hbind _ fun p hp => SubProbability.satisfies_pure _ _
        (satisfies_inv_of_confined L A hdisj hc inst₂ (fun ω => bad ω ∧ Q (L.get x.2) ω)
          (fun n a g hg => hsQ₂ n a g _ hg.1 hg.2) A.body hconf ⟨g₂, A.initLocals a₂⟩
          ⟨hb, hx' x hx⟩ p hp)
    exact hy' y hy
  · -- before it: the synchronized runs of the body, then the return value
    intro g₁ g₂ ⟨hpre, hnb⟩
    obtain ⟨rfl, hs⟩ := hpre.resolve_left hnb
    obtain ⟨μ, hm1, hm2, hsat⟩ := prhl2_body_upto L A inst₁ inst₂ bad Q F I hAF hFL hc
      (fun n a g₁ g₂ h => horacle n a a g₁ g₂ ⟨rfl, h⟩) hsQ₁ hsQ₂ A.body hconf
      ⟨g₁, A.initLocals a₁⟩ ⟨g₂, A.initLocals a₁⟩
      ⟨Or.inr ⟨hs, rfl⟩, hbody inst₁ hll₁ a₁ g₁, hbody inst₂ hll₂ a₁ g₂⟩
    have hret : ∀ ps₁ ps₂, liftRel (syncInv L F I bad) ps₁ ps₂ →
        A.return_val.get ps₁ = A.return_val.get ps₂ :=
      fun ps₁ ps₂ h => reads_equal_of_footprintCompat
        (footprintCompat_globInvF L A F hAF hFL (fun ω₁ ω₂ => I ω₁ ω₂ ∧ ¬ bad ω₂))
        (ProgramDenotation.inFootprint_of_footprint_le (get_return_val_le_fvP_proc A)) h
    refine ⟨μ >>= fun w => pure ((A.return_val.get w.1.2, w.1.2.globals),
                                 (A.return_val.get w.2.2, w.2.2.globals)), ?_, ?_, ?_⟩
    · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
      rw [procedureDenotation_eq_procWrap_gen]
      change (μ >>= fun w => pure (A.return_val.get w.1.2, w.1.2.globals))
          = (programDenotation (A.body.instantiate inst₁))
              ⟨g₁, A.initLocals a₁⟩ >>= fun p => pure (A.return_val.get p.2, p.2.globals)
      rw [← hm1]
      simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    · simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
      rw [procedureDenotation_eq_procWrap_gen]
      change (μ >>= fun w => pure (A.return_val.get w.2.2, w.2.2.globals))
          = (programDenotation (A.body.instantiate inst₂))
              ⟨g₂, A.initLocals a₁⟩ >>= fun p => pure (A.return_val.get p.2, p.2.globals)
      rw [← hm2]
      simp only [SubProbability.bind_assoc', SubProbability.pure_bind]
    · refine SubProbability.satisfies_bind _ (fun w hw => SubProbability.satisfies_pure _ _ ?_)
      rcases hsat w hw with hb | hrel
      · exact Or.inl hb
      · exact Or.inr ⟨hret _ _ hrel, hrel.1⟩

/-! ### Synchronized means equal

With `={glob}` everything outside `L` (`F = L.compl.footprint`) and `invP` equality on `L`,
EasyCrypt's `={glob A} /\ invP` before the bad event is equality of the global states, and the
per-oracle premise can be stated at equal states (`prhlProc_upto_of_eq`). -/

/-- `syncInv` at `F = L.compl.footprint` and `invP` equality: equal states, not bad. -/
theorem syncInv_compl_eq_iff (bad : Ω → Prop) (g₁ g₂ : VariableAssignment) :
    syncInv L L.compl.footprint (· = ·) bad g₁ g₂ ↔ g₁ = g₂ ∧ ¬ bad (L.get g₂) := by
  constructor
  · rintro ⟨hc, he, hb⟩
    exact ⟨L.splitSpace.injective
      (Prod.ext he ((Lens.footprint_touched_getter_eq_iff L.compl _ _).mp hc)), hb⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, rfl, hb⟩

/-- The oracle premise of `prhlProc_abstract_call_upto(_module)` at `F = L.compl.footprint`,
`invP` equality and `invQ` trivial, from equal arguments and states: after the calls, the bad
event, or equal results and states. -/
theorem prhlProc_upto_of_eq {sig' : ProcedureSignature} (bad : Ω → Prop)
    {o₁ o₂ : Procedure sig'}
    (h : prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂ ∧ ¬ bad (L.get g₂)) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => bad (L.get g₂) ∨ (r₁ = r₂ ∧ g₁ = g₂))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ syncInv L L.compl.footprint (· = ·) bad g₁ g₂) o₁ o₂
      (fun r₁ g₁ r₂ g₂ => badInv L bad (fun _ _ => True) g₁ g₂ ∨
        (r₁ = r₂ ∧ syncInv L L.compl.footprint (· = ·) bad g₁ g₂)) := by
  refine prhlProc_conseq h
    (fun a₁ g₁ a₂ g₂ ⟨ha, hs⟩ => ⟨ha, (syncInv_compl_eq_iff L bad g₁ g₂).mp hs⟩)
    (fun r₁ g₁ r₂ g₂ hpost => ?_)
  by_cases hb : bad (L.get g₂)
  · exact Or.inl ⟨hb, trivial⟩
  · rcases hpost with hb' | ⟨hr, hg⟩
    · exact absurd hb' hb
    · exact Or.inr ⟨hr, (syncInv_compl_eq_iff L bad g₁ g₂).mpr ⟨hg, hb⟩⟩

/-- **The up-to-bad abstract call rule for a module** (EasyCrypt's `declare module D <: T {-O}`,
then `call (: bad, invP, invQ)`): `prhlProc_abstract_call_upto` through `D`'s representation.
`D`'s losslessness with the two oracles is EasyCrypt's `islossless` premise (from `D_ll`). -/
theorem prhlProc_abstract_call_upto_module {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    {holes : HoleSigs} (D : Module.Arr T (Module.Proc sig)) (ext : T → holes.Instantiation)
    (hD : Module.Representable D ext) (F : Footprint VariableAssignment)
    (hDF : FVP.fvP D ≤ F) (hFL : F ≤ (L.footprint)ᶜ)
    (hc : ∀ {sig' : ProcedureSignature}, HoleIndex holes sig' → Countable sig'.ParamType)
    (bad : Ω → Prop) (I Q : Ω → Ω → Prop) (O₁ O₂ : T)
    (hll₁ : (Module.app D O₁).procedure.IsLossless)
    (hll₂ : (Module.app D O₂).procedure.IsLossless)
    (horacle : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig'),
      prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ syncInv L F I bad g₁ g₂)
        ((ext O₁).lookup n) ((ext O₂).lookup n)
        (fun r₁ g₁ r₂ g₂ => badInv L bad Q g₁ g₂ ∨ (r₁ = r₂ ∧ syncInv L F I bad g₁ g₂)))
    (hQ₁ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (ω₂ : Ω), bad ω₂ →
      hoareProc (fun _ g => Q (L.get g) ω₂) ((ext O₁).lookup n) (fun _ g => Q (L.get g) ω₂))
    (hQ₂ : ∀ {sig' : ProcedureSignature} (n : HoleIndex holes sig') (ω₁ : Ω),
      hoareProc (fun _ g => bad (L.get g) ∧ Q ω₁ (L.get g)) ((ext O₂).lookup n)
        (fun _ g => bad (L.get g) ∧ Q ω₁ (L.get g))) :
    prhlProc (fun a₁ g₁ a₂ g₂ => badInv L bad Q g₁ g₂ ∨ (a₁ = a₂ ∧ syncInv L F I bad g₁ g₂))
      (Module.app D O₁).procedure (Module.app D O₂).procedure
      (fun r₁ g₁ r₂ g₂ => badInv L bad Q g₁ g₂ ∨ (r₁ = r₂ ∧ syncInv L F I bad g₁ g₂)) := by
  obtain ⟨p, hden, hle⟩ := hD
  have hll : ∀ O : T, (Module.app D O).procedure.IsLossless →
      (p.instantiate (ext O)).IsLossless := fun O h a g => by
    have h1 := h a g
    unfold Procedure.ewp at h1 ⊢
    rwa [hden O a] at h1
  intro a₁ a₂
  rw [hden O₁ a₁, hden O₂ a₂]
  exact prhlProc_abstract_call_upto L (ext O₁) (ext O₂) p F (hle.trans hDF) hFL hc bad I Q
    (hll O₁ hll₁) (hll O₂ hll₂) horacle hQ₁ hQ₂ a₁ a₂

end Rule

end GaudisCrypt
