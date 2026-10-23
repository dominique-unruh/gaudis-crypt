import GaudisCrypt.Logic.PRHL2
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Logic.Judgment

/-!
# pRHL for statements and procedures

The relational judgment on the statements and procedures of the language, EasyCrypt's
`equiv [ c₁ ~ c₂ : P ==> Q ]`: from any two states related by `P`, the two runs can be *coupled*
so that the final states are related by `Q`.  It is the coupling judgment
`ProgramDenotation.prhl2` (`Logic/PRHL2.lean`) at the statements' denotations, so all its rules
apply; this file states the ones the tactics use at the level of statements:

* sequencing (`prhlStmt_seq`), `skip`, consequence, case analysis;
* one-sided tails (`prhlStmt_seq_left`/`_right`): a statement run on one side only, which must
  terminate there — deterministic code (`Stmt.Det`) and lossless samplings are the instances the
  wp driver uses;
* a sampling on both sides, coupled along a function (`prhlStmt_seq_sample`, EC's `rnd f`);
* the synchronized loop rule (`prhlStmt_while`);
* transport along statement equivalences, on either side (what `stmt_inline`/`stmt_split` use);
* procedures (`prhlProc`), the bridge to the statement form, and EC's `byequiv`
  (`Procedure.Pr_eq_of_prhlProc`).
-/

namespace GaudisCrypt

open ProgramDenotation

/-- `equiv[ A ==> B ] { c₁ } ~ { c₂ }`: from states related by `A`, the runs of `c₁` and `c₂` can
be coupled so that the final states are related by `B`. -/
def prhlStmt (A : ProgramState → ProgramState → Prop) (c₁ c₂ : Stmt)
    (B : ProgramState → ProgramState → Prop) : Prop :=
  ProgramDenotation.prhl2 A (programDenotation c₁) (programDenotation c₂) (fun u v => B u.2 v.2)

/-- `equiv[ p₁ ~ p₂ : A ==> B ]`: for all arguments, from globals related by `A`, the runs of the
two procedures can be coupled so that the results and the final globals are related by `B`. -/
def prhlProc {sig₁ sig₂ : ProcedureSignature}
    (A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop)
    (p₁ : Procedure sig₁) (p₂ : Procedure sig₂)
    (B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop) : Prop :=
  ∀ a₁ a₂, ProgramDenotation.prhl2 (fun g₁ g₂ => A a₁ g₁ a₂ g₂) (procedureDenotation p₁ a₁)
    (procedureDenotation p₂ a₂) (fun u v => B u.1 u.2 v.1 v.2)

/-! ## Couplings, generically -/

section Coupling

universe u

/-- A positive-mass point of a subprobability is in its support. -/
theorem SubProbability.mem_support_of_ne_zero {α : Type u} {μ : SubProbability α} {a : α}
    (h : μ.1 {a} ≠ 0) : a ∈ μ.support := by
  have hfin : μ.1 {a} ≠ ⊤ :=
    (((MeasureTheory.measure_mono (Set.subset_univ _)).trans μ.2.1).trans_lt
      ENNReal.one_lt_top).ne
  rw [SubProbability.mem_support_iff]
  change (μ.1 {a}).toNNReal ≠ 0
  exact (ENNReal.toNNReal_ne_zero).mpr ⟨h, hfin⟩

/-- A statement's run, as its expectations: the subprobability is determined by them. -/
theorem SubProbability.marginal_fst_eq {X Y : Type u} {μ : SubProbability (X × Y)}
    {ν : SubProbability X} (h : ∀ F : X → ENNReal, μ.expected (fun x => F x.1) = ν.expected F) :
    (μ >>= fun x => (pure x.1 : SubProbability X)) = ν :=
  SubProbability.ext_of_expected fun F => by rw [SubProbability.expected_map, h]

theorem SubProbability.marginal_snd_eq {X Y : Type u} {μ : SubProbability (X × Y)}
    {ν : SubProbability Y} (h : ∀ F : Y → ENNReal, μ.expected (fun x => F x.2) = ν.expected F) :
    (μ >>= fun x => (pure x.2 : SubProbability Y)) = ν :=
  SubProbability.ext_of_expected fun F => by rw [SubProbability.expected_map, h]

/-- The marginal conditions, as expectations. -/
theorem SubProbability.expected_fst_of_marginal {X Y : Type u} {μ : SubProbability (X × Y)}
    {ν : SubProbability X} (h : (μ >>= fun x => (pure x.1 : SubProbability X)) = ν)
    (F : X → ENNReal) : μ.expected (fun x => F x.1) = ν.expected F := by
  rw [← h, SubProbability.expected_map]

theorem SubProbability.expected_snd_of_marginal {X Y : Type u} {μ : SubProbability (X × Y)}
    {ν : SubProbability Y} (h : (μ >>= fun x => (pure x.2 : SubProbability Y)) = ν)
    (F : Y → ENNReal) : μ.expected (fun x => F x.2) = ν.expected F := by
  rw [← h, SubProbability.expected_map]

/-- An expectation only depends on the function on the support. -/
theorem SubProbability.expected_congr_satisfies {X : Type u} {μ : SubProbability X}
    {P : X → Prop} (hP : μ.satisfies P) {F G : X → ENNReal} (h : ∀ x, P x → F x = G x) :
    μ.expected F = μ.expected G := by
  rw [SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : μ.1 {x} = 0
  · rw [hx, mul_zero, mul_zero]
  · rw [h x (hP x hx)]

/-- Two reads coupled: a point mass. -/
theorem ProgramDenotation.prhl2.getG {α β : Type} {A : ProgramState → ProgramState → Prop}
    {g₁ : Getter α ProgramState} {g₂ : Getter β ProgramState}
    {B : α × ProgramState → β × ProgramState → Prop}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B (g₁.get σ₁, σ₁) (g₂.get σ₂, σ₂)) :
    ProgramDenotation.prhl2 A (ProgramDenotation.get g₁) (ProgramDenotation.get g₂) B := by
  intro σ₁ σ₂ hA
  refine ⟨pure ((g₁.get σ₁, σ₁), (g₂.get σ₂, σ₂)), ?_, ?_,
    SubProbability.satisfies_pure _ _ (h σ₁ σ₂ hA)⟩
  · rw [SubProbability.pure_bind]; rfl
  · rw [SubProbability.pure_bind]; rfl

end Coupling

/-! ## Basic rules -/

section Basic

variable {A A' B B' C : ProgramState → ProgramState → Prop} {c₁ c₂ d₁ d₂ : Stmt}

/-- Consequence: a stronger precondition, a weaker postcondition. -/
theorem prhlStmt_conseq (h : prhlStmt A' c₁ c₂ B') (hA : ∀ σ₁ σ₂, A σ₁ σ₂ → A' σ₁ σ₂)
    (hB : ∀ σ₁ σ₂, B' σ₁ σ₂ → B σ₁ σ₂) : prhlStmt A c₁ c₂ B :=
  ProgramDenotation.prhl2.conseq h hA fun u v => hB u.2 v.2

/-- Strengthening the precondition, the judgment first (as `hoare_pre`). -/
theorem prhlStmt_pre (h : prhlStmt A' c₁ c₂ B) (hA : ∀ σ₁ σ₂, A σ₁ σ₂ → A' σ₁ σ₂) :
    prhlStmt A c₁ c₂ B :=
  prhlStmt_conseq h hA fun _ _ h => h

/-- Weakening the postcondition, the judgment first. -/
theorem prhlStmt_post (h : prhlStmt A c₁ c₂ B') (hB : ∀ σ₁ σ₂, B' σ₁ σ₂ → B σ₁ σ₂) :
    prhlStmt A c₁ c₂ B :=
  prhlStmt_conseq h (fun _ _ h => h) hB

/-- Symmetry: the two sides swapped. -/
theorem prhlStmt.symm (h : prhlStmt A c₁ c₂ B) :
    prhlStmt (fun σ₂ σ₁ => A σ₁ σ₂) c₂ c₁ (fun σ₂ σ₁ => B σ₁ σ₂) :=
  ProgramDenotation.prhl2.symm h

/-- Symmetry, backwards: the judgment with the sides swapped. -/
theorem prhlStmt_of_symm
    (h : prhlStmt (fun σ₂ σ₁ => A σ₁ σ₂) c₂ c₁ (fun σ₂ σ₁ => B σ₁ σ₂)) : prhlStmt A c₁ c₂ B :=
  h.symm

theorem prhlStmt_symm_iff :
    prhlStmt A c₁ c₂ B ↔ prhlStmt (fun σ₂ σ₁ => A σ₁ σ₂) c₂ c₁ (fun σ₂ σ₁ => B σ₁ σ₂) :=
  ⟨prhlStmt.symm, fun h => h.symm⟩

/-- `skip ~ skip`: the precondition implies the postcondition. -/
theorem prhlStmt_skip (h : ∀ σ₁ σ₂, A σ₁ σ₂ → B σ₁ σ₂) :
    prhlStmt A StmtWithHoles.skip StmtWithHoles.skip B := by
  unfold prhlStmt
  simp only [programDenotation, ProgramDenotation.skip]
  exact ProgramDenotation.prhl2.pure_pure fun σ₁ σ₂ hA => h σ₁ σ₂ hA

/-- Sequencing: an intermediate relation `B`.  The second judgment comes first, so that the wp
steps can fill `B`. -/
theorem prhlStmt_seq (h₂ : prhlStmt B d₁ d₂ C) (h₁ : prhlStmt A c₁ c₂ B) :
    prhlStmt A (.seq c₁ d₁) (.seq c₂ d₂) C := by
  unfold prhlStmt
  rw [programDenotation_seq, programDenotation_seq]
  exact ProgramDenotation.prhl2.bind h₁ fun _ _ => h₂

/-- Case analysis on a relation of the initial states. -/
theorem prhlStmt_case (P : ProgramState → ProgramState → Prop)
    (hp : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ P σ₁ σ₂) c₁ c₂ B)
    (hn : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ ¬ P σ₁ σ₂) c₁ c₂ B) : prhlStmt A c₁ c₂ B :=
  ProgramDenotation.prhl2.case P hp hn

/-- An existential in the precondition (EC's `exists*`/`elim*`). -/
theorem prhlStmt_exists_pre {ι : Sort*} {A : ι → ProgramState → ProgramState → Prop}
    (h : ∀ i, prhlStmt (A i) c₁ c₂ B) : prhlStmt (fun σ₁ σ₂ => ∃ i, A i σ₁ σ₂) c₁ c₂ B :=
  ProgramDenotation.prhl2.exists_pre h

/-- A false precondition. -/
theorem prhlStmt_false : prhlStmt (fun _ _ => False) c₁ c₂ B := fun _ _ h => h.elim

end Basic

/-! ## One-sided tails

A statement at the end of one side only, matched against nothing on the other: it must terminate
(the other side does nothing, so the coupling has to pair *every* run of it with the other
side's final state), and the postcondition must hold on all its outcomes.  Deterministic code and
lossless samplings are the instances; EC's `wp` and `rnd{1}`. -/

section OneSided

/-- A program run on the left only: lossless where the precondition holds, and the postcondition
on all its outcomes.  (`ProgramDenotation.prhl2.kill_left`, with losslessness only where it is
needed.) -/
theorem ProgramDenotation.prhl2.kill_left' {s₁ s₂ : Type 1} {A : s₁ → s₂ → Prop}
    {p₀ : ProgramDenotation s₁ Unit} {B : Unit × s₁ → Unit × s₂ → Prop}
    (h : ∀ σ₁ σ₂, A σ₁ σ₂ →
      p₀.wp (fun _ => 1) σ₁ = 1 ∧ (p₀ σ₁).satisfies (fun u => B u ((), σ₂))) :
    ProgramDenotation.prhl2 A p₀ (pure ()) B := by
  intro σ₁ σ₂ hA
  obtain ⟨hloss, hsupp⟩ := h σ₁ σ₂ hA
  refine ⟨(p₀ σ₁) >>= fun u => pure (u, ((), σ₂)), ?_, ?_, ?_⟩
  · refine SubProbability.ext_of_expected (fun F => ?_)
    rw [SubProbability.expected_map, SubProbability.expected_bind]
    refine SubProbability.expected_congr _ (fun u => ?_)
    rw [expected_pure]
  · refine SubProbability.ext_of_expected (fun F => ?_)
    have hmass1 : (p₀ σ₁).1 Set.univ = 1 := by
      rw [← MeasureTheory.lintegral_one]; exact hloss
    rw [SubProbability.expected_map, SubProbability.expected_bind]
    simp only [expected_pure]
    change (p₀ σ₁).expected (fun _ => F ((), σ₂)) = ((pure () : ProgramDenotation s₂ Unit)
        σ₂).expected F
    rw [show ((pure () : ProgramDenotation s₂ Unit) σ₂) = (pure ((), σ₂) : SubProbability (Unit ×
        s₂)) from rfl, expected_pure]
    change ∫⁻ _, F ((), σ₂) ∂(p₀ σ₁).1 = F ((), σ₂)
    rw [MeasureTheory.lintegral_const, hmass1, mul_one]
  · exact SubProbability.satisfies_bind (p₀ σ₁) (fun u hu =>
      SubProbability.satisfies_pure _ _ (hsupp u hu))

variable {A B : ProgramState → ProgramState → Prop} {s₁ s₂ d : Stmt}

/-- **One-sided tail, left**: `d` at the end of the left side, nothing on the right. -/
theorem prhlStmt_seq_left
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      (programDenotation d).wp (fun _ => 1) σ₁ = 1 ∧
        (programDenotation d σ₁).satisfies fun u => B u.2 σ₂) :
    prhlStmt A (.seq s₁ d) s₂ B := by
  unfold prhlStmt
  rw [programDenotation_seq, ← ProgramDenotation.bind_pure (programDenotation s₂)]
  refine ProgramDenotation.prhl2.bind h fun _ x₂ => ?_
  obtain ⟨⟩ := x₂
  exact ProgramDenotation.prhl2.kill_left' fun σ₁ σ₂ hM => hM

/-- **One-sided tail, right**: the mirror of `prhlStmt_seq_left`. -/
theorem prhlStmt_seq_right
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      (programDenotation d).wp (fun _ => 1) σ₂ = 1 ∧
        (programDenotation d σ₂).satisfies fun v => B σ₁ v.2) :
    prhlStmt A s₁ (.seq s₂ d) B := by
  have h' : prhlStmt (fun σ₂ σ₁ => A σ₁ σ₂) s₂ s₁ fun σ₂ σ₁ =>
      (programDenotation d).wp (fun _ => 1) σ₂ = 1 ∧
        (programDenotation d σ₂).satisfies fun v => B σ₁ v.2 := h.symm
  exact (prhlStmt_seq_left (B := fun σ₂ σ₁ => B σ₁ σ₂) h').symm

/-- A deterministic statement runs as a point mass. -/
theorem Stmt.Det.denotation {d : Stmt} {upd : ProgramState → ProgramState} (hd : Stmt.Det d upd)
    (σ : ProgramState) : programDenotation d σ = pure ((), upd σ) :=
  SubProbability.ext_of_expected fun F => by
    rw [expected_pure]
    exact hd F σ

/-- **Deterministic tail, left** (`Stmt.Det`): the postcondition after the update. -/
theorem prhlStmt_seq_det_left {upd : ProgramState → ProgramState} (hd : Stmt.Det d upd)
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ => B (upd σ₁) σ₂) : prhlStmt A (.seq s₁ d) s₂ B := by
  refine prhlStmt_seq_left (prhlStmt_post h fun σ₁ σ₂ hB => ⟨?_, ?_⟩)
  · rw [hd]
  · rw [hd.denotation]
    exact SubProbability.satisfies_pure _ _ hB

/-- **Deterministic tail, right**. -/
theorem prhlStmt_seq_det_right {upd : ProgramState → ProgramState} (hd : Stmt.Det d upd)
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ => B σ₁ (upd σ₂)) : prhlStmt A s₁ (.seq s₂ d) B := by
  refine prhlStmt_seq_right (prhlStmt_post h fun σ₁ σ₂ hB => ⟨?_, ?_⟩)
  · rw [hd]
  · rw [hd.denotation]
    exact SubProbability.satisfies_pure _ _ hB

/-- A sampling's run: draw, then write. -/
theorem programDenotation_sample_apply {α : Type} (x : Setter α ProgramState)
    (e : Getter (SubProbability α) ProgramState) (σ : ProgramState) :
    programDenotation (StmtWithHoles.sample x e) σ
      = (e.get σ).hbind fun a => pure ((), x.set a σ) :=
  SubProbability.ext_of_expected fun F => by
    rw [SubProbability.expected_hbind]
    have := congrFun (Stmt.ewp_sample x e (fun σ' => F ((), σ'))) σ
    simp only [Stmt.ewp, ProgramDenotation.wp] at this
    simp only [expected_pure]
    exact this

/-- **Sampling on the left only** (EC's `rnd{1}`): a lossless distribution, and the
postcondition for every value in its support. -/
theorem prhlStmt_seq_sample_left {α : Type} {x : Setter α ProgramState}
    {e : Getter (SubProbability α) ProgramState}
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      (e.get σ₁).expected (fun _ => 1) = 1 ∧ ∀ a ∈ (e.get σ₁).support, B (x.set a σ₁) σ₂) :
    prhlStmt A (.seq s₁ (.sample x e)) s₂ B := by
  refine prhlStmt_seq_left (prhlStmt_post h fun σ₁ σ₂ hB => ⟨?_, ?_⟩)
  · have := congrFun (Stmt.ewp_sample x e (fun _ => 1)) σ₁
    simp only [Stmt.ewp] at this
    rw [this, hB.1]
  · rw [programDenotation_sample_apply]
    exact SubProbability.satisfies_hbind _ fun a ha =>
      SubProbability.satisfies_pure _ _ (hB.2 a (SubProbability.mem_support_of_ne_zero ha))

/-- **Sampling on the right only** (EC's `rnd{2}`). -/
theorem prhlStmt_seq_sample_right {α : Type} {x : Setter α ProgramState}
    {e : Getter (SubProbability α) ProgramState}
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      (e.get σ₂).expected (fun _ => 1) = 1 ∧ ∀ a ∈ (e.get σ₂).support, B σ₁ (x.set a σ₂)) :
    prhlStmt A s₁ (.seq s₂ (.sample x e)) B := by
  have h' := (prhlStmt_seq_sample_left (B := fun σ₂ σ₁ => B σ₁ σ₂) h.symm)
  exact h'.symm

end OneSided

/-! ## Two-sided sampling (EC's `rnd f`) -/

section Sample

variable {A B : ProgramState → ProgramState → Prop} {s₁ s₂ : Stmt}

/-- **Coupled samplings**: the two draws coupled along `f` (which may depend on the two states
before the draws), which must push the left distribution to the right one; the postcondition
for every left value in the support, paired with its image. -/
theorem prhlStmt_seq_sample {α β : Type} {x₁ : Setter α ProgramState} {x₂ : Setter β ProgramState}
    {e₁ : Getter (SubProbability α) ProgramState} {e₂ : Getter (SubProbability β) ProgramState}
    (f : ProgramState → ProgramState → α → β)
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ =>
      ((e₁.get σ₁ >>= fun a => pure (f σ₁ σ₂ a)) = e₂.get σ₂) ∧
        ∀ a ∈ (e₁.get σ₁).support, B (x₁.set a σ₁) (x₂.set (f σ₁ σ₂ a) σ₂)) :
    prhlStmt A (.seq s₁ (.sample x₁ e₁)) (.seq s₂ (.sample x₂ e₂)) B := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ h
  intro σ₁ σ₂ ⟨hf, hB⟩
  refine ⟨(e₁.get σ₁).hbind fun a => pure (((), x₁.set a σ₁), ((), x₂.set (f σ₁ σ₂ a) σ₂)),
    ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [programDenotation_sample_apply, SubProbability.expected_hbind,
      SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [programDenotation_sample_apply, SubProbability.expected_hbind,
      SubProbability.expected_hbind, ← hf, SubProbability.expected_bind]
    simp only [expected_pure]
  · exact SubProbability.satisfies_hbind _ fun a ha =>
      SubProbability.satisfies_pure _ _ (hB a (SubProbability.mem_support_of_ne_zero ha))

/-! ### Pushing a distribution along a function

The first conjunct `prhlStmt_seq_sample` leaves: the coupling function pushes the left
distribution to the right one. -/

/-- The identity coupling. -/
@[simp] theorem SubProbability.bind_pure_id {α : Type} (μ : SubProbability α) :
    (μ >>= fun a => (pure a : SubProbability α)) = μ :=
  SubProbability.bind_pure μ

/-- A bijection pushes the uniform distribution to itself. -/
theorem SubProbability.uniform_bind_pure_bijective {α : Type} [Fintype α] [Nonempty α]
    {f : α → α} (hf : Function.Bijective f) :
    (SubProbability.uniform >>= fun a => (pure (f a) : SubProbability α))
      = SubProbability.uniform :=
  SubProbability.ext_of_expected fun F => by
    rw [SubProbability.expected_map, uniform_expected, uniform_expected]
    exact Equiv.sum_comp (Equiv.ofBijective f hf) (fun x => F x / Fintype.card α)

/-- Negation pushes the uniform coin to itself (EC's `rnd (fun b => !b)`). -/
@[simp] theorem SubProbability.uniform_bind_not :
    (SubProbability.uniform >>= fun b => (pure (!b) : SubProbability Bool))
      = SubProbability.uniform :=
  SubProbability.uniform_bind_pure_bijective (Function.Involutive.bijective Bool.not_not)

/-- Xor with a constant pushes the uniform coin to itself. -/
@[simp] theorem SubProbability.uniform_bind_xor (c : Bool) :
    (SubProbability.uniform >>= fun b => (pure (b ^^ c) : SubProbability Bool))
      = SubProbability.uniform :=
  SubProbability.uniform_bind_pure_bijective
    (Function.Involutive.bijective fun b => by cases b <;> cases c <;> rfl)

/-- The uniform distribution is lossless (the side condition of a one-sided sampling). -/
@[simp] theorem SubProbability.uniform_expected_one {α : Type} [Fintype α] [Nonempty α] :
    (SubProbability.uniform : SubProbability α).expected (fun _ => 1) = 1 := by
  rw [uniform_expected, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_div_cancel (by simp) (ENNReal.natCast_ne_top _)

/-- A translation pushes the uniform distribution on a group to itself. -/
@[simp] theorem SubProbability.uniform_bind_add_left {G : Type} [AddGroup G] [Fintype G]
    [Nonempty G] (m : G) :
    (SubProbability.uniform >>= fun a => (pure (m + a) : SubProbability G))
      = SubProbability.uniform :=
  SubProbability.uniform_bind_pure_bijective (add_right_injective m).bijective_of_finite

/-- A translation on the right pushes the uniform distribution on a group to itself. -/
@[simp] theorem SubProbability.uniform_bind_add_right {G : Type} [AddGroup G] [Fintype G]
    [Nonempty G] (m : G) :
    (SubProbability.uniform >>= fun a => (pure (a + m) : SubProbability G))
      = SubProbability.uniform :=
  SubProbability.uniform_bind_pure_bijective (add_left_injective m).bijective_of_finite

end Sample

/-! ## Loops -/

section While

variable {I B : ProgramState → ProgramState → Prop} {c₁ c₂ : Getter Bool ProgramState}
  {b₁ b₂ : Stmt}

/-- **Synchronized loops**: under the invariant the guards agree, and the bodies keep the
invariant; on exit, the invariant and the (common) guard false. -/
theorem prhlStmt_while (hg : ∀ σ₁ σ₂, I σ₁ σ₂ → c₁.get σ₁ = c₂.get σ₂)
    (hb : prhlStmt (fun σ₁ σ₂ => I σ₁ σ₂ ∧ c₁.get σ₁ = true) b₁ b₂ I) :
    prhlStmt I (.while c₁ b₁) (.while c₂ b₂) fun σ₁ σ₂ => I σ₁ σ₂ ∧ c₁.get σ₁ = false := by
  unfold prhlStmt
  simp only [programDenotation]
  refine ProgramDenotation.prhl2.while_loop
    (PostC := fun b σ₁ σ₂ => I σ₁ σ₂ ∧ c₁.get σ₁ = b) ?_ hb
  refine ProgramDenotation.prhl2.getG fun σ₁ σ₂ hI => ⟨?_, hI, rfl⟩
  exact hg σ₁ σ₂ hI

/-- The loop rule at the end of both sides, as the tactic applies it: the body keeps `I`, `I`
and the guard false give `B`, and the code before the loops establishes `I`. -/
theorem prhlStmt_seq_while {A : ProgramState → ProgramState → Prop} {s₁ s₂ : Stmt}
    (hg : ∀ σ₁ σ₂, I σ₁ σ₂ → c₁.get σ₁ = c₂.get σ₂)
    (hb : prhlStmt (fun σ₁ σ₂ => I σ₁ σ₂ ∧ c₁.get σ₁ = true) b₁ b₂ I)
    (hexit : ∀ σ₁ σ₂, I σ₁ σ₂ → c₁.get σ₁ = false → B σ₁ σ₂)
    (hpre : prhlStmt A s₁ s₂ I) :
    prhlStmt A (.seq s₁ (.while c₁ b₁)) (.seq s₂ (.while c₂ b₂)) B :=
  prhlStmt_seq (prhlStmt_post (prhlStmt_while hg hb) fun σ₁ σ₂ h => hexit σ₁ σ₂ h.1 h.2) hpre

end While

/-! ## Conditionals -/

section If

variable {A B : ProgramState → ProgramState → Prop} {c₁ c₂ : Getter Bool ProgramState}
  {t₁ t₂ e₁ e₂ : Stmt}

/-- **Synchronized conditionals**: the guards agree, and the branches are related. -/
theorem prhlStmt_if (hg : ∀ σ₁ σ₂, A σ₁ σ₂ → c₁.get σ₁ = c₂.get σ₂)
    (ht : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ c₁.get σ₁ = true) t₁ t₂ B)
    (he : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ c₁.get σ₁ = false) e₁ e₂ B) :
    prhlStmt A (.ifThenElse c₁ t₁ e₁) (.ifThenElse c₂ t₂ e₂) B := by
  unfold prhlStmt
  simp only [programDenotation]
  refine ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ A u.2 v.2 ∧ c₁.get u.2 = u.1)
    (ProgramDenotation.prhl2.getG fun σ₁ σ₂ hA => ⟨hg σ₁ σ₂ hA, hA, rfl⟩) fun b₁ b₂ => ?_
  intro σ₁ σ₂ ⟨hb, hA, hc⟩
  subst hb
  cases b₁
  · exact he σ₁ σ₂ ⟨hA, hc⟩
  · exact ht σ₁ σ₂ ⟨hA, hc⟩

/-- A conditional runs one of its branches. -/
theorem programDenotation_ifThenElse_apply (c : Getter Bool ProgramState) (t e : Stmt)
    (σ : ProgramState) :
    programDenotation (StmtWithHoles.ifThenElse c t e) σ
      = if c.get σ then programDenotation t σ else programDenotation e σ :=
  SubProbability.ext_of_expected fun F => by
    have := congrFun (Stmt.ewp_ifThenElse c t e (fun σ' => F ((), σ'))) σ
    simp only [Stmt.ewp, ProgramDenotation.wp] at this
    rw [this]
    split <;> rfl

/-- **A conditional on the left only** (EC's `if{1}`): each branch against the right side. -/
theorem prhlStmt_if_left {s : Stmt} (ht : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ c₁.get σ₁ = true) t₁ s B)
    (he : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ c₁.get σ₁ = false) e₁ s B) :
    prhlStmt A (.ifThenElse c₁ t₁ e₁) s B := by
  intro σ₁ σ₂ hA
  have hd := programDenotation_ifThenElse_apply c₁ t₁ e₁ σ₁
  cases hc : c₁.get σ₁
  · rw [hc] at hd
    simp only [Bool.false_eq_true, if_false] at hd
    rw [hd]
    exact he σ₁ σ₂ ⟨hA, hc⟩
  · rw [hc] at hd
    simp only [if_true] at hd
    rw [hd]
    exact ht σ₁ σ₂ ⟨hA, hc⟩

/-- **A conditional on the right only** (EC's `if{2}`). -/
theorem prhlStmt_if_right {s : Stmt}
    (ht : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ c₂.get σ₂ = true) s t₂ B)
    (he : prhlStmt (fun σ₁ σ₂ => A σ₁ σ₂ ∧ c₂.get σ₂ = false) s e₂ B) :
    prhlStmt A s (.ifThenElse c₂ t₂ e₂) B :=
  (prhlStmt_if_left (A := fun σ₂ σ₁ => A σ₁ σ₂) (B := fun σ₂ σ₁ => B σ₁ σ₂) ht.symm he.symm).symm

end If

/-! ## Judgments about equivalent statements

Along `s.EquivInLens s' l`, a judgment about `s` on one side is the judgment about `s'` with the
conditions read through `l` on that side: what `stmt_inline` and `stmt_split` use, per side. -/

section Transport

variable {A A' B B' : ProgramState → ProgramState → Prop}

/-- Transport on the left side, the conditions given up to an equation (as the inliner cleans
them). -/
theorem prhlStmt_of_equivInLens_left {s s' t : Stmt} {l : Lens ProgramState ProgramState}
    (h : s.EquivInLens s' l) (hA : (fun τ σ => A (l.get τ) σ) = A')
    (hB : (fun τ σ => B (l.get τ) σ) = B') (h' : prhlStmt A' s' t B') : prhlStmt A s t B := by
  subst hA hB
  have hs : ∀ τ, (programDenotation s' τ).mapState l.get = programDenotation s (l.get τ) :=
    fun τ => by
      have := h ⟨⟩ (l.get τ) τ rfl
      rwa [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty] at this
  intro σ₁ σ₂ hA
  have hτ : l.get (l.set σ₁ σ₁) = σ₁ := l.set_get σ₁ σ₁
  obtain ⟨μ, hm1, hm2, hsat⟩ := h' (l.set σ₁ σ₁) σ₂ (show A _ σ₂ by rw [hτ]; exact hA)
  refine ⟨μ >>= fun x => pure ((x.1.1, l.get x.1.2), x.2), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map]
    rw [SubProbability.expected_fst_of_marginal hm1 (fun u => F (u.1, l.get u.2)),
      ← SubProbability.expected_mapState l.get _ F, hs, hτ]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map]
    exact SubProbability.expected_snd_of_marginal hm2 F
  · exact SubProbability.satisfies_bind _ fun x hx => SubProbability.satisfies_pure _ _ (hsat x hx)

/-- Transport on the right side. -/
theorem prhlStmt_of_equivInLens_right {s t t' : Stmt} {l : Lens ProgramState ProgramState}
    (h : t.EquivInLens t' l) (hA : (fun σ τ => A σ (l.get τ)) = A')
    (hB : (fun σ τ => B σ (l.get τ)) = B') (h' : prhlStmt A' s t' B') : prhlStmt A s t B := by
  subst hA hB
  exact (prhlStmt_of_equivInLens_left (A := fun σ₂ σ₁ => A σ₁ σ₂)
    (B := fun σ₂ σ₁ => B σ₁ σ₂) h rfl rfl h'.symm).symm

/-- Transport on the left, without renaming. -/
theorem prhlStmt_of_equiv_left {s s' t : Stmt} (h : s.Equiv s') (h' : prhlStmt A s' t B) :
    prhlStmt A s t B :=
  prhlStmt_of_equivInLens_left h rfl rfl h'

/-- Transport on the right, without renaming. -/
theorem prhlStmt_of_equiv_right {s t t' : Stmt} (h : t.Equiv t') (h' : prhlStmt A s t' B) :
    prhlStmt A s t B :=
  prhlStmt_of_equivInLens_right h rfl rfl h'

end Transport

/-! ## Procedures -/

section Proc

/-- A call statement's run: the callee's, its result written to `x` and its globals kept. -/
theorem programDenotation_call_apply {sig : ProcedureSignature} (x : Setter sig.ret ProgramState)
    (p : Procedure sig) (args : Getter sig.ParamType ProgramState) (σ : ProgramState) :
    programDenotation (Stmt.call x p args) σ
      = (procedureDenotation p (args.get σ) σ.globals).hbind fun r =>
          pure ((), x.set r.1 (ProgramState.globalL.set r.2 σ)) :=
  SubProbability.ext_of_expected fun F => by
    have := congrFun (Stmt.ewp_call x p args (fun σ' => F ((), σ'))) σ
    simp only [Stmt.ewp, ProgramDenotation.wp, Procedure.ewp] at this
    rw [SubProbability.expected_hbind]
    simp only [expected_pure]
    exact this

variable {sig₁ sig₂ : ProcedureSignature}
  {A : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
  {p₁ : Procedure sig₁} {p₂ : Procedure sig₂}
  {B : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}

/-- **From a procedure judgment to a statement judgment**: the procedures' judgment is the one
about the two call statements `res <- call pᵢ (args)`, the arguments in local slots `argsLᵢ` and
the results in local slots `resLᵢ` (`phoareProc_as_phoareStmt` for pRHL). -/
theorem prhlProc_of_prhlStmt (resL₁ : Lens sig₁.ret VariableAssignment)
    (argsL₁ : Lens sig₁.ParamType VariableAssignment) (resL₂ : Lens sig₂.ret VariableAssignment)
    (argsL₂ : Lens sig₂.ParamType VariableAssignment)
    (h : prhlStmt
      (fun σ₁ σ₂ => A (argsL₁.get σ₁.locals) σ₁.globals (argsL₂.get σ₂.locals) σ₂.globals)
      (Stmt.call resL₁.intoLocal p₁ argsL₁.intoLocal)
      (Stmt.call resL₂.intoLocal p₂ argsL₂.intoLocal)
      (fun σ₁ σ₂ => B (resL₁.get σ₁.locals) σ₁.globals (resL₂.get σ₂.locals) σ₂.globals)) :
    prhlProc A p₁ p₂ B := by
  intro a₁ a₂ g₁ g₂ hA
  let σ₁ : ProgramState := ⟨g₁, argsL₁.set a₁ VariableAssignment.init⟩
  let σ₂ : ProgramState := ⟨g₂, argsL₂.set a₂ VariableAssignment.init⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ₁ σ₂ (by simpa only [σ₁, σ₂, Lens.set_get] using hA)
  refine ⟨μ >>= fun x => pure ((resL₁.get x.1.2.locals, x.1.2.globals),
    (resL₂.get x.2.2.locals, x.2.2.globals)), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map,
      SubProbability.expected_fst_of_marginal hm1 (fun u => F (resL₁.get u.2.locals, u.2.globals)),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
    simp [σ₁, Lens.intoLocal, Lens.chain, ProgramState.localL, ProgramState.globalL, Lens.set_get]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map,
      SubProbability.expected_snd_of_marginal hm2 (fun u => F (resL₂.get u.2.locals, u.2.globals)),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
    simp [σ₂, Lens.intoLocal, Lens.chain, ProgramState.localL, ProgramState.globalL, Lens.set_get]
  · exact SubProbability.satisfies_bind _ fun x hx => SubProbability.satisfies_pure _ _ (hsat x hx)

/-- **EC's `byequiv`, for expectations**: expectations that agree on related outcomes are equal. -/
theorem Procedure.ewp_eq_of_prhlProc (h : prhlProc A p₁ p₂ B)
    {F : sig₁.ret → VariableAssignment → ENNReal} {G : sig₂.ret → VariableAssignment → ENNReal}
    (hFG : ∀ r₁ g₁ r₂ g₂, B r₁ g₁ r₂ g₂ → F r₁ g₁ = G r₂ g₂)
    {a₁ : sig₁.ParamType} {a₂ : sig₂.ParamType} {σ₁ σ₂ : VariableAssignment}
    (hA : A a₁ σ₁ a₂ σ₂) : p₁.ewp a₁ F σ₁ = p₂.ewp a₂ G σ₂ :=
  ProgramDenotation.relE.wp_eq (h a₁ a₂).to_relE (fun _ _ hxy => hFG _ _ _ _ hxy) hA

/-- **EC's `byequiv`**: events that agree on related outcomes have the same probability. -/
theorem Procedure.Pr_eq_of_prhlProc (h : prhlProc A p₁ p₂ B)
    {E₁ : sig₁.ret → VariableAssignment → Prop} {E₂ : sig₂.ret → VariableAssignment → Prop}
    (hE : ∀ r₁ g₁ r₂ g₂, B r₁ g₁ r₂ g₂ → (E₁ r₁ g₁ ↔ E₂ r₂ g₂))
    {a₁ : sig₁.ParamType} {a₂ : sig₂.ParamType} {σ₁ σ₂ : VariableAssignment}
    (hA : A a₁ σ₁ a₂ σ₂) : p₁.Pr a₁ σ₁ E₁ = p₂.Pr a₂ σ₂ E₂ := by
  refine ENNReal.coe_injective ?_
  rw [Procedure.Pr_eq_ewp, Procedure.Pr_eq_ewp]
  exact Procedure.ewp_eq_of_prhlProc h (fun r₁ g₁ r₂ g₂ hB => by rw [hE r₁ g₁ r₂ g₂ hB]) hA

/-- **EC's `byequiv`, one-sided**: if related outcomes in `E₁` are in `E₂`, then `E₁` is at most as
likely as `E₂`. -/
theorem Procedure.Pr_le_of_prhlProc (h : prhlProc A p₁ p₂ B)
    {E₁ : sig₁.ret → VariableAssignment → Prop} {E₂ : sig₂.ret → VariableAssignment → Prop}
    (hE : ∀ r₁ g₁ r₂ g₂, B r₁ g₁ r₂ g₂ → E₁ r₁ g₁ → E₂ r₂ g₂)
    {a₁ : sig₁.ParamType} {a₂ : sig₂.ParamType} {σ₁ σ₂ : VariableAssignment}
    (hA : A a₁ σ₁ a₂ σ₂) : p₁.Pr a₁ σ₁ E₁ ≤ p₂.Pr a₂ σ₂ E₂ := by
  refine ENNReal.coe_le_coe.mp ?_
  rw [Procedure.Pr_eq_ewp, Procedure.Pr_eq_ewp]
  refine ProgramDenotation.rel.wp_le (h a₁ a₂).to_relE.1 (fun x y hxy => ?_) hA
  by_cases h₁ : E₁ x.1 x.2
  · simp [indicatorE, h₁, hE _ _ _ _ hxy h₁]
  · simp [indicatorE, h₁]

/-- **Calls on both sides, with a procedure judgment** (EC's `call (_ : P ==> Q)`): the callees'
runs coupled by `h`, from the arguments and globals before the calls; the postcondition for
every results and globals `h` relates, written back. -/
theorem prhlStmt_seq_call (h : prhlProc A p₁ p₂ B) {x₁ : Setter sig₁.ret ProgramState}
    {e₁ : Getter sig₁.ParamType ProgramState} {x₂ : Setter sig₂.ret ProgramState}
    {e₂ : Getter sig₂.ParamType ProgramState} {A' B' : ProgramState → ProgramState → Prop}
    {s₁ s₂ : Stmt}
    (hpre : prhlStmt A' s₁ s₂ fun σ₁ σ₂ => A (e₁.get σ₁) σ₁.globals (e₂.get σ₂) σ₂.globals ∧
      ∀ r₁ g₁ r₂ g₂, B r₁ g₁ r₂ g₂ →
        B' (x₁.set r₁ (ProgramState.globalL.set g₁ σ₁))
          (x₂.set r₂ (ProgramState.globalL.set g₂ σ₂))) :
    prhlStmt A' (.seq s₁ (Stmt.call x₁ p₁ e₁)) (.seq s₂ (Stmt.call x₂ p₂ e₂)) B' := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ hpre
  intro σ₁ σ₂ ⟨hA, hB⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := h (e₁.get σ₁) (e₂.get σ₂) σ₁.globals σ₂.globals hA
  refine ⟨μ >>= fun w => pure (((), x₁.set w.1.1 (ProgramState.globalL.set w.1.2 σ₁)),
    ((), x₂.set w.2.1 (ProgramState.globalL.set w.2.2 σ₂))), ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_fst_of_marginal hm1
      (fun r => F ((), x₁.set r.1 (ProgramState.globalL.set r.2 σ₁))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [SubProbability.expected_map, SubProbability.expected_snd_of_marginal hm2
      (fun r => F ((), x₂.set r.1 (ProgramState.globalL.set r.2 σ₂))),
      programDenotation_call_apply, SubProbability.expected_hbind]
    simp only [expected_pure]
  · exact SubProbability.satisfies_bind _ fun w hw =>
      SubProbability.satisfies_pure _ _ (hB _ _ _ _ (hsat w hw))

/-- **Transitivity** of procedure judgments (game hopping): couplings of `p₁` with `p₂` and of
`p₂` with `p₃` glue along `p₂` (`ProgramDenotation.prhl2.trans`). -/
theorem prhlProc.trans {sig₃ : ProcedureSignature} {p₃ : Procedure sig₃}
    {A₂ : sig₂.ParamType → VariableAssignment → sig₃.ParamType → VariableAssignment → Prop}
    {B₂ : sig₂.ret → VariableAssignment → sig₃.ret → VariableAssignment → Prop}
    (h₁ : prhlProc A p₁ p₂ B) (h₂ : prhlProc A₂ p₂ p₃ B₂) :
    prhlProc (fun a₁ g₁ a₃ g₃ => ∃ a₂ g₂, A a₁ g₁ a₂ g₂ ∧ A₂ a₂ g₂ a₃ g₃) p₁ p₃
      (fun r₁ g₁ r₃ g₃ => ∃ r₂ g₂, B r₁ g₁ r₂ g₂ ∧ B₂ r₂ g₂ r₃ g₃) := by
  intro a₁ a₃ g₁ g₃ ⟨a₂, g₂, hA, hA₂⟩
  obtain ⟨μ, hm1, hm2, hsat⟩ := ((h₁ a₁ a₂).trans (h₂ a₂ a₃)) g₁ g₃ ⟨g₂, hA, hA₂⟩
  exact ⟨μ, hm1, hm2, fun x hx => by
    obtain ⟨y, hy₁, hy₂⟩ := hsat x hx
    exact ⟨y.1, y.2, hy₁, hy₂⟩⟩

/-- Consequence for procedure judgments. -/
theorem prhlProc_conseq
    {A' : sig₁.ParamType → VariableAssignment → sig₂.ParamType → VariableAssignment → Prop}
    {B' : sig₁.ret → VariableAssignment → sig₂.ret → VariableAssignment → Prop}
    (h : prhlProc A' p₁ p₂ B') (hA : ∀ a₁ g₁ a₂ g₂, A a₁ g₁ a₂ g₂ → A' a₁ g₁ a₂ g₂)
    (hB : ∀ r₁ g₁ r₂ g₂, B' r₁ g₁ r₂ g₂ → B r₁ g₁ r₂ g₂) : prhlProc A p₁ p₂ B := fun a₁ a₂ =>
  (h a₁ a₂).conseq (fun g₁ g₂ => hA a₁ g₁ a₂ g₂) fun u v => hB u.1 u.2 v.1 v.2

end Proc

/-! ## Abstract procedures (EC's `call (_ : ={glob A})`) -/

/-- **Reflexivity**: any procedure, on equal arguments from equal globals, can be coupled with
itself to equal results and equal globals (EC's `call (_ : true)` on the same code). -/
theorem prhlProc_refl {sig : ProcedureSignature} (p : Procedure sig) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ g₁ = g₂) p p
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ g₁ = g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hg⟩
  subst ha hg
  have h := (ProgramDenotation.prhl2.refl (procedureDenotation p a₁)).conseq
    (A' := fun g₁ g₂ => g₁ = g₂)
    (B' := fun (u v : sig.ret × VariableAssignment) => u.1 = v.1 ∧ u.2 = v.2)
    (fun _ _ h => h) (fun u v h => h ▸ ⟨rfl, rfl⟩)
  exact h g₁ g₁ rfl

/-- **The adversary rule**: a procedure confined to the footprint `R` (on every argument), run
on equal arguments from globals that agree on what it can touch (`R.touched_getter`, EC's
`glob A`), returns equal results and globals that again agree on it (`prhl2_glob`). -/
theorem prhlProc_glob {sig : ProcedureSignature} {p : Procedure sig}
    {R : Footprint VariableAssignment}
    (hp : ∀ a, (procedureDenotation p a).inFootprint R) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ R.touched_getter.get g₁ = R.touched_getter.get g₂)
      p p (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ R.touched_getter.get g₁ = R.touched_getter.get g₂) := by
  intro a₁ a₂ g₁ g₂ ⟨ha, hg⟩
  subst ha
  exact prhl2_glob (hp a₁) g₁ g₂ hg

end GaudisCrypt
