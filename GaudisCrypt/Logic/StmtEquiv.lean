import GaudisCrypt.Logic.Hoare

/-!
# Denotational equivalence of statements

`StmtWithHoles.EquivInLens a b l`: `b`, running on wide states, does what `a` does on the narrow
state `l` projects to.  `StmtWithHoles.Equiv` is the case `l = Lens.id`, plain denotational
equivalence.  The relation is a congruence for the statement formers, and a Hoare triple can be
moved along it (`hoareStmt_iff_of_equivInLens`).

The statement rewriters (`TacticMisc.flattenSeq`, `HoareSplit.splitSeq`, the inliner in
`Inline.lean`) prove their results equivalent to their inputs with these lemmas.
-/

namespace GaudisCrypt

/-! ## Lens helpers -/

/-- Compose a getter with a lens between its containers. -/
def Lens.chainGetter {a : Type u} {s : Type v} {t : Type w} (l : Lens s t) (g : Getter a s) :
    Getter a t where
  get τ := g.get (l.get τ)

/-- Compose a setter with a lens between its containers. -/
def Lens.chainSetter {a : Type u} {s : Type v} {t : Type w} (l : Lens s t) (x : Setter a s) :
    Setter a t where
  set v τ := l.set (x.set v (l.get τ)) τ
  set_set σ u v := by simp [l.set_get, x.set_set, l.set_set]

@[simp] theorem Lens.id_chain {a : Type u} {m : Type v} (y : Lens a m) :
    Lens.chain Lens.id y = y := rfl

@[simp] theorem Lens.chain_id {a : Type u} {m : Type v} (x : Lens a m) :
    Lens.chain x Lens.id = x := rfl

/-- Chaining is associative. -/
theorem Lens.chain_assoc {a : Type u} {b : Type v} {c : Type w} {d : Type w'} (x : Lens c d)
    (y : Lens b c) (z : Lens a b) : (x.chain y).chain z = x.chain (y.chain z) := rfl

/-! ## Denotational equivalence along a lens -/

/-- Push a state map through a denotation's result: `(u, τ) ↦ (u, f τ)`. -/
noncomputable def SubProbability.mapState {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) : SubProbability (α × s) :=
  (fun p => (p.1, f p.2)) <$> μ

/-- `b`, running on the wide state `t`, is denotationally equivalent to `a`, running on the
narrow state `s`, in the lens `l : Lens s t`: from any wide state, running `b` and projecting the
result with `l.get` gives the same subdistribution as running `a` from the projected state.

Nothing is assumed about the part of the wide state that `l` does not see — in particular the
frame of a flattened callee, which the flattened code resets before it reads it. -/
def ProgramDenotation.EquivInLens {s t : Type u} {α : Type v} (a : ProgramDenotation s α)
    (b : ProgramDenotation t α) (l : Lens s t) : Prop :=
  ∀ (sa : s) (sb : t), sa = l.get sb → (b sb).mapState l.get = a sa

/-- The statement-level relation.  `programDenotation` needs a hole-free statement and the
rewrites here leave hole indices untouched, so the instantiation is quantified — the same one on
both sides. -/
def StmtWithHoles.EquivInLens {hCtx : HoleSigs} (a b : StmtWithHoles hCtx)
    (l : Lens ProgramState ProgramState) : Prop :=
  ∀ inst : hCtx.Instantiation,
    (programDenotation (a.instantiate inst)).EquivInLens
      (programDenotation (b.instantiate inst)) l

/-- Denotational equivalence without renaming — what `flattenSeq` proves. -/
abbrev StmtWithHoles.Equiv {hCtx : HoleSigs} (a b : StmtWithHoles hCtx) : Prop :=
  a.EquivInLens b Lens.id

/-! ## The primitives, applied at a state -/

/-- `ProgramDenotation.get` applied at a state — the `Getter` version of
`ProgramDenotation.get_apply` (which is stated for a `Lens`). -/
theorem ProgramDenotation.get_apply' {s : Type u} {a : Type v} (g : Getter a s) (st : s) :
    ProgramDenotation.get g st = pure (g.get st, st) := rfl

/-- `ProgramDenotation.set` applied at a state — the `Setter` version of
`ProgramDenotation.set_apply` (which is stated for a `Lens`). -/
theorem ProgramDenotation.set_apply' {s : Type u} {a : Type v} (x : Setter a s) (v : a)
    (st : s) : ProgramDenotation.set x v st = pure ((), x.set v st) := rfl

/-! ## `EquivInLens` is a congruence

What the flattener needs along the path down to the call it is rewriting. -/

/-- `mapState` spelled out as a `bind`, for rewriting. -/
theorem SubProbability.mapState_eq {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) : μ.mapState f = μ >>= fun q => pure (q.1, f q.2) := rfl

/-- `pure` is equivalent to itself. -/
theorem ProgramDenotation.EquivInLens.pure {s t : Type u} {α : Type v} {l : Lens s t} (a : α) :
    (Pure.pure a : ProgramDenotation s α).EquivInLens (Pure.pure a) l := by
  rintro sa sb rfl
  change ((Pure.pure (a, sb) : SubProbability (α × t))
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s))) = _
  rw [SubProbability.pure_bind]
  rfl

/-- Diverging is equivalent to diverging. -/
theorem ProgramDenotation.EquivInLens.bot {s t : Type u} {α : Type v} {l : Lens s t} :
    (⊥ : ProgramDenotation s α).EquivInLens ⊥ l := by
  rintro sa sb rfl
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

/-- Reading through the composed getter is equivalent to reading through the original one. -/
theorem ProgramDenotation.EquivInLens.get {s t : Type u} {α : Type v} (l : Lens s t)
    (g : Getter α s) :
    (ProgramDenotation.get g).EquivInLens (ProgramDenotation.get (l.chainGetter g)) l := by
  rintro sa sb rfl
  change (ProgramDenotation.get (l.chainGetter g) sb
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s)))
    = ProgramDenotation.get g (l.get sb)
  rw [ProgramDenotation.get_apply', ProgramDenotation.get_apply', SubProbability.pure_bind]
  rfl

/-- Writing through the composed setter is equivalent to writing through the original one. -/
theorem ProgramDenotation.EquivInLens.set {s t : Type u} {α : Type v} (l : Lens s t)
    (x : Setter α s) (v : α) :
    (ProgramDenotation.set x v).EquivInLens (ProgramDenotation.set (l.chainSetter x) v) l := by
  rintro sa sb rfl
  change (ProgramDenotation.set (l.chainSetter x) v sb
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (Unit × s)))
    = ProgramDenotation.set x v (l.get sb)
  rw [ProgramDenotation.set_apply', ProgramDenotation.set_apply', SubProbability.pure_bind]
  simp only [Lens.chainSetter, l.set_get]

/-- A state-blind draw is equivalent to itself. -/
theorem ProgramDenotation.EquivInLens.lift {s t : Type u} {α : Type v} (l : Lens s t)
    (μ : SubProbability α) :
    (μ.toProgramDenotation : ProgramDenotation s α).EquivInLens
      (μ.toProgramDenotation : ProgramDenotation t α) l := by
  rintro sa sb rfl
  change SubProbability.hbind (μ.hbind fun v => (Pure.pure (v, sb) : SubProbability (α × t)))
      (fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s)))
    = μ.hbind fun v => Pure.pure (v, l.get sb)
  rw [SubProbability.hbind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_hbind]

/-- **Bind congruence** — the `seq` case, and the heart of the path congruences.  Note the
continuation hypothesis is over *wide* states, which is exactly what `EquivInLens` provides. -/
theorem ProgramDenotation.EquivInLens.bind {s t : Type u} {α β : Type v} {l : Lens s t}
    {p : ProgramDenotation s α} {q : ProgramDenotation t α}
    {p' : α → ProgramDenotation s β} {q' : α → ProgramDenotation t β}
    (h : p.EquivInLens q l) (h' : ∀ a, (p' a).EquivInLens (q' a) l) :
    (p >>= p').EquivInLens (q >>= q') l := by
  rintro sa sb rfl
  have hfun : (fun r : α × t =>
        (q' r.1 r.2 >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (β × s))))
      = (fun r : α × t => p' r.1 (l.get r.2)) := funext fun r => h' r.1 _ r.2 rfl
  change ((q sb >>= fun r => q' r.1 r.2)
      >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (β × s)))
    = p (l.get sb) >>= fun r => p' r.1 r.2
  rw [SubProbability.bind_assoc, hfun, ← h _ sb rfl]
  change _ = ((q sb >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (α × s)))
      >>= fun r => p' r.1 r.2)
  rw [SubProbability.bind_assoc]
  congr 1; funext r
  rw [SubProbability.pure_bind]

/-- Projecting twice is projecting along the composite. -/
theorem SubProbability.mapState_mapState {α : Type v} {s t u : Type w} (f : u → t) (g : t → s)
    (μ : SubProbability (α × u)) :
    (μ.mapState f).mapState g = μ.mapState (fun x => g (f x)) := by
  change ((μ >>= fun q => Pure.pure (q.1, f q.2)) >>= fun q => Pure.pure (q.1, g q.2))
    = μ >>= fun q => Pure.pure (q.1, g (f q.2))
  rw [SubProbability.bind_assoc]
  congr 1; funext q
  rw [SubProbability.pure_bind]

/-- Equivalences compose: through `l`, then through `m`, is through `m.chain l`. -/
theorem ProgramDenotation.EquivInLens.trans {s t u : Type w} {α : Type v} {l : Lens s t}
    {m : Lens t u} {p : ProgramDenotation s α} {q : ProgramDenotation t α}
    {r : ProgramDenotation u α}
    (h : p.EquivInLens q l) (h' : q.EquivInLens r m) : p.EquivInLens r (m.chain l) := by
  rintro sa su rfl
  change ((r su).mapState (fun x => l.get (m.get x))) = p (l.get (m.get su))
  rw [← SubProbability.mapState_mapState, h' _ su rfl, h _ (m.get su) rfl]

/-- `mapState` is ω-continuous — what the loop congruence needs. -/
theorem SubProbability.mapState_ωScottContinuous {α : Type v} {s t : Type u} (f : t → s) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun μ : SubProbability (α × t) => μ.mapState f) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono =>
    intro μ₁ μ₂ h
    exact SubProbability.bind_mono (fun μ : SubProbability (α × t) => μ)
      (fun _ q => (Pure.pure (q.1, f q.2) : SubProbability (α × s)))
      (fun _ _ hh => hh) (fun _ _ _ => le_rfl) h
  case sup =>
    intro ch
    exact (SubProbability.bind_ωScottContinuous (fun μ : SubProbability (α × t) => μ)
      (fun _ q => (Pure.pure (q.1, f q.2) : SubProbability (α × s)))
      OmegaCompletePartialOrder.ωScottContinuous.const
      OmegaCompletePartialOrder.ωScottContinuous.id).map_ωSup ch

/-- Equivalence passes to ω-suprema of chains — the limit step of the loop congruence. -/
theorem ProgramDenotation.EquivInLens.ωSup {s t : Type u} {α : Type v} {l : Lens s t}
    (chP : OmegaCompletePartialOrder.Chain (ProgramDenotation s α))
    (chQ : OmegaCompletePartialOrder.Chain (ProgramDenotation t α))
    (h : ∀ n, (chP n).EquivInLens (chQ n) l) :
    (OmegaCompletePartialOrder.ωSup chP).EquivInLens (OmegaCompletePartialOrder.ωSup chQ) l := by
  rintro sa sb rfl
  have hQ : (OmegaCompletePartialOrder.ωSup chQ) sb = OmegaCompletePartialOrder.ωSup
      (chQ.map ⟨fun m => m sb, fun _ _ hh => Pi.le_def.mp hh sb⟩) := rfl
  have hP : (OmegaCompletePartialOrder.ωSup chP) (l.get sb) = OmegaCompletePartialOrder.ωSup
      (chP.map ⟨fun m => m (l.get sb), fun _ _ hh => Pi.le_def.mp hh (l.get sb)⟩) := rfl
  rw [hQ, hP, (SubProbability.mapState_ωScottContinuous (α := α) l.get).map_ωSup]
  congr 1
  ext n
  exact h n _ sb rfl

/-- **Loop congruence** (Kleene/ωSup argument again): equivalent conditions and equivalent bodies
give equivalent loops. -/
theorem ProgramDenotation.EquivInLens.while_loop {s t : Type u} {l : Lens s t}
    {cond : ProgramDenotation s Bool} {cond' : ProgramDenotation t Bool}
    {body : ProgramDenotation s Unit} {body' : ProgramDenotation t Unit}
    (hc : cond.EquivInLens cond' l) (hb : body.EquivInLens body' l) :
    (while_loop cond body).EquivInLens (while_loop cond' body') l := by
  let F := while_iteration cond body
  let G := while_iteration cond' body'
  have key : ∀ n : ℕ, ((F^[n] (⊥ : Unit → ProgramDenotation s Unit)) ()).EquivInLens
      ((G^[n] (⊥ : Unit → ProgramDenotation t Unit)) ()) l := by
    intro n
    induction n with
    | zero => exact ProgramDenotation.EquivInLens.bot
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (cond >>= fun b => if b = true then body >>= fun _ => (F^[n] ⊥) ()
                else (Pure.pure () : ProgramDenotation s Unit)).EquivInLens
             (cond' >>= fun b => if b = true then body' >>= fun _ => (G^[n] ⊥) ()
                else (Pure.pure () : ProgramDenotation t Unit)) l
      refine ProgramDenotation.EquivInLens.bind hc fun b => ?_
      by_cases h : b = true
      · simp only [h, if_true]
        exact ProgramDenotation.EquivInLens.bind hb fun _ => ih
      · simp only [h, Bool.false_eq_true, if_false]
        exact ProgramDenotation.EquivInLens.pure ()
  let chainF : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F^[n] ⊥, Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _)⟩
  let chainG : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation t Unit) :=
    ⟨fun n => G^[n] ⊥, Monotone.monotone_iterate_of_le_map G.monotone (OrderBot.bot_le _)⟩
  have hF_at : F.lfp () = OmegaCompletePartialOrder.ωSup
      (chainF.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  have hG_at : G.lfp () = OmegaCompletePartialOrder.ωSup
      (chainG.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  change (F.lfp ()).EquivInLens (G.lfp ()) l
  rw [hF_at, hG_at]
  exact ProgramDenotation.EquivInLens.ωSup _ _ key

/-- Every program is equivalent to itself, in the identity lens. -/
theorem ProgramDenotation.EquivInLens.refl {s : Type u} {α : Type v} (p : ProgramDenotation s α) :
    p.EquivInLens p Lens.id := by
  rintro sa sb rfl
  exact SubProbability.bind_pure _

/-! ### The same, at statement level -/

/-- Sequencing. -/
theorem StmtWithHoles.EquivInLens.seq {hCtx : HoleSigs} {l : Lens ProgramState ProgramState}
    {a b a' b' : StmtWithHoles hCtx} (ha : a.EquivInLens a' l) (hb : b.EquivInLens b' l) :
    (a.seq b).EquivInLens (a'.seq b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  exact ProgramDenotation.EquivInLens.bind (ha inst) fun _ => hb inst

/-- Branching; the condition is re-targeted by composing it with the lens. -/
theorem StmtWithHoles.EquivInLens.ifThenElse {hCtx : HoleSigs}
    {l : Lens ProgramState ProgramState} (c : Getter Bool ProgramState)
    {a b a' b' : StmtWithHoles hCtx} (ha : a.EquivInLens a' l) (hb : b.EquivInLens b' l) :
    (StmtWithHoles.ifThenElse c a b).EquivInLens
      (StmtWithHoles.ifThenElse (l.chainGetter c) a' b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  refine ProgramDenotation.EquivInLens.bind (ProgramDenotation.EquivInLens.get l c) fun bv => ?_
  cases bv
  · simpa using hb inst
  · simpa using ha inst

/-- Looping; the condition is re-targeted by composing it with the lens. -/
theorem StmtWithHoles.EquivInLens.while {hCtx : HoleSigs} {l : Lens ProgramState ProgramState}
    (c : Getter Bool ProgramState) {b b' : StmtWithHoles hCtx} (hb : b.EquivInLens b' l) :
    (StmtWithHoles.while c b).EquivInLens (StmtWithHoles.while (l.chainGetter c) b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  exact ProgramDenotation.EquivInLens.while_loop (ProgramDenotation.EquivInLens.get l c) (hb inst)

/-- Statement equivalences compose — how the flattener's passes are stitched together. -/
theorem StmtWithHoles.EquivInLens.trans {hCtx : HoleSigs} {l m : Lens ProgramState ProgramState}
    {a b c : StmtWithHoles hCtx} (h : a.EquivInLens b l) (h' : b.EquivInLens c m) :
    a.EquivInLens c (m.chain l) :=
  fun inst => (h inst).trans (h' inst)

/-- Reflexivity of the renaming-free relation. -/
theorem StmtWithHoles.Equiv.refl {hCtx : HoleSigs} (a : StmtWithHoles hCtx) : a.Equiv a :=
  fun _ => ProgramDenotation.EquivInLens.refl _

/-- Sequencing is associative, denotationally. -/
theorem StmtWithHoles.Equiv.seq_assoc {hCtx : HoleSigs} (a b c : StmtWithHoles hCtx) :
    ((a.seq b).seq c).Equiv (a.seq (b.seq c)) := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  rw [ProgramDenotation.bind_assoc]
  exact ProgramDenotation.EquivInLens.refl _

/-! ## Deterministic statements -/

/-- An assignment, run at a state: a deterministic write. -/
theorem programDenotation_assign_apply {a : Type} (y : Setter a ProgramState)
    (e : Getter a ProgramState) (τ : ProgramState) :
    programDenotation (StmtWithHoles.assign (h := .empty) y e) τ
      = Pure.pure ((), y.set (e.get τ) τ) := by
  simp only [StmtWithHoles.assign, programDenotation]
  rw [ProgramDenotation.bind_apply, ProgramDenotation.get_apply', SubProbability.pure_bind,
    ProgramDenotation.bind_apply]
  change ((Pure.pure (e.get τ) : SubProbability a).hbind fun v => Pure.pure (v, τ))
      >>= (fun p => ProgramDenotation.set y p.1 p.2) = _
  rw [SubProbability.pure_hbind, SubProbability.pure_bind, ProgramDenotation.set_apply']

/-- An assignment is a read followed by a write. -/
theorem programDenotation_assign {a : Type} (y : Setter a ProgramState)
    (e : Getter a ProgramState) :
    programDenotation (StmtWithHoles.assign (h := .empty) y e)
      = ProgramDenotation.get e >>= fun v => ProgramDenotation.set y v := by
  funext τ
  rw [programDenotation_assign_apply, ProgramDenotation.bind_apply,
    ProgramDenotation.get_apply', SubProbability.pure_bind, ProgramDenotation.set_apply']

/-- `skip` is the identity state map. -/
theorem programDenotation_skip_apply (τ : ProgramState) :
    programDenotation (StmtWithHoles.skip (h := .empty)) τ = Pure.pure ((), τ) := by
  simp only [programDenotation, ProgramDenotation.skip]
  rfl

/-- Sequencing is `bind`. -/
theorem programDenotation_seq (a b : Stmt) :
    programDenotation (a.seq b) = programDenotation a >>= fun _ => programDenotation b := by
  simp only [programDenotation]

/-- Two deterministic statements in sequence: their state maps compose. -/
theorem programDenotation_seq_apply_det {a b : Stmt} {fa fb : ProgramState → ProgramState}
    (ha : ∀ τ, programDenotation a τ = Pure.pure ((), fa τ))
    (hb : ∀ τ, programDenotation b τ = Pure.pure ((), fb τ)) :
    ∀ τ, programDenotation (a.seq b) τ = Pure.pure ((), fb (fa τ)) := by
  intro τ
  rw [programDenotation_seq, ProgramDenotation.bind_apply, ha, SubProbability.pure_bind, hb]

/-! ## At the identity lens

What `flattenSeq` rewrites with (and `StmtWithHoles.Equiv.seq_assoc`, above). -/

/-- A leading `skip` can be dropped. -/
theorem StmtWithHoles.Equiv.skip_seq {hCtx : HoleSigs} (a : StmtWithHoles hCtx) :
    ((StmtWithHoles.skip).seq a).Equiv a := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
  rw [ProgramDenotation.pure_bind]
  exact ProgramDenotation.EquivInLens.refl _

/-- A trailing `skip` can be dropped. -/
theorem StmtWithHoles.Equiv.seq_skip {hCtx : HoleSigs} (a : StmtWithHoles hCtx) :
    (a.seq (StmtWithHoles.skip)).Equiv a := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
  rw [ProgramDenotation.bind_pure]
  exact ProgramDenotation.EquivInLens.refl _

/-- An assignment to `_` does nothing. -/
theorem programDenotation_assign_throwaway {a : Type} (e : Getter a ProgramState) :
    programDenotation (StmtWithHoles.assign (h := .empty) Setter.throwaway e)
      = ProgramDenotation.skip := by
  funext τ
  rw [programDenotation_assign_apply]
  rfl

/-- A leading assignment to `_` can be dropped (a call with no parameters writes its argument
`()` to `_`). -/
theorem StmtWithHoles.Equiv.throwaway_seq {hCtx : HoleSigs} {α : Type} (e : Getter α ProgramState)
    (a : StmtWithHoles hCtx) :
    ((StmtWithHoles.assign Setter.throwaway e).seq a).Equiv a := by
  intro inst
  change (programDenotation ((StmtWithHoles.assign (h := .empty) Setter.throwaway e).seq
    (a.instantiate inst))).EquivInLens _ _
  rw [programDenotation_seq, programDenotation_assign_throwaway, ProgramDenotation.skip,
    ProgramDenotation.pure_bind]
  exact ProgramDenotation.EquivInLens.refl _

/-- A trailing assignment to `_` can be dropped (a call whose result is discarded stores it to
`_`). -/
theorem StmtWithHoles.Equiv.seq_throwaway {hCtx : HoleSigs} {α : Type}
    (a : StmtWithHoles hCtx) (e : Getter α ProgramState) :
    (a.seq (StmtWithHoles.assign Setter.throwaway e)).Equiv a := by
  intro inst
  change (programDenotation ((a.instantiate inst).seq
    (StmtWithHoles.assign (h := .empty) Setter.throwaway e))).EquivInLens _ _
  rw [programDenotation_seq, programDenotation_assign_throwaway, ProgramDenotation.skip,
    ProgramDenotation.bind_pure]
  exact ProgramDenotation.EquivInLens.refl _

/-- Branching, at the identity lens. -/
theorem StmtWithHoles.Equiv.ifThenElse {hCtx : HoleSigs} (c : Getter Bool ProgramState)
    {a b a' b' : StmtWithHoles hCtx} (ha : a.Equiv a') (hb : b.Equiv b') :
    (StmtWithHoles.ifThenElse c a b).Equiv (StmtWithHoles.ifThenElse c a' b') :=
  StmtWithHoles.EquivInLens.ifThenElse c ha hb

/-- Looping, at the identity lens. -/
theorem StmtWithHoles.Equiv.while {hCtx : HoleSigs} (c : Getter Bool ProgramState)
    {b b' : StmtWithHoles hCtx} (hb : b.Equiv b') :
    (StmtWithHoles.while c b).Equiv (StmtWithHoles.while c b') :=
  StmtWithHoles.EquivInLens.while c hb

/-- Transitivity, at the identity lens (`Lens.id.chain Lens.id` is `Lens.id`). -/
theorem StmtWithHoles.Equiv.trans {hCtx : HoleSigs} {a b c : StmtWithHoles hCtx}
    (h : a.Equiv b) (h' : b.Equiv c) : a.Equiv c :=
  StmtWithHoles.EquivInLens.trans h h'

/-- Symmetry, at the identity lens (the one lens at which the relation is symmetric). -/
theorem StmtWithHoles.Equiv.symm {hCtx : HoleSigs} {a b : StmtWithHoles hCtx} (h : a.Equiv b) :
    b.Equiv a := by
  intro inst σ τ hσ
  change σ = τ at hσ
  subst hσ
  have ha : (programDenotation (a.instantiate inst) σ).mapState Lens.id.get
      = programDenotation (a.instantiate inst) σ :=
    SubProbability.bind_pure _
  have hb : (programDenotation (b.instantiate inst) σ).mapState Lens.id.get
      = programDenotation (b.instantiate inst) σ :=
    SubProbability.bind_pure _
  rw [ha, ← h inst σ σ rfl, hb]

/-! ## Hoare triples

A statement triple is a triple about any statement equivalent to its own, with the conditions read
through the lens of the equivalence: so it can be proved about a rewritten statement instead
(`hoare_inline`, `hoare_split`). -/

/-- The chance of an event under `mapState f μ` is that of its preimage under `μ`. -/
theorem SubProbability.ofEvent_mapState {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) (E : Set (α × s)) :
    (μ.mapState f).ofEvent E = μ.ofEvent ((fun p => (p.1, f p.2)) ⁻¹' E) := by
  letI : MeasurableSpace (α × s) := ⊤
  letI : MeasurableSpace (α × t) := ⊤
  change (MeasureTheory.Measure.bind μ.1 (fun p => MeasureTheory.Measure.dirac (p.1, f p.2)) E
    ).toNNReal = (μ.1 _).toNNReal
  rw [MeasureTheory.Measure.bind_dirac_eq_map _ measurable_from_top,
    MeasureTheory.Measure.map_apply measurable_from_top (MeasurableSpace.measurableSet_top)]

/-- **A triple about an equivalent statement**: along `s.EquivInLens s' l`, the triple about `s`
is the triple about `s'` with both conditions read through `l`. -/
theorem hoareStmt_iff_of_equivInLens {A B : ProgramState → Prop} {s s' : Stmt}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l) :
    hoareStmt A s B ↔ hoareStmt (fun τ => A (l.get τ)) s' (fun τ => B (l.get τ)) := by
  have h' : ∀ τ, (programDenotation s' τ).mapState l.get = programDenotation s (l.get τ) :=
    fun τ => by
      have := h ⟨⟩ (l.get τ) τ rfl
      rwa [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty] at this
  constructor
  · intro hs τ hA
    have := hs _ hA
    rw [← h' τ, SubProbability.ofEvent_mapState] at this
    exact this
  · intro hs σ hA
    have hτ : l.get (l.set σ σ) = σ := l.set_get σ σ
    have := hs (l.set σ σ) (show A (l.get (l.set σ σ)) by rw [hτ]; exact hA)
    rw [← hτ, ← h', SubProbability.ofEvent_mapState]
    exact this

/-- `hoareStmt_iff_of_equivInLens`, backwards, with the conditions given up to an equation: what
`hoare_inline` applies, the equations being those of the cleaning pass. -/
theorem hoareStmt_of_equivInLens {A B A' B' : ProgramState → Prop} {s s' : Stmt}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l)
    (hA : (fun τ => A (l.get τ)) = A') (hB : (fun τ => B (l.get τ)) = B')
    (h' : hoareStmt A' s' B') : hoareStmt A s B := by
  subst hA hB
  exact (hoareStmt_iff_of_equivInLens h).mpr h'

/-- A triple about an equivalent statement, without renaming: the conditions stay as they are. -/
theorem hoareStmt_of_equiv {A B : ProgramState → Prop} {s s' : Stmt} (h : s.Equiv s')
    (h' : hoareStmt A s' B) : hoareStmt A s B :=
  (hoareStmt_iff_of_equivInLens h).mpr h'

end GaudisCrypt
