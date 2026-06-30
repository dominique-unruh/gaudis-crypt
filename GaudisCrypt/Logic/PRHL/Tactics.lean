import GaudisCrypt.Logic.PRHL.Core
import GaudisCrypt.Logic.PRHL.Lenses
import GaudisCrypt.Logic.PRHL.Loops

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics

/-!
# pRHL tactic layer (v1)

Lightweight sugar for the recurring proof moves observed in the validation
clients:

* **`wp_peel`** — strip leading deterministic (`set`/`get`/`pure`) and
  `uniform` steps off a `wp` goal, turning them into state updates and
  uniform averages and stopping at the first non-atomic head (a loop, an
  adversary, …). This packages the "peel the synchronized prefix" pattern
  used by both clients: do-notation produces exactly the right-nested
  binds the peel lemmas match.
* **`rel_bind Mid`** — cut a relational goal at the leading bind with the
  given intermediate relation (EasyCrypt's `seq` tactic). The `Mid`
  annotation is mandatory by design: it is the specification of the cut,
  and implicit unification of it is non-Miller and unreliable.
* **`rel_step`** — try the structural/leaf relational rules in order
  (refl, pure, set, get, ite, uniform with the identity coupling, loop,
  while, one-sided sampling). Rules with side conditions leave them as
  goals.
-/

/-! ## Peel lemmas -/

lemma ProgramDenotation.wp_set_seq {s γ α : Type} (L : Lens γ s) (v : γ)
    (P : ProgramDenotation s α) (F : α × s → ENNReal) (σ : s) :
    (ProgramDenotation.set L v >>= fun _ : Unit => P).wp F σ = P.wp F (L.set v σ) := by
  rw [wp_bind, wp_set]

lemma ProgramDenotation.wp_get_seq {s γ α : Type} (L : Lens γ s)
    (k : γ → ProgramDenotation s α) (F : α × s → ENNReal) (σ : s) :
    (ProgramDenotation.get L >>= k).wp F σ = (k (L.get σ)).wp F σ := by
  rw [wp_bind, wp_get]

lemma ProgramDenotation.wp_pure_seq {s α β : Type} (x : α)
    (k : α → ProgramDenotation s β) (F : β × s → ENNReal) (σ : s) :
    ((pure x : ProgramDenotation s α) >>= k).wp F σ = (k x).wp F σ := by
  rw [ProgramDenotation.pure_bind]

lemma ProgramDenotation.wp_uniform_seq {s α β : Type} [Fintype α] [Nonempty α]
    (k : α → ProgramDenotation s β) (F : β × s → ENNReal) (σ : s) :
    ((ProgramDenotation.uniform : ProgramDenotation s α) >>= k).wp F σ
    = ∑ v : α, (k v).wp F σ / Fintype.card α := by
  rw [wp_bind, wp_uniform]

/-! ## Tactics -/

/-- Strip leading `set`/`get`/`pure`/`uniform` steps off `wp` goals. -/
macro "wp_peel" : tactic =>
  `(tactic| simp only [ProgramDenotation.wp_set_seq, ProgramDenotation.wp_get_seq,
      ProgramDenotation.wp_pure_seq, ProgramDenotation.wp_uniform_seq])

/-- Cut a `relE` goal at the leading bind, with the given intermediate
    relation (EasyCrypt's `seq`). Produces the prefix judgment and the
    `∀`-quantified continuation judgment as goals. -/
macro "rel_bind" t:term : tactic =>
  `(tactic| refine ProgramDenotation.relE.bind (Mid := $t) ?_ (fun _ _ => ?_))

/-- Like `rel_bind`, for one-sided `rel` goals. -/
macro "rel_bind_le" t:term : tactic =>
  `(tactic| refine ProgramDenotation.rel.bind (Mid := $t) ?_ (fun _ _ => ?_))

/-- Try the structural/leaf relational rules; side conditions are left as
    goals. Runs at reducible transparency so failed candidates fail fast
    instead of unfolding program semantics. -/
macro "rel_step" : tactic =>
  `(tactic| with_reducible first
    | exact ProgramDenotation.relE.refl _
    | exact ProgramDenotation.rel.refl _
    | apply ProgramDenotation.relE.pure_pure
    | apply ProgramDenotation.relE.set_set
    | apply ProgramDenotation.relE.get_get
    | apply ProgramDenotation.relE.ite_sync
    | apply ProgramDenotation.relE.uniform_bij (Equiv.refl _)
    | apply ProgramDenotation.relE.loop_n
    | apply ProgramDenotation.relE.while_loop
    | apply ProgramDenotation.rel.pure_pure
    | apply ProgramDenotation.rel.set_set
    | apply ProgramDenotation.rel.get_get
    | apply ProgramDenotation.rel.ite_sync
    | apply ProgramDenotation.rel.uniform_bij (Equiv.refl _)
    | apply ProgramDenotation.rel.loop_n
    | apply ProgramDenotation.rel.while_loop
    | apply ProgramDenotation.rel.sample_left
    | apply ProgramDenotation.rel.sample_right)

/-! ## Smoke tests -/

example {s : Type} (p : ProgramDenotation s Bool) : p.relE p Eq Eq := by
  rel_step

example {s γ : Type} (L : Lens γ s) (v : γ) (q : ProgramDenotation s Bool)
    (F : Bool × s → ENNReal) (σ : s) :
    (ProgramDenotation.set L v >>= fun _ : Unit => q).wp F σ = q.wp F (L.set v σ) := by
  wp_peel

example {s γ : Type} (L M : Lens γ s) (v : γ) :
    (ProgramDenotation.set L v >>= fun _ => ProgramDenotation.get M).relE
    (ProgramDenotation.set L v >>= fun _ => ProgramDenotation.get M) Eq
    (fun u v => u.1 = v.1) := by
  rel_bind (fun u v : Unit × s => u.2 = v.2)
  · rel_step
    intro σ₁ σ₂ h
    rw [h]
  · rel_step
    intro τ₁ τ₂ h
    have h' : τ₁ = τ₂ := h
    rw [h']
