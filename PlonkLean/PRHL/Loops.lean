import PlonkLean.PRHL.Core
import PlonkLean.ProgramRange

/-!
# pRHL loop rules

Synchronized invariant rules for the bounded loop combinator `loop_n`.
(A synchronized `while_loop` rule is deliberately deferred: both OW proofs
use only `loop_n`, and the unbounded rule needs a Kleene-iterate argument.)
-/

namespace Program.rel

/-- **Synchronized loop rule**: if the bodies preserve the relational
    invariant `Inv` (as a state relation), so do `n` synchronized
    iterations. -/
lemma loop_n {s₁ s₂ : Type}
    {body₁ : Program s₁ Unit} {body₂ : Program s₂ Unit}
    {Inv : s₁ → s₂ → Prop}
    (h : body₁.rel body₂ Inv (fun x y => Inv x.2 y.2)) (n : ℕ) :
    (loop_n n body₁).rel (loop_n n body₂) Inv (fun x y => Inv x.2 y.2) := by
  induction n with
  | zero =>
    exact Program.rel.pure_pure (fun σ₁ σ₂ hpre => hpre)
  | succ n ih =>
    change (body₁ >>= fun _ => _root_.loop_n n body₁).rel
           (body₂ >>= fun _ => _root_.loop_n n body₂) Inv _
    exact Program.rel.bind h (fun _ _ => ih)

end Program.rel

namespace Program.relE

/-- Two-sided synchronized loop rule. -/
lemma loop_n {s₁ s₂ : Type}
    {body₁ : Program s₁ Unit} {body₂ : Program s₂ Unit}
    {Inv : s₁ → s₂ → Prop}
    (h : body₁.relE body₂ Inv (fun x y => Inv x.2 y.2)) (n : ℕ) :
    (loop_n n body₁).relE (loop_n n body₂) Inv (fun x y => Inv x.2 y.2) :=
  ⟨Program.rel.loop_n h.1 n, Program.rel.loop_n h.2 n⟩

end Program.relE
