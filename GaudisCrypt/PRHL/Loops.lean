import GaudisCrypt.PRHL.Core
import GaudisCrypt.ProgramRange

/-!
# pRHL loop rules

Synchronized invariant rules for the bounded loop combinator `loop_n` and
for the unbounded `while_loop`.

The `while_loop` rule follows EasyCrypt's synchronized while: the guards
must agree under the invariant (`PostC` refines the invariant by the guard
value), the bodies preserve the invariant from `PostC true`, and the loop
relates at `PostC false`. The proof needs no Kleene induction: the left
loop's wp is a least fixed point (`wp_while`), so it suffices to exhibit a
prefixed point — `fun τ₁ => ⨅ τ₂, ⨅ (_ : Inv τ₁ τ₂), (while₂).wp G τ₂` —
the same `ENNReal`-interpolant trick as `rel.trans`.
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

/-! ## Synchronized `while_loop` rule -/

/-- Unfold one application of the wp loop functional (definitional). -/
private lemma while_iteration_wp_apply {s : Type}
    (c : Program s Bool) (p : Program s Unit) (post : Program.Post s Unit)
    (fp : Program.Pre s) (σ : s) :
    while_iteration_wp c p () post fp σ
    = c.wp (fun bst : Bool × s =>
        if bst.1 then p.wp (fun ut : Unit × s => fp ut.2) bst.2
        else post ((), bst.2)) σ := rfl

/-- **Synchronized while rule**: under the invariant the guards agree
    (`PostC b` records the invariant refined by the guard value `b`), the
    bodies preserve the invariant from `PostC true`, and the loops relate
    at `PostC false`. -/
lemma Program.rel.while_loop {s₁ s₂ : Type}
    {cond₁ : Program s₁ Bool} {body₁ : Program s₁ Unit}
    {cond₂ : Program s₂ Bool} {body₂ : Program s₂ Unit}
    {Inv : s₁ → s₂ → Prop} {PostC : Bool → s₁ → s₂ → Prop}
    (h_cond : cond₁.rel cond₂ Inv (fun u v => u.1 = v.1 ∧ PostC u.1 u.2 v.2))
    (h_body : body₁.rel body₂ (PostC true) (fun u v => Inv u.2 v.2)) :
    (_root_.while_loop cond₁ body₁).rel (_root_.while_loop cond₂ body₂) Inv
      (fun u v => PostC false u.2 v.2) := by
  intro F G hFG σ₁ σ₂ hpre
  rw [wp_while]
  have hIle : (while_iteration_wp cond₁ body₁ () F).lfp
      ≤ fun τ₁ => ⨅ τ₂, ⨅ (_ : Inv τ₁ τ₂), (_root_.while_loop cond₂ body₂).wp G τ₂ := by
    apply OrderHom.lfp_le
    intro τ₁
    refine le_iInf₂ fun τ₂ hinv => ?_
    rw [while_iteration_wp_apply]
    conv_rhs => rw [wp_while_unfold cond₂ body₂ G]
    refine h_cond _ _ ?_ τ₁ τ₂ hinv
    rintro ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨hb, hpc⟩
    have hb' : b₁ = b₂ := hb
    subst hb'
    dsimp only
    cases b₁ with
    | true =>
      simp only [↓reduceIte]
      refine h_body _ _ ?_ t₁ t₂ hpc
      rintro ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ hinv'
      change (⨅ τ₂, ⨅ (_ : Inv w₁ τ₂), (_root_.while_loop cond₂ body₂).wp G τ₂)
          ≤ (_root_.while_loop cond₂ body₂).wp G w₂
      exact iInf₂_le w₂ hinv'
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hFG _ _ hpc
  calc (while_iteration_wp cond₁ body₁ () F).lfp σ₁
      ≤ ⨅ τ₂, ⨅ (_ : Inv σ₁ τ₂), (_root_.while_loop cond₂ body₂).wp G τ₂ := hIle σ₁
    _ ≤ (_root_.while_loop cond₂ body₂).wp G σ₂ := iInf₂_le σ₂ hpre

/-- Two-sided synchronized while rule. -/
lemma Program.relE.while_loop {s₁ s₂ : Type}
    {cond₁ : Program s₁ Bool} {body₁ : Program s₁ Unit}
    {cond₂ : Program s₂ Bool} {body₂ : Program s₂ Unit}
    {Inv : s₁ → s₂ → Prop} {PostC : Bool → s₁ → s₂ → Prop}
    (h_cond : cond₁.relE cond₂ Inv (fun u v => u.1 = v.1 ∧ PostC u.1 u.2 v.2))
    (h_body : body₁.relE body₂ (PostC true) (fun u v => Inv u.2 v.2)) :
    (_root_.while_loop cond₁ body₁).relE (_root_.while_loop cond₂ body₂) Inv
      (fun u v => PostC false u.2 v.2) := by
  constructor
  · exact Program.rel.while_loop h_cond.1 h_body.1
  · refine Program.rel.while_loop (Inv := fun σ₂ σ₁ => Inv σ₁ σ₂)
      (PostC := fun b σ₂ σ₁ => PostC b σ₁ σ₂) ?_ h_body.2
    exact h_cond.2.conseq (fun _ _ h => h)
      (fun v u h => ⟨h.1.symm, h.1 ▸ h.2⟩)
