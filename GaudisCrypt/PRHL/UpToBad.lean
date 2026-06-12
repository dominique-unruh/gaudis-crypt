import PlonkLean.PRHL.Core
import PlonkLean.ProgramRange

/-!
# pRHL up-to-bad and rectangular rules

* `Program.relE.up_to_bad` — the Fundamental Lemma of game-playing as a
  corollary of a `relE` judgment whose post says "the bad flags agree, and
  on good runs the win indicator agrees". Note the post is parameterized by
  the indicator `G` rather than demanding full state equality on good runs:
  in real games the related states may still differ in parts `G` cannot see
  (e.g. the random-oracle entry at the challenge point).
* `Program.rel.of_unary` — the rectangular rule: a relational judgment from
  two *unary* facts ("p almost surely lands in P" and "q has mass 1 on Q").
  Needed when the two sides genuinely diverge (e.g. after the bad event) and
  the only maintainable invariant is one-sided.
-/

/-- **Up-to-bad** (Fundamental Lemma, relational form). From a diagonal
    `relE` whose post forces agreement of the bad flag and of `G` on good
    runs, conclude `Pr[p : G] ≤ Pr[q : G] + Pr[p : bad ∧ G]`. -/
lemma Program.relE.up_to_bad {s α : Type} {p q : Program s α}
    {bad : s → Prop} [DecidablePred bad]
    {Post : α × s → α × s → Prop}
    (G : α × s → ENNReal)
    (h : p.relE q Eq Post)
    (h_bad : ∀ x y, Post x y → (bad x.2 ↔ bad y.2))
    (h_good : ∀ x y, Post x y → ¬ bad x.2 → G x = G y)
    (σ : s) :
    p.wp G σ
    ≤ q.wp G σ + p.wp (fun x : α × s => if bad x.2 then G x else 0) σ := by
  apply Program.up_to_bad
  intro σ'
  apply h.wp_eq ?_ rfl
  intro x y hxy
  by_cases hb : bad x.2
  · rw [if_pos hb, if_pos ((h_bad x y hxy).mp hb)]
  · rw [if_neg hb, if_neg (fun hb' => hb ((h_bad x y hxy).mpr hb')),
        h_good x y hxy hb]

/-- The bad-event probabilities agree under the same `relE` judgment
    (companion to `Program.relE.up_to_bad`; in the unary development this
    took a separate mass-conservation chain). -/
lemma Program.relE.bad_eq {s α : Type} {p q : Program s α}
    {bad : s → Prop} [DecidablePred bad]
    {Post : α × s → α × s → Prop}
    (h : p.relE q Eq Post)
    (h_bad : ∀ x y, Post x y → (bad x.2 ↔ bad y.2))
    (σ : s) :
    p.wp (fun x : α × s => if bad x.2 then 1 else 0) σ
    = q.wp (fun y : α × s => if bad y.2 then 1 else 0) σ := by
  apply h.wp_eq ?_ rfl
  intro x y hxy
  by_cases hb : bad x.2
  · rw [if_pos hb, if_pos ((h_bad x y hxy).mp hb)]
  · rw [if_neg hb, if_neg (fun hb' => hb ((h_bad x y hxy).mpr hb'))]

/-- **Rectangular rule**: if `p` almost surely lands in `P` (from
    `Pre`-related states) and `q` has full mass on `Q`, then `p ~ q` at the
    rectangular post `P × Q`. The two sides need not be coupled at all. -/
lemma Program.rel.of_unary {s₁ s₂ α β : Type}
    {p : Program s₁ α} {q : Program s₂ β}
    {Pre : s₁ → s₂ → Prop}
    {P : α × s₁ → Prop} [DecidablePred P]
    {Q : β × s₂ → Prop} [DecidablePred Q]
    (hP : ∀ σ₁ σ₂, Pre σ₁ σ₂ →
        p.wp (fun x => if P x then 0 else 1) σ₁ = 0)
    (hQ : ∀ σ₁ σ₂, Pre σ₁ σ₂ →
        q.wp (fun y => if Q y then 1 else 0) σ₂ = 1) :
    p.rel q Pre (fun x y => P x ∧ Q y) := by
  intro F G hFG σ₁ σ₂ hpre
  have hstep1 : p.wp F σ₁ ≤ ⨅ y, ⨅ (_ : Q y), G y := by
    calc p.wp F σ₁
        ≤ p.wp (fun x => (⨅ y, ⨅ (_ : Q y), G y)
              + (⊤ : ENNReal) * (if P x then 0 else 1)) σ₁ := by
          apply Program.wp_le_wp_of_le
          intro x
          by_cases hx : P x
          · rw [if_pos hx, mul_zero, add_zero]
            exact le_iInf₂ (fun y hy => hFG x y ⟨hx, hy⟩)
          · rw [if_neg hx, mul_one]
            simp
      _ = p.wp (fun _ => ⨅ y, ⨅ (_ : Q y), G y) σ₁
          + (⊤ : ENNReal) * p.wp (fun x => if P x then 0 else 1) σ₁ := by
          rw [← Program.wp_const_mul, ← Program.wp_add]
      _ ≤ (⨅ y, ⨅ (_ : Q y), G y) + (⊤ : ENNReal) * 0 := by
          rw [hP σ₁ σ₂ hpre]
          gcongr
          exact Program.wp_const_le p _ σ₁
      _ = ⨅ y, ⨅ (_ : Q y), G y := by rw [mul_zero, add_zero]
  have hstep2 : (⨅ y, ⨅ (_ : Q y), G y) ≤ q.wp G σ₂ := by
    calc (⨅ y, ⨅ (_ : Q y), G y)
        = (⨅ y, ⨅ (_ : Q y), G y)
          * q.wp (fun y => if Q y then 1 else 0) σ₂ := by
          rw [hQ σ₁ σ₂ hpre, mul_one]
      _ = q.wp (fun y => (⨅ y', ⨅ (_ : Q y'), G y')
              * (if Q y then 1 else 0)) σ₂ := by
          rw [← Program.wp_const_mul]
      _ ≤ q.wp G σ₂ := by
          apply Program.wp_le_wp_of_le
          intro y
          by_cases hy : Q y
          · rw [if_pos hy, mul_one]
            exact iInf₂_le y hy
          · rw [if_neg hy, mul_zero]
            exact zero_le
  exact hstep1.trans hstep2
