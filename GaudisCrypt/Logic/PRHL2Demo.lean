import GaudisCrypt.Logic.PRHL2

open GaudisCrypt.Language.Lens

namespace GaudisCrypt.Language.Semantics

/-!
# Demonstration: one-time-pad perfect secrecy via `prhl2`

The canonical coupling-logic example. Over any finite abelian group `G`,
the one-time pad encrypts a message `m` as `m + k` for a uniformly random
key `k`:

  `enc m  :=  do let k ← uniform; return (m + k)`

**Perfect secrecy**: for any two messages `m₀`, `m₁` the ciphertext
distributions coincide. In the coupling logic this is one move — exhibit a
coupling of the two key samplings under which the *ciphertexts are equal*.
Couple `k₀` (left) with `k₁ = k₀ + (m₀ - m₁)` (right): this is a translation
(an `Equiv`), so it sends the uniform distribution to itself, and

  `m₁ + k₁ = m₁ + (k₀ + (m₀ - m₁)) = m₀ + k₀`,

i.e. the two ciphertexts agree. The proof is `rnd` (the `uniform` rule with
the shift bijection) to align the keys, then `pure_pure` to return.
-/

/-- The one-time pad over a finite abelian group `G`. -/
noncomputable def enc {G : Type} [Fintype G] [Nonempty G] [AddCommGroup G]
    (m : G) : Program Unit G :=
  Program.uniform >>= fun k => pure (m + k)

/-- **One-time-pad perfect secrecy.** The ciphertexts of any two messages
    are related by the diagonal (equal-output) coupling — so they have the
    same distribution. -/
theorem otp_perfect_secrecy {G : Type} [Fintype G] [Nonempty G] [AddCommGroup G]
    (m₀ m₁ : G) :
    Program.prhl2 (fun _ _ : Unit => True) (enc m₀) (enc m₁) (fun u v => u.1 = v.1) := by
  -- Sequence: first the two key draws, then the two returns.
  refine Program.prhl2.bind
    -- couple the keys by the shift `k ↦ k + (m₀ - m₁)` (uniform ↦ uniform),
    -- carrying the invariant `m₀ + k₀ = m₁ + k₁`.
    (Program.prhl2.uniform (B := fun u v => m₀ + u.1 = m₁ + v.1)
      (Equiv.addRight (m₀ - m₁)) (fun k _ _ _ => by
        show m₀ + k = m₁ + (k + (m₀ - m₁))
        abel)) ?_
  -- the returns agree exactly when the carried invariant holds.
  intro k₀ k₁
  exact Program.prhl2.pure_pure (fun _ _ hM => hM)

/-- Consequently the two encryptions are wp-indistinguishable: any
    ciphertext-only observable has equal expectation under `enc m₀` and
    `enc m₁`. (Bridges the coupling to the probability level via `to_relE`.) -/
theorem otp_wp_eq {G : Type} [Fintype G] [Nonempty G] [AddCommGroup G]
    (m₀ m₁ : G) (F : G → ENNReal) :
    (enc m₀).wp (fun u => F u.1) () = (enc m₁).wp (fun u => F u.1) () := by
  have h := (otp_perfect_secrecy m₀ m₁).to_relE
  refine le_antisymm ?_ ?_
  · exact h.1 (fun u => F u.1) (fun v => F v.1)
      (fun u v huv => le_of_eq (congrArg F huv)) () () trivial
  · exact h.2 (fun v => F v.1) (fun u => F u.1)
      (fun v u huv => le_of_eq (congrArg F huv.symm)) () () trivial

/-!
## Demonstration 2: `#heads = #tails` over `n` fair coin flips

A longer "game". The state is a counter (`ℕ`). One loop counts heads, the
other counts tails, both over `n` fair flips:

  `headBody := do let b ← coin; if b then incr else skip`
  `tailBody := do let b ← coin; if b then skip else incr`

Their final-count distributions coincide. The coupling flips the coin
*oppositely* on the two sides (`b₂ = ¬b₁`) — a bijection that preserves the
fair coin — so each side increments on exactly the same physical outcome,
keeping the two counters equal throughout. The proof chains `loop_n`,
`bind`, `uniform` (the `¬` coupling), `get`, `set`, a case split, and
`pure_pure`.
-/

/-- The bit-flip bijection `Bool ≃ Bool`; it preserves the uniform (fair)
    coin, which is what licenses the opposite-coin coupling. -/
def notEquiv : Bool ≃ Bool :=
  ⟨Bool.not, Bool.not, fun b => Bool.not_not b, fun b => Bool.not_not b⟩

/-- Increment the counter (the whole state, via the identity lens). -/
noncomputable def incr : Program ℕ Unit :=
  Program.get Lens.id >>= fun c => Program.set Lens.id (c + 1)

/-- Two increments from equal counters end at equal counters. -/
theorem incr_rel : Program.prhl2 Eq incr incr (fun u v => u.2 = v.2) := by
  refine Program.prhl2.bind
    (Program.prhl2.get Lens.id Lens.id
      (B := fun u v => u.1 = v.1 ∧ u.2 = v.2) (fun _ _ h => ⟨h, h⟩)) (fun c₁ c₂ => ?_)
  exact Program.prhl2.set Lens.id Lens.id (c₁ + 1) (c₂ + 1)
    (fun _ _ h => by have hc : c₁ = c₂ := h.1; subst hc; rfl)

/-- Count a head: increment iff the coin shows `true`. -/
noncomputable def headBody : Program ℕ Unit :=
  (Program.uniform : Program ℕ Bool) >>= fun b => if b then incr else pure ()

/-- Count a tail: increment iff the coin shows `false`. -/
noncomputable def tailBody : Program ℕ Unit :=
  (Program.uniform : Program ℕ Bool) >>= fun b => if b then pure () else incr

/-- One head-step and one tail-step, with the coin coupled oppositely,
    preserve equality of the counters. -/
theorem body_rel : Program.prhl2 Eq headBody tailBody (fun u v => u.2 = v.2) := by
  refine Program.prhl2.bind
    (Program.prhl2.uniform (B := fun u v => v.1 = !u.1 ∧ u.2 = v.2) notEquiv
      (fun _ _ _ h => ⟨rfl, h⟩)) (fun b₁ b₂ => ?_)
  intro τ₁ τ₂ hpre
  have hb : b₂ = !b₁ := hpre.1
  have hτ : τ₁ = τ₂ := hpre.2
  cases b₁ with
  | true => rw [hb]; exact incr_rel τ₁ τ₂ hτ
  | false =>
    rw [hb]
    exact Program.prhl2.pure_pure (A := Eq) (B := fun u v => u.2 = v.2)
      (fun _ _ h => h) τ₁ τ₂ hτ

/-- **`#heads` and `#tails` have the same distribution** after `n` fair
    flips: the two counting loops are related by the equal-counter coupling. -/
theorem count_heads_eq_count_tails (n : ℕ) :
    Program.prhl2 Eq (loop_n n headBody) (loop_n n tailBody) (fun u v => u.2 = v.2) :=
  Program.prhl2.loop_n body_rel n

/-!
## Demonstration 3: a reduction step — the adversary frame rule

The workhorse of reductions: **a state change outside the adversary's
window is invisible to it.** This is what licenses inserting bookkeeping,
reprogramming a hidden oracle table, or sampling auxiliary randomness
*between* game hops without disturbing the adversary's output.

Setup: an adversary `winA.lift P` acts only through its window `winA`. A
reduction tweaks some *external* state `winE` (disjoint from `winA`, so
`winA.get (winE.set v σ) = winA.get σ`). Then running the adversary, and
running the tweak-then-adversary, produce the same output distribution.

The proof chains four rules: `prefix_right` (frame the external write off
the right side), `set_skip_right` (relate that write against `skip`, using
the disjointness), the new **`adversary`** call rule (the adversary from
window-agreeing states returns equal results), and `conseq`.
-/

theorem external_tweak_invisible {a e s γ : Type}
    [Countable a] [Countable s] [Countable γ]
    (winA : Lens a s) (winE : Lens e s) (P : Program a γ) (v : e)
    (hdisj : ∀ σ, winA.get (winE.set v σ) = winA.get σ) :
    Program.prhl2 (fun σ₁ σ₂ => winA.get σ₁ = winA.get σ₂)
      (winA.lift P)
      (Program.set winE v >>= fun _ => winA.lift P)
      (fun u v => u.1 = v.1) := by
  refine Program.prhl2.prefix_right (Mid := fun σ₁ σ₂ => winA.get σ₁ = winA.get σ₂) ?_ ?_
  · exact Program.prhl2.set_skip_right winE v (fun σ₁ σ₂ h => by
      show winA.get σ₁ = winA.get (winE.set v σ₂)
      rw [hdisj]; exact h)
  · exact (Program.prhl2.adversary winA P).conseq (fun _ _ h => h) (fun _ _ h => h.1)

end GaudisCrypt.Language.Semantics
