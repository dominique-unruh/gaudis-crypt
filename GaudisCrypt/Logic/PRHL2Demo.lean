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

end GaudisCrypt.Language.Semantics
