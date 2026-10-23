import GaudisCrypt.Examples.Pedersen.HidingPHoare
import GaudisCrypt.Logic.PRHLWp

/-!
# Pedersen hiding, relationally (EC's `phi_hi` with `equiv[ ]`)

EC's
```
local lemma phi_hi (U<:Unhider) &m:
  Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = Pr[FakeCommit(U).main() @ &m : res].
proof.
  byequiv => //.
  proc; inline*.
  call (_:true); wp.
  rnd (fun d, (d + x * (b?m1:m0)){2}) (fun d, (d - x * (b?m1:m0)){2}).
  by wp; rnd; call (_: true); auto => />; progress; algebra.
qed.
```
`phi_hi_prhl` is the same script: inline, the adversary's calls by reflexivity
(`equiv_call prhlProc_refl _`, EC's `call (_:true)`), the opening key coupled with the fake
game's exponent along `d ↦ d + x·m` (`equiv_rnd`), the other samplings by the identity, and the
algebra `g^d · (g^x)^m = g^(d + x·m)`.

The precondition is equality of all globals, which is what `phi_hi` (both games at the same
memory `&m`) needs: no footprint of the adversary is involved.  `Hiding.lean` proves the same
`phi_hi` on the coupling layer below with the stronger precondition `={glob U}`, which needs the
adversary rule at the level of denotations (`hidingGame_self_glob`, still a `sorry`); so
`pedersen_perfect_hiding'` here is the `sorry`-free version of `pedersen_perfect_hiding`.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt

variable (group : PedersenGroup)

theorem phi_hi_prhl (U : Unhider group.types) :
    equiv[ (hidingGame group U) ~ (fakeGame group U) :
      §allGlobals{1} = §allGlobals{2} ==> ={res} ] := by
  equiv_proc
  stmt_inline 0
  stmt_inline{1} 0
  stmt_inline{1} 1
  stmt_wp
  equiv_call prhlProc_refl _
  stmt_wp
  equiv_rnd (fun d => d + §x0{1} * §m{1})
  stmt_wp
  equiv_rnd
  equiv_call prhlProc_refl _
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  -- what is left, with the values named: the exponent `x`, the adversary's messages `m₁`/`m₂`
  -- (and globals) from `choose`, the coin `b`, the opening key `d`; then the two calls to
  -- `guess` must get equal arguments from equal globals (the real commitment
  -- `g^d * (g^x)^m_b` against the fake one `g^(d + x·m_b)`), and equal answers give `={res}`
  change ∀ σ₁ σ₂ : ProgramState, σ₁.globals = σ₂.globals →
    ∀ x : group.F, σ₁.globals = σ₂.globals ∧
      ∀ (m₁ : group.F × group.F) (g₁ : VariableAssignment) (m₂ : group.F × group.F)
        (g₂ : VariableAssignment), m₁ = m₂ ∧ g₁ = g₂ →
      ∀ (b : Bool) (d : group.F),
        (group.g ^ d * (group.g ^ x) ^ (if b then m₁.2 else m₁.1)
            = group.g ^ (d + x * if b then m₁.2 else m₁.1) ∧ g₁ = g₂) ∧
        ∀ (b'₁ : Bool) (g'₁ : VariableAssignment) (b'₂ : Bool) (g'₂ : VariableAssignment),
          b'₁ = b'₂ ∧ g'₁ = g'₂ → (b == b'₁) = (b == b'₂)
  intro σ₁ σ₂ h x
  refine ⟨h, ?_⟩
  rintro m g₁ _ _ ⟨rfl, rfl⟩ b d
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · rw [Pedersen.pow_mul group, Pedersen.pow_add group]
  · rintro _ _ _ _ ⟨rfl, -⟩
    rfl

/-- EC's `phi_hi`, by `byequiv` from `phi_hi_prhl`. -/
theorem phi_hi' (U : Unhider group.types) (σ : VariableAssignment) :
    Pr (hidingGame group U) σ = Pr (fakeGame group U) σ :=
  Procedure.Pr_eq_of_prhlProc (phi_hi_prhl group U) (E₁ := fun r _ => r = true)
    (E₂ := fun r _ => r = true) (fun r₁ _ r₂ _ (h : r₁ = r₂) => by rw [h]) rfl

/-- **Perfect hiding** (EC's `pedersen_perfect_hiding`): `phi_hi'` and `fakecommit_half'`. -/
theorem pedersen_perfect_hiding' (U : Unhider group.types) (σ : VariableAssignment)
    (uc_ll : IsLossless (Unhider.choose group.types U).procedure)
    (ug_ll : IsLossless (Unhider.guess group.types U).procedure) :
    Pr (hidingGame group U) σ = 1 / 2 := by
  rw [phi_hi' group U σ]
  exact fakecommit_half' group U σ uc_ll ug_ll

end GaudisCrypt.Examples.Pedersen
