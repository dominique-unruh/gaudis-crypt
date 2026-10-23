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
(`equiv_call`, EC's `call (_:true)`), the opening key coupled with the fake
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
  equiv_call
  stmt_wp
  equiv_rnd (fun d => d + §x0{1} * §m{1})
  stmt_wp
  equiv_rnd
  equiv_call
  stmt_wp
  equiv_rnd
  stmt_wp
  equiv_skip
  -- left: from equal globals, for every exponent `x`, messages `m` (and globals) from `choose`,
  -- coin `b` and opening key `d`, the real commitment is the fake one
  intro _ _ h x
  refine ⟨h, fun m _ b d => ?_⟩
  rw [Pedersen.pow_mul group, Pedersen.pow_add group]

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
