import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PRHLStmt
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Lib.EC.Distr

/-!
# EasyCrypt's product distributions (`theories/distributions/DProd.ec`), `ProdSampling`

The abstract theory `ProdSampling`'s types `t1`, `t2` are section variables, so a `clone` is an
application.  Only what ported developments use is here.
-/

namespace GaudisCrypt.EC.DProd.ProdSampling

open GaudisCrypt GaudisCrypt.EC

/-- **A product sampling against two samplings** (the coupling of EC's `sample_sample2`): `x <$ d`
on the left, `x₁ <$ d1; x₂ <$ d2` on the right, `d = d1 \`*\` d2` (`d2` not reading `x₁`), coupled
by the identity. -/
theorem prhlStmt_seq_sample_dprod {t1 t2 : Type} {A B : ProgramState → ProgramState → Prop}
    {s₁ s₂ : Stmt} {x : Setter (t1 × t2) ProgramState}
    {e : Getter (SubProbability (t1 × t2)) ProgramState}
    {x₁ : Setter t1 ProgramState} {e₁ : Getter (SubProbability t1) ProgramState}
    {x₂ : Setter t2 ProgramState} {e₂ : Getter (SubProbability t2) ProgramState}
    (h : prhlStmt A s₁ s₂ fun σ₁ σ₂ => e.get σ₁ = dprod (e₁.get σ₂) (e₂.get σ₂) ∧
      (∀ a, e₂.get (x₁.set a σ₂) = e₂.get σ₂) ∧
      ∀ p ∈ (e.get σ₁).support, B (x.set p σ₁) (x₂.set p.2 (x₁.set p.1 σ₂))) :
    prhlStmt A (.seq s₁ (.sample x e)) (.seq s₂ (.seq (.sample x₁ e₁) (.sample x₂ e₂))) B := by
  refine prhlStmt_seq (B := fun σ₁ σ₂ => _) ?_ h
  intro σ₁ σ₂ ⟨he, he₂, hB⟩
  refine ⟨(e.get σ₁).hbind fun p => pure (((), x.set p σ₁), ((), x₂.set p.2 (x₁.set p.1 σ₂))),
    ?_, ?_, ?_⟩
  · refine SubProbability.marginal_fst_eq fun F => ?_
    rw [programDenotation_sample_apply, SubProbability.expected_hbind,
      SubProbability.expected_hbind]
    simp only [expected_pure]
  · refine SubProbability.marginal_snd_eq fun F => ?_
    rw [programDenotation_seq, ProgramDenotation.bind_apply, programDenotation_sample_apply,
      SubProbability.expected_hbind, SubProbability.expected_bind, SubProbability.expected_hbind,
      he, dprod]
    simp only [expected_pure, SubProbability.expected_bind, programDenotation_sample_apply,
      SubProbability.expected_hbind, he₂]
  · exact SubProbability.satisfies_hbind _ fun a ha =>
      SubProbability.satisfies_pure _ _ (hB a (SubProbability.mem_support_of_ne_zero ha))


open Lean Meta Elab Tactic in
/-- `equiv_rnd_dprod`: `x <$ d1 \`*\` d2` on the left against `x₁ <$ d1; x₂ <$ d2` on the right,
coupled by the identity (`prhlStmt_seq_sample_dprod`). -/
elab "equiv_rnd_dprod" : tactic => withMainContext do
  let g ← getMainGoal
  let _ ← PRHLWp.prhlGoal g "equiv_rnd_dprod"
  let g ← HoareSplit.hoareSplit 1 g (side? := some 1)
  let g ← HoareSplit.hoareSplit 2 g (side? := some 2)
  g.withContext do
    let ty ← PRHLWp.prhlGoal g "equiv_rnd_dprod"
    let c ← mkConstWithFreshMVarLevels ``prhlStmt_seq_sample_dprod
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    unless ← isDefEq concl ty do
      throwError "equiv_rnd_dprod: not `x <$ d1 `*` d2` against two samplings:{indentExpr ty}"
    let hJ := ms.back!
    let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← inferType hJ)) (← g.getTag)
    unless ← isDefEq hJ g' do throwError "equiv_rnd_dprod: cannot set the new judgment"
    g.assign (← instantiateMVars (mkAppN c ms))
    let g' ← Judgment.simpArg g'.mvarId! 3 PRHLWp.relSimpDecls []
    replaceMainGoal [g']

variable (t1 t2 : Type) [Inhabited t1] [Inhabited t2]

module S {
  proc sample (d1 : SubProbability t1, d2 : SubProbability t2) : (t1 × t2) {
    var r : t1 × t2;
    r <$ dprod $d1 $d2;
    return $r
  };
  proc sample2 (d1 : SubProbability t1, d2 : SubProbability t2) : (t1 × t2) {
    var r1 : t1, r2 : t2;
    r1 <$ $d1;
    r2 <$ $d2;
    return ($r1, $r2)
  };
}

/-- `equiv sample_sample2 : S.sample ~ S.sample2 : ={d1, d2} ==> ={res}`. -/
theorem sample_sample2 :
    prhlProc (fun a₁ _ a₂ _ => a₁ = a₂) (S.sample t1 t2).procedure (S.sample2 t1 t2).procedure
      (fun r₁ _ r₂ _ => r₁ = r₂) := by
  equiv_proc_to_stmt
  stmt_inline 0
  stmt_wp
  equiv_rnd_dprod
  stmt_wp
  equiv_skip
  rintro _ _ _ _ h
  cases h
  rfl

end GaudisCrypt.EC.DProd.ProdSampling
