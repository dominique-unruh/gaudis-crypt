import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.PHoareWp
import GaudisCrypt.Logic.ECLoop

/-!
# EasyCrypt's `if` on the first statement

    stmt_if          -- EC's `if`: the first statements, conditionals (on both sides of `equiv`)
    stmt_if{i}       -- EC's `if{i}`: side `i`'s first statement, a conditional
    stmt_rcondt{i} n -- EC's `rcondt{i} n`: statement `n` a conditional whose test holds there
    stmt_rcondf{i} n -- EC's `rcondf{i} n`: … whose test fails there

EC's `if` works on the first statement of the code, the rest following each branch.  Here the
conditional takes the rest into its branches (`StmtWithHoles.Equiv.ifThenElse_seq`, an
equivalence, for any judgment), then the judgment's rule for a conditional applies: `hoareStmt_if`,
`phoareStmt_if` (any relation to the bound), `prhlStmt_if` (the guard goal: the tests agree), or
`prhlStmt_if_left`/`_right`.  Goals in EC's order: `guard` for the two-sided
rule (the tests agree), then `then`, `else` (the precondition with the test true, false).
-/

namespace GaudisCrypt

/-- A conditional followed by `r`: `r` in both branches. -/
theorem StmtWithHoles.Equiv.ifThenElse_seq {hCtx : HoleSigs} (c : Getter Bool ProgramState)
    (t e r : StmtWithHoles hCtx) :
    ((StmtWithHoles.ifThenElse c t e).seq r).Equiv
      (StmtWithHoles.ifThenElse c (t.seq r) (e.seq r)) := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  rw [ProgramDenotation.bind_assoc]
  have : ∀ b : Bool, ((if b then programDenotation (t.instantiate inst)
      else programDenotation (e.instantiate inst)) >>= fun _ => programDenotation (r.instantiate inst))
      = if b then (programDenotation (t.instantiate inst) >>= fun _ =>
          programDenotation (r.instantiate inst))
        else (programDenotation (e.instantiate inst) >>= fun _ =>
          programDenotation (r.instantiate inst)) := by
    intro b; cases b <;> rfl
  simp only [this]
  exact ProgramDenotation.EquivInLens.refl _

/-- **EC's `if`** on a Hoare triple whose statement is a conditional. -/
theorem hoareStmt_if {A B : ProgramState → Prop} {c : Getter Bool ProgramState} {t e : Stmt}
    (ht : hoareStmt (fun σ => A σ ∧ c.get σ = true) t B)
    (he : hoareStmt (fun σ => A σ ∧ c.get σ = false) e B) :
    hoareStmt A (StmtWithHoles.ifThenElse c t e) B := by
  rw [hoareStmt_iff_phoareStmt] at ht he ⊢
  intro σ hA
  rw [Stmt.ewp_ifThenElse]
  cases hc : c.get σ
  · simpa [hc] using he σ ⟨hA, hc⟩
  · simpa [hc] using ht σ ⟨hA, hc⟩

/-- **EC's `if`** on a `phoare` judgment whose statement is a conditional (any relation `ρ` to the
bound). -/
theorem phoareStmt_if {A : ProgramState → Prop} {c : Getter Bool ProgramState} {t e : Stmt}
    {g : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop} {r : ProgramState → ENNReal}
    (ht : phoareStmt (fun σ => A σ ∧ c.get σ = true) t g ρ r)
    (he : phoareStmt (fun σ => A σ ∧ c.get σ = false) e g ρ r) :
    phoareStmt A (StmtWithHoles.ifThenElse c t e) g ρ r := by
  intro σ hA
  rw [Stmt.ewp_ifThenElse]
  cases hc : c.get σ
  · simpa [hc] using he σ ⟨hA, hc⟩
  · simpa [hc] using ht σ ⟨hA, hc⟩

/-! ## `rcondt`, `rcondf`: a conditional whose test is known

EC's `rcondt n` (`rcondf n`): the statement at position `n` is a conditional whose test holds
(fails) wherever the code before it ends, from the precondition (a Hoare triple on that code);
the conditional is replaced by its branch.  On a loop (EC's `rcondt`/`rcondf` on a `while`), the
loop unrolled first (`Stmt.Equiv.unroll`): `rcondt` leaves its body before the loop, `rcondf`
nothing. -/

/-- A conditional run where its test is `b`: the branch `b` selects. -/
theorem programDenotation_ifThenElse_of {c : Getter Bool ProgramState} {t e : Stmt}
    {τ : ProgramState} {b : Bool} (hc : c.get τ = b) :
    programDenotation (StmtWithHoles.ifThenElse c t e) τ
      = programDenotation (if b then t else e) τ := by
  refine SubProbability.ext_of_expected fun F => ?_
  have h := congrFun (Stmt.ewp_ifThenElse c t e (fun σ' => F ((), σ'))) τ
  simp only [Stmt.ewp, ProgramDenotation.wp] at h
  rw [h, hc]
  cases b <;> rfl

/-- The core of `rcondt`/`rcondf`: from states where `p`'s runs end with the test `b`,
`p; (if c then t else e); r` runs as `p; (branch b); r`. -/
theorem programDenotation_rcond {p t e r : Stmt} {c : Getter Bool ProgramState}
    {P : ProgramState → Prop} (b : Bool) (hp : hoareStmt P p fun σ => c.get σ = b)
    {σ : ProgramState} (hσ : P σ) :
    programDenotation (p.seq ((StmtWithHoles.ifThenElse c t e).seq r)) σ
      = programDenotation (p.seq ((if b then t else e).seq r)) σ := by
  simp only [programDenotation_seq, ProgramDenotation.bind_apply]
  refine SubProbability.bind_congr_support _ fun u hu => ?_
  have hc : c.get u.2 = b := hp.satisfies hσ u hu
  rw [programDenotation_ifThenElse_of hc]

variable {A B : ProgramState → Prop} {p t e r : Stmt} {c : Getter Bool ProgramState}

/-- **EC's `rcondt`/`rcondf`** on a Hoare triple. -/
theorem hoareStmt_rcond (b : Bool) (hp : hoareStmt A p fun σ => c.get σ = b)
    (h : hoareStmt A (p.seq ((if b then t else e).seq r)) B) :
    hoareStmt A (p.seq ((StmtWithHoles.ifThenElse c t e).seq r)) B := by
  intro σ hA
  rw [programDenotation_rcond b hp hA]
  exact h σ hA

/-- **EC's `rcondt`/`rcondf`** on a `phoare` judgment. -/
theorem phoareStmt_rcond {g : ProgramState → ENNReal} {ρ : ENNReal → ENNReal → Prop}
    {rb : ProgramState → ENNReal} (b : Bool) (hp : hoareStmt A p fun σ => c.get σ = b)
    (h : phoareStmt A (p.seq ((if b then t else e).seq r)) g ρ rb) :
    phoareStmt A (p.seq ((StmtWithHoles.ifThenElse c t e).seq r)) g ρ rb := by
  intro σ hA
  have : Stmt.ewp (p.seq ((StmtWithHoles.ifThenElse c t e).seq r)) g σ
      = Stmt.ewp (p.seq ((if b then t else e).seq r)) g σ := by
    simp only [Stmt.ewp, ProgramDenotation.wp]
    rw [programDenotation_rcond b hp hA]
  rw [this]
  exact h σ hA

/-- **EC's `rcondt{1}`/`rcondf{1}`**: the test on the left, for every right state. -/
theorem prhlStmt_rcond_left {A B : ProgramState → ProgramState → Prop} {s₂ : Stmt} (b : Bool)
    (hp : ∀ σ₂, hoareStmt (fun σ₁ => A σ₁ σ₂) p fun σ => c.get σ = b)
    (h : prhlStmt A (p.seq ((if b then t else e).seq r)) s₂ B) :
    prhlStmt A (p.seq ((StmtWithHoles.ifThenElse c t e).seq r)) s₂ B := by
  intro σ₁ σ₂ hA
  rw [programDenotation_rcond b (hp σ₂) hA]
  exact h σ₁ σ₂ hA

/-- **EC's `rcondt{2}`/`rcondf{2}`**: the test on the right, for every left state. -/
theorem prhlStmt_rcond_right {A B : ProgramState → ProgramState → Prop} {s₁ : Stmt} (b : Bool)
    (hp : ∀ σ₁, hoareStmt (fun σ₂ => A σ₁ σ₂) p fun σ => c.get σ = b)
    (h : prhlStmt A s₁ (p.seq ((if b then t else e).seq r)) B) :
    prhlStmt A s₁ (p.seq ((StmtWithHoles.ifThenElse c t e).seq r)) B := by
  intro σ₁ σ₂ hA
  rw [programDenotation_rcond b (hp σ₁) hA]
  exact h σ₁ σ₂ hA

namespace ECIf

open Lean Meta Elab Tactic PRHLWp

/-- The first statement of `s`, a conditional followed by more code, with that code in its
branches; `s` itself if it is a conditional, or not one (a proof of `s.Equiv s'`). -/
partial def distribute (s : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s' ← TacticMisc.openStmt s
  if s'.isAppOfArity ``StmtWithHoles.seq 3 then
    let first ← TacticMisc.openStmt (s'.getArg! 1)
    -- a leading `skip` (what `sim` leaves of the code it went through): dropped
    if TacticMisc.isSkip first then
      let r := s'.getArg! 2
      let (r', pr) ← distribute r
      return (r', ← mkAppM ``StmtWithHoles.Equiv.trans
        #[← mkAppM ``StmtWithHoles.Equiv.skip_seq #[r], pr])
    if first.isAppOfArity ``StmtWithHoles.ifThenElse 4 then
      let r := s'.getArg! 2
      let (c, t, e) := (first.getArg! 1, first.getArg! 2, first.getArg! 3)
      let pf ← mkAppM ``StmtWithHoles.Equiv.ifThenElse_seq #[c, t, e, r]
      let rhs ← mkAppM ``StmtWithHoles.ifThenElse #[c, ← mkAppM ``StmtWithHoles.seq #[t, r],
        ← mkAppM ``StmtWithHoles.seq #[e, r]]
      return (rhs, pf)
  return (s, ← TacticMisc.mkEquivRefl s)

end ECIf

open Lean Meta Elab Tactic PRHLWp ECIf in
/-- **EC's `if`**: see the module docstring. -/
elab "stmt_if" s:(Judgment.judgmentSide)? : tactic => withMainContext do
  let side? := Judgment.sideOf? s
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let g ← if ty.isAppOf ``prhlStmt && side?.isNone then
      Judgment.onStmt distribute (← Judgment.onStmt distribute g (some 1)) (some 2)
    else Judgment.onStmt distribute g side?
  let ty ← instantiateMVars (← g.getType)
  let (lem, tags) :=
    if ty.isAppOf ``hoareStmt then (``hoareStmt_if, [`then, `else])
    else if ty.isAppOf ``phoareStmt then (``phoareStmt_if, [`then, `else])
    else match side? with
      | some 1 => (``prhlStmt_if_left, [`then, `else])
      | some 2 => (``prhlStmt_if_right, [`then, `else])
      | _ => (``prhlStmt_if, [`guard, `then, `else])
  let gs ← try applyLemma lem g
    catch _ => throwError "stmt_if: the first statement is not a conditional"
  unless gs.size == tags.length do
    throwError "stmt_if: `{lem}` left {gs.size} goals"
  let mut out := #[]
  for (m, tag) in gs.toList.zip tags do
    let m' ← if tag == `guard then pure m else
      try Judgment.simpArg m 0 relSimpDecls [] catch _ => pure m
    -- a branch with the code after it is `(body); rest`: flat, as EC counts its statements
    let m' ← if tag == `guard then pure m' else do
      let sides : List (Option Nat) := if ty.isAppOf ``prhlStmt then
          (match side? with | some i => [some i] | none => [some 1, some 2])
        else [none]
      let mut h := m'
      for sd in sides do
        h ← try Judgment.onStmt TacticMisc.flattenSeq h sd catch _ => pure h
      pure h
    m'.setTag tag
    out := out.push m'
  -- EC's order: the guard goal (two-sided), then the branches
  replaceMainGoal out.toList

namespace ECIf

open Lean Meta Elab Tactic PRHLWp

/-- The statement `s` as `p; (if …); r` around its statement at our position `k` (from 0): `p`
the code before (`skip` if none), `r` the code after (`skip` if none); and a proof of
`s.Equiv` it. -/
def aroundAt (k : Nat) (s : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let n ← HoareSplit.seqLength s
  unless k < n do throwError "rcond: no statement {k + 1} (the code has {n})"
  let (s₁, pr₁) ← HoareSplit.splitSeq (n - k) s
  let s₁' ← TacticMisc.openStmt s₁
  let (p, q) := (s₁'.getArg! 1, s₁'.getArg! 2)
  let q' ← TacticMisc.openStmt q
  if q'.isAppOfArity ``StmtWithHoles.seq 3 then return (s₁, pr₁)
  -- the conditional last: `q ≡ q; skip`
  let hCtx := (← whnf (← inferType q)).appArg!
  let sk ← mkAppOptM ``StmtWithHoles.skip #[some hCtx]
  let qs ← mkAppM ``StmtWithHoles.seq #[q, sk]
  let prq ← mkAppM ``StmtWithHoles.Equiv.symm #[← mkAppM ``StmtWithHoles.Equiv.seq_skip #[q]]
  let pr₂ ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← TacticMisc.mkEquivRefl p, prq]
  return (← mkAppM ``StmtWithHoles.seq #[p, qs], ← mkAppM ``StmtWithHoles.Equiv.trans #[pr₁, pr₂])

/-- EC's `rcondt{i} n` (`b = true`) and `rcondf{i} n` (`b = false`). -/
def rcond (b : Bool) (side? : Option Nat) (n : Nat) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let isRel := ty.isAppOf ``prhlStmt
  if isRel && side?.isNone then throwError "rcond: a side, `rcondt\{1} n` or `rcondt\{2} n`"
  -- EC's position: the resets inlining leaves not counted
  let (d, ty') ← Judgment.descOf g side?
  let groups := TacticMisc.ecGroups (← TacticMisc.spineResets (ty'.getArg! d.stmtArg))
  unless 1 ≤ n && n ≤ groups.size do
    throwError "rcond: no statement {n} (the code has {groups.size})"
  let k := (groups.extract 0 n).foldl (· + ·) 0 - 1
  -- a loop (EC's `rcondt`/`rcondf` on a `while`): unrolled, `if c { body; while c body }`
  let g ← if ← ECLoop.isLoopAt k (ty'.getArg! d.stmtArg) then ECLoop.unrollAt k g side?
    else pure g
  let g ← Judgment.onStmt (aroundAt k) g side?
  let lem := if ty.isAppOf ``hoareStmt then ``hoareStmt_rcond
    else if ty.isAppOf ``phoareStmt then ``phoareStmt_rcond
    else if side? == some 2 then ``prhlStmt_rcond_right else ``prhlStmt_rcond_left
  let gs ← try applyLemma lem g #[(`b, toExpr b)]
    catch _ => throwError "rcond: statement {n} is not a conditional"
  -- `applyLemma` leaves the premises in order: the test's (`hp`), then the judgment (`h`)
  let #[hp, h] := gs | throwError "rcond: `{lem}` left {gs.size} goals"
  hp.setTag `cond
  -- the judgment: the branch selected (`if true = true then t else e` is `t`)
  let (d, _) ← Judgment.descOf h side?
  let h ← Judgment.simpArg h d.stmtArg
    [``eq_self_iff_true, ``ite_true, ``Bool.false_eq_true, ``ite_false] []
  -- the branch spliced in, as EC leaves it (EC's later positions count its statements)
  let h ← try Judgment.onStmt TacticMisc.flattenSeq h side? catch _ => pure h
  -- EC's order: the test's goal, then the judgment
  replaceMainGoal [hp, h]

end ECIf

open Lean Elab Tactic ECIf in
/-- **EC's `rcondt{i} n`**: see the module docstring. -/
elab "stmt_rcondt" s:(Judgment.judgmentSide)? ppSpace n:num : tactic =>
  rcond true (Judgment.sideOf? s) n.getNat

open Lean Elab Tactic ECIf in
/-- **EC's `rcondf{i} n`**: see the module docstring. -/
elab "stmt_rcondf" s:(Judgment.judgmentSide)? ppSpace n:num : tactic =>
  rcond false (Judgment.sideOf? s) n.getNat

end GaudisCrypt
