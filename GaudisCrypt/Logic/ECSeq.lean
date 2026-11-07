import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.StmtSwap

/-!
# EasyCrypt's `seq n m : P` on a relational judgment

    equiv_seq n m : P        -- EC's `seq n m : P`

Cut both statements after their first `n` (left) and `m` (right) statements, in EC's positions
(the resets inlining leaves are not counted: each goes with the statement after it, as for
`stmt_swap [a..b] k`), with the relation `P` in between.  Goals: the code before the cut (to `P`),
then the code after it (from `P`).  It is `equiv_seq_last` (`Logic/PRHLWp.lean`), which counts the
statements after the cut, from the end.
-/

namespace GaudisCrypt.ECSeq

open Lean Meta Elab Tactic StmtSwap

/-- Our statements after the first `n` of EC's, of the statement `s` (as `equiv_seq_last` counts
them). -/
def afterEC (s : Lean.Expr) (n : Nat) : MetaM Nat := do
  let gs := ecGroups (← spineResets s)
  unless n ≤ gs.size do
    throwError "equiv_seq: {n} statements, but the code has {gs.size}"
  return (gs.extract n gs.size).foldl (· + ·) 0

end GaudisCrypt.ECSeq

namespace GaudisCrypt

open Lean Meta Elab Tactic ECSeq PRHLWp

/-- **EC's `seq n m : P`**: see the module docstring. -/
elab "equiv_seq " n:num ppSpace m:num " : " P:term : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← prhlGoal g "equiv_seq"
  let k₁ ← afterEC (ty.getArg! 1) n.getNat
  let k₂ ← afterEC (ty.getArg! 2) m.getNat
  evalTactic (← `(tactic| equiv_seq_last $(quote k₁) $(quote k₂) : $P))

end GaudisCrypt
