import Lean

/-!
# EasyCrypt's goal selectors: `on_goals`

    on_goals 1, 3 => auto        -- EC's `1,3: auto`
    on_goals 2..-2 => tac        -- EC's `2..-2: tac` (a range; negative positions from the end)
    on_goals -1 => tac           -- EC's `-1: tac`

EC applies a tactic to the goals at the given positions (from 1; `-k` the `k`-th from the end)
and leaves the others where they are; the goals each run leaves take its place.  Batteries'
`on_goal n` does it for one goal; EC's `last first` / `first last` are Lean's `rotate_right` /
`rotate_left`.
-/

namespace GaudisCrypt.ECGoals

declare_syntax_cat ecGoalSel
syntax num : ecGoalSel
syntax "-" num : ecGoalSel
syntax num ".." num : ecGoalSel
syntax num ".." "-" num : ecGoalSel

open Lean Elab Tactic

/-- The positions (from 0) that a selector picks among `n` goals. -/
def selected (n : Nat) (s : TSyntax `ecGoalSel) : TacticM (List Nat) := do
  let pos (k : Nat) (neg : Bool) : Nat := if neg then n - k else k - 1
  match s with
  | `(ecGoalSel| $k:num) => return [pos k.getNat false]
  | `(ecGoalSel| - $k:num) => return [pos k.getNat true]
  | `(ecGoalSel| $a:num .. $b:num) => return (List.range' (pos a.getNat false)
      (pos b.getNat false + 1 - pos a.getNat false))
  | `(ecGoalSel| $a:num .. - $b:num) => return (List.range' (pos a.getNat false)
      (pos b.getNat true + 1 - pos a.getNat false))
  | _ => throwUnsupportedSyntax

end GaudisCrypt.ECGoals

open Lean Elab Tactic GaudisCrypt.ECGoals in
/-- **EC's goal selectors** `i, j, a..b: tac`: see the module docstring. -/
elab "on_goals " sels:ecGoalSel,+ " => " tac:tacticSeq : tactic => do
  let gs ← getGoals
  let mut picked : List Nat := []
  for s in sels.getElems do
    picked := picked ++ (← selected gs.length s)
  let mut out : List MVarId := []
  for (g, i) in gs.zip (List.range gs.length) do
    if picked.contains i then
      if ← g.isAssigned then continue
      setGoals [g]
      evalTactic tac
      out := out ++ (← getUnsolvedGoals)
    else out := out ++ [g]
  setGoals out
