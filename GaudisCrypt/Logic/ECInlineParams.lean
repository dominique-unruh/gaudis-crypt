import GaudisCrypt.Logic.StmtSwap

/-!
# One assignment per parameter of an inlined call

EasyCrypt inlines `f(e₁, e₂)` as `x₁ <- e₁; x₂ <- e₂; …`, one assignment per parameter; our
inliner writes `x₁, x₂ <- (e₁, e₂)`.  EC's positions after an `inline` then count more
statements than ours, and a `swap` that moves a statement between two parameters has nothing to
move past.

`stmt_split_params` turns every such tuple assignment into EC's sequence (`Stmt.split_pair`):
the tuple assignments that follow a `reset_vars` (what `inline` leaves in front of the
parameters).  Written after `stmt_inline*` until the inliner does it itself.
-/

namespace GaudisCrypt

open Lean Meta Elab Tactic StmtSwap TacticMisc in
/-- `stmt_split_params`: one assignment per parameter of the inlined calls, as EC's `inline`
leaves them (see the module docstring); `stmt_split_params{i}` on side `i`. -/
elab "stmt_split_params" s:(Judgment.judgmentSide)? : tactic =>
  liftMetaTactic1 fun g => some <$>
    Judgment.onStmt (fun st => do
      let rs := (← TacticMisc.spineResets st).toArray
      let mut cur := st
      let mut pf ← mkEquivRefl st
      -- the statements after a reset, from the last (the positions before it stay)
      for p in (List.range rs.size).reverse do
        if p == 0 || !rs[p - 1]! || rs[p]! then continue
        try
          let (s₁, p₁) ← splitPairAt p cur
          cur := s₁
          pf ← mkAppM ``StmtWithHoles.Equiv.trans #[pf, p₁]
        catch _ => pure ()
      let (s₂, p₂) ← flattenSeq cur
      return (s₂, ← mkAppM ``StmtWithHoles.Equiv.trans #[pf, p₂])) g (Judgment.sideOf? s)

end GaudisCrypt
