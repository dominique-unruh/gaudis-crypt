import GaudisCrypt.Logic.TacticMisc

/-!
# Splitting a sequence into two blocks

`splitSeq k` regroups a right-nested sequence `x₁; …; xₙ` as `{x₁; …; xₙ₋ₖ}; {xₙ₋ₖ₊₁; …; xₙ}`, with
a proof of denotational equivalence, and the tactic `hoare_split k` does that to the statement of a
`hoareStmt` goal.
-/

namespace GaudisCrypt.HoareSplit

open Lean Meta Elab Tactic TacticMisc

/-- The number of statements along the right spine of a sequence: `x₁; …; xₙ`, nested to the
right as `flattenSeq` leaves it, has `n`.  A `let` in the spine counts as one statement. -/
partial def seqLength (s : Lean.Expr) : MetaM Nat := do
  let s ← openStmt s
  if s.isAppOfArity ``StmtWithHoles.seq 3 then return (← seqLength (s.getArg! 2)) + 1
  return 1

/-- Split `x₁; …; xₙ` (nested to the right) into the two blocks `{x₁; …; xₙ₋ₖ}; {xₙ₋ₖ₊₁; …; xₙ}`,
returning the result and a proof of `‹input›.Equiv result`.  The second block is the input's own
subterm, the first is rebuilt.  At the ends, `k = 0` gives `{x₁; …; xₙ}; skip` and `k = n` gives
`skip; {x₁; …; xₙ}`.  Fails if `k > n`. -/
partial def splitSeq (k : Nat) (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => do
      let (r, p) ← splitSeq k (body.instantiate1 fv)
      return (← mkLetFVars #[fv] r (usedLetOnly := false),
              ← mkLetFVars #[fv] p (usedLetOnly := false))
  let n ← seqLength s
  if k = 0 ∨ k = n then
    let hCtx := (← whnf (← inferType s)).appArg!
    let skip ← mkAppOptM ``StmtWithHoles.skip #[some hCtx]
    let (parts, lem) := if k = 0 then (#[s, skip], ``StmtWithHoles.Equiv.seq_skip)
      else (#[skip, s], ``StmtWithHoles.Equiv.skip_seq)
    return (← mkAppM ``StmtWithHoles.seq parts,
            ← mkAppM ``StmtWithHoles.Equiv.symm #[← mkAppM lem #[s]])
  unless k < n do
    throwError "splitSeq: cannot split a sequence of {n} statements with {k} of them in the \
      second block"
  go (n - k) s
where
  /-- Split off the first `m` statements, `0 < m` and fewer than the sequence has: by induction
  on `m`, re-associating `x; ({l}; b)` to `{x; l}; b` at each step. -/
  go (m : Nat) (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    let s ← openStmt s₀
    if m = 1 then return (s, ← mkEquivRefl s)
    let x := s.getArg! 1
    let (r, p) ← go (m - 1) (s.getArg! 2)
    let (l, b) := (r.getArg! 1, r.getArg! 2)
    let pRest ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl x, p]
    let pAssoc ← mkAppM ``StmtWithHoles.Equiv.symm
      #[← mkAppM ``StmtWithHoles.Equiv.seq_assoc #[x, l, b]]
    return (← mkAppM ``StmtWithHoles.seq #[← mkAppM ``StmtWithHoles.seq #[x, l], b],
            ← mkAppM ``StmtWithHoles.Equiv.trans #[pRest, pAssoc])

/-- `hoare_split k`: on a goal `hoareStmt A {x₁; …; xₙ} B`, regroup the statement as
`{x₁; …; xₙ₋ₖ}; {xₙ₋ₖ₊₁; …; xₙ}`, the last `k` statements in the second block (`splitSeq`;
`k = 0` and `k = n` pad the empty side with `skip`). -/
elab "hoare_split " k:num : tactic =>
  liftMetaTactic1 fun g => some <$> hoareOnStmt (splitSeq k.getNat) g

end GaudisCrypt.HoareSplit
