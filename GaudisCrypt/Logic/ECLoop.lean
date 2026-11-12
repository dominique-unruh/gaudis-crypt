import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.PHoareWp

/-!
# EasyCrypt's `splitwhile` and `unroll`

    stmt_splitwhile{i} n : e     -- EC's `splitwhile{i} n : e`
    stmt_unroll{i} n             -- EC's `unroll{i} n`

The loop at EC's position `n` (from 1, the resets inlining leaves not counted, as for
`stmt_swap [a..b] k`) is rewritten by an equivalence of statements: `while c b` becomes
`while (c /\ e) b; while c b` (`splitwhile`), or `if c { b; while c b }` (`unroll`).  On any
registered judgment, on side `i` of a relational one.  `e` is written like a condition of the
goal (`§x` reads the program variable `x`) and may be a proposition (decided) or a boolean.

`splitwhile` holds for every loop, as in EC (`Stmt.Equiv.splitwhile'`): the split loop's
expectation is the original's by the least-fixed-point property of loops alone
(`Stmt.ewp_while_le`), no variant needed.
-/

namespace GaudisCrypt

/-- **`splitwhile`**, on expectations, for every loop: a loop is the same loop run first while
`e` also holds, then on. -/
theorem Stmt.ewp_splitwhile' (c e : Getter Bool ProgramState) (body : Stmt)
    (g : ProgramState → ENNReal) (σ : ProgramState) :
    Stmt.ewp (StmtWithHoles.while c body) g σ =
      Stmt.ewp (StmtWithHoles.seq (StmtWithHoles.while (c.andB e) body)
        (StmtWithHoles.while c body)) g σ := by
  rw [Stmt.ewp_seq]
  set W := Stmt.ewp (StmtWithHoles.while c body) g with hW
  set L := Stmt.ewp (StmtWithHoles.while (c.andB e) body) W with hL
  have hfix : ∀ τ, (c.andB e).get τ = true → body.ewp W τ = W τ := fun τ hτ => by
    have hc : c.get τ = true := by simp only [Getter.andB_get, Bool.and_eq_true] at hτ; exact hτ.1
    rw [hW, Stmt.ewp_while_unfold c body g τ, if_pos hc]
  -- the split loop's expectation is at most the loop's: `W` is a fixed point of its rounds
  have hLW : ∀ τ, L τ ≤ W τ := fun τ =>
    Stmt.ewp_while_le W W (fun τ hτ => (hfix τ hτ).le) (fun _ _ => le_rfl) τ
  refine le_antisymm ?_ (hLW σ)
  -- and at least: `L` is a prefixed point of the loop's rounds
  refine Stmt.ewp_while_le L g (fun τ hc => ?_) (fun τ hc => ?_) σ
  · cases he : e.get τ
    · have hce : (c.andB e).get τ = false := by
        rw [Getter.andB_get, he, Bool.and_false]
      rw [hL, Stmt.ewp_while_unfold (c.andB e) body W τ,
        if_neg (by rw [hce]; exact Bool.false_ne_true), hW,
        Stmt.ewp_while_unfold c body g τ, if_pos hc]
      exact Stmt.ewp_mono _ hLW τ
    · have hce : (c.andB e).get τ = true := by
        rw [Getter.andB_get, hc, he]; rfl
      rw [hL, Stmt.ewp_while_unfold (c.andB e) body W τ, if_pos hce]
  · have hce : (c.andB e).get τ = false := by
      rw [Getter.andB_get, hc, Bool.false_and]
    rw [hL, Stmt.ewp_while_unfold (c.andB e) body W τ,
      if_neg (by rw [hce]; exact Bool.false_ne_true), hW,
      Stmt.ewp_while_unfold c body g τ, if_neg (by rw [hc]; exact Bool.false_ne_true)]

/-- **`splitwhile`** (EC's `splitwhile … : e`), as an equivalence of statements, for every
loop. -/
theorem Stmt.Equiv.splitwhile' (c e : Getter Bool ProgramState) (body : Stmt) :
    (StmtWithHoles.while c body).Equiv
      (StmtWithHoles.seq (StmtWithHoles.while (c.andB e) body) (StmtWithHoles.while c body)) :=
  Stmt.Equiv.of_denotation_eq fun σ =>
    Stmt.denotation_eq_of_ewp (fun g σ => Stmt.ewp_splitwhile' c e body g σ) σ


namespace ECLoop

open Lean Meta Elab Tactic TacticMisc StmtSwap

/-- Rewrite the statement at our position `p` (from 0) along the right-nested sequence `s₀`
(through the `let`s of the locals) by `f`, which gives the new statement and its equivalence to
the old one: the new sequence and its equivalence. -/
partial def rewriteAt (p : Nat) (f : Lean.Expr → MetaM (Lean.Expr × Lean.Expr))
    (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => do
      let (r, pr) ← rewriteAt p f (body.instantiate1 fv)
      return (← mkLetFVars #[fv] r (usedLetOnly := false),
              ← mkLetFVars #[fv] pr (usedLetOnly := false))
  if s.isAppOfArity ``StmtWithHoles.seq 3 then
    let a := s.getArg! 1
    let rest := s.getArg! 2
    if p == 0 then
      let (a', pa) ← f a
      return (← mkAppM ``StmtWithHoles.seq #[a', rest],
              ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, ← mkEquivRefl rest])
    let (rest', pr) ← rewriteAt (p - 1) f rest
    return (← mkAppM ``StmtWithHoles.seq #[a, rest'],
            ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl a, pr])
  unless p == 0 do throwError "no statement at position {p + 1}"
  f s

/-- The loop `while c body` of the statement `s`: `(c, body)`. -/
def loopOf (tac : String) (s : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← openStmt s
  unless s.isAppOfArity ``StmtWithHoles.while 3 do
    throwError "{tac}: not a loop:{indentExpr s}"
  return (s.getArg! 1, s.getArg! 2)

/-- Our position (from 0) of EC's statement `n` (from 1) of the statement `s`: the last of its
group (`ecGroups`: the resets before it come first). -/
def ourPos (tac : String) (s : Lean.Expr) (n : Nat) : MetaM Nat := do
  let gs := TacticMisc.ecGroups (← TacticMisc.spineResets s)
  unless 1 ≤ n && n ≤ gs.size do
    throwError "{tac}: no statement {n} (the code has {gs.size})"
  return (gs.extract 0 n).foldl (· + ·) 0 - 1

/-- A condition written like those of the goal's program (`§x` reads the program variable `x`),
a proposition (decided) or a boolean, as a getter of the program state. -/
def elabStmtCond (s : Lean.Expr) (stx : Term) : TacticM Lean.Expr := do
  let vars := (← ProgramSyntax.frameVars #[s] #[]).filter (·.nameable)
  let mut t ← `((GaudiExpr[ decide ($stx) ] : Getter Bool ProgramState))
  for v in vars.reverse do
    let some slot := v.slots[0]? | continue
    t ← `(letI $(mkIdent (.mkSimple v.name)) := $(← Term.exprToSyntax slot); $t)
  let e ← Term.elabTermEnsuringType t
    (← mkAppM ``Getter #[mkConst ``Bool, mkConst ``ProgramState])
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The guard `c /\ e` of the first loop of a split: for two condition getters `Getter.mk f`,
`Getter.mk g` (what `GaudiExpr[ ]` gives) the getter of `f st && g st`, whose reads the
tactics see (and which prints as a condition); `Getter.andB c e` otherwise. -/
def andGetter (c e : Lean.Expr) : MetaM Lean.Expr := do
  let c ← instantiateMVars c
  let e ← instantiateMVars e
  unless c.isAppOfArity ``Getter.mk 3 && e.isAppOfArity ``Getter.mk 3 do
    return ← mkAppM ``Getter.andB #[c, e]
  withLocalDeclD `st (mkConst ``ProgramState) fun st => do
    let b ← mkAppM ``Bool.and #[(mkApp c.appArg! st).headBeta, (mkApp e.appArg! st).headBeta]
    mkAppM ``Getter.mk #[← mkLambdaFVars #[st] b]

/-- The loop at our position `p` (from 0) of side `side?` of the judgment `g`, unrolled
(`Stmt.Equiv.unroll`): `if c { body; while c body }`. -/
def unrollAt (p : Nat) (g : MVarId) (side? : Option Nat) : MetaM MVarId :=
  Judgment.onStmt (rewriteAt p fun a => do
    let (c, body) ← loopOf "unroll" a
    let w ← mkAppM ``StmtWithHoles.while #[c, body]
    return (← mkAppM ``StmtWithHoles.ifThenElse
              #[c, ← mkAppM ``StmtWithHoles.seq #[body, w],
                ← mkAppOptM ``StmtWithHoles.skip #[(← whnfR (← inferType body)).appArg!]],
            ← mkAppM ``Stmt.Equiv.unroll #[c, body])) g side?

end ECLoop

open Lean Meta Elab Tactic ECLoop in
/-- **EC's `splitwhile{i} n : e`**: see the module docstring. -/
elab "stmt_splitwhile" s:(Judgment.judgmentSide)? ppSpace n:num " : " e:term : tactic => do
  let side? := Judgment.sideOf? s
  let g ← getMainGoal
  let (p, eE) ← g.withContext do
    let (d, ty) ← Judgment.descOf g side?
    let st := ty.getArg! d.stmtArg
    return (← ourPos "splitwhile" st n.getNat, ← elabStmtCond st e)
  liftMetaTactic1 fun g => some <$> Judgment.onStmt (rewriteAt p fun a => do
    let (c, body) ← loopOf "splitwhile" a
    let G ← andGetter c eE
    let w₁ ← mkAppM ``StmtWithHoles.while #[G, body]
    let pr ← mkAppM ``Stmt.Equiv.splitwhile' #[c, eE, body]
    -- the guard as `andGetter` spells it (by definition `Getter.andB c e`)
    let andB ← mkAppM ``Getter.andB #[c, eE]
    let ty := (← inferType pr).replace fun x => if x == andB then some G else none
    return (← mkAppM ``StmtWithHoles.seq #[w₁, ← mkAppM ``StmtWithHoles.while #[c, body]],
            ← mkExpectedTypeHint pr ty)) g side?

open Lean Meta Elab Tactic ECLoop in
/-- **EC's `unroll{i} n`**: see the module docstring. -/
elab "stmt_unroll" s:(Judgment.judgmentSide)? ppSpace n:num : tactic => do
  let side? := Judgment.sideOf? s
  let g ← getMainGoal
  let p ← g.withContext do
    let (d, ty) ← Judgment.descOf g side?
    ourPos "unroll" (ty.getArg! d.stmtArg) n.getNat
  liftMetaTactic1 fun g => some <$> unrollAt p g side?

end GaudisCrypt
