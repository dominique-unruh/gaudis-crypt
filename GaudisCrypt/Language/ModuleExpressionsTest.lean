import GaudisCrypt.Language.ModuleExpressions

/-! # Tests for `ModuleExpressions`

Smoke tests for the `moduletyping`, `normalmodule` and `reduce_simp` tactics, kept out of
`ModuleExpressions.lean` so that file stays definitions-and-proofs only. -/

namespace GaudisCrypt

variable [ProgramSpec]

/-! ### Smoke tests -/

example : ModuleExpression.HasType .unit [] .unit := by moduletyping

example (A : ModuleTypeRep) : ModuleExpression.HasType (.var 0) [A] A := by moduletyping

example :
    ModuleExpression.HasType (.pair .unit .unit) [] (.prod .unit .unit) := by moduletyping

example : ModuleExpression.HasType (.fst (.pair .unit .unit)) [] .unit := by moduletyping

-- `.unit` applied to `.unit` is not well-typed (`.unit` isn't a function). `moduletyping`
-- peels the outer `.app`, closes the argument side (`HasType .unit [] ?A` via `.unit`, forcing
-- `?A := .unit`), and leaves the un-closable function side open instead of failing — so the
-- tactic block below ends with a genuine (and genuinely false) unsolved goal, caught by
-- `#guard_msgs` rather than papered over with a permanent `sorry`.
/-- error: unsolved goals
case a
inst✝ : ProgramSpec
⊢ ModuleExpression.unit.HasType [] (ModuleTypeRep.unit.arr ModuleTypeRep.unit) -/
#guard_msgs (whitespace := lax) in
example : ModuleExpression.HasType (.app .unit .unit) [] .unit := by
  moduletyping
  guard_target = ModuleExpression.HasType .unit [] (.arr .unit .unit)

-- `moduletyping!` fails loudly on the same goal, with a message pinpointing the `.unit` node
-- (not a function) rather than just the outer `.app` goal.
/-- error: Cannot show (ModuleExpression.unit.app ModuleExpression.unit).HasType [] ModuleTypeRep.unit: `.unit` has type `.unit`, but the expected type ModuleTypeRep.unit.arr ModuleTypeRep.unit is not `.unit` -/
#guard_msgs (whitespace := lax) in
example : ModuleExpression.HasType (.app .unit .unit) [] .unit := by
  moduletyping!

-- `.proc _` mismatch.
/-- error: Cannot show (ModuleExpression.proc p).HasType [] T: `.proc _` always has a `.proc sig`-shaped type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example {sig : ProcedureSignature} (p : Procedure sig) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.proc p) [] T := by
  moduletyping!

-- `.procHoles _ _` mismatch.
/-- error: Cannot show (ModuleExpression.procHoles ne p).HasType [] T: `.procHoles _ _` always has an `.arr _ (.proc sig)`-shaped type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.procHoles ne p) [] T := by
  moduletyping!

-- `.abs _` mismatch (expected type isn't `.arr _ _`-shaped).
/-- error: Cannot show body.abs.HasType [] T: `.abs _` always has an `.arr _ _`-shaped (function) type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example (body : ModuleExpression) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.abs body) [] T := by
  moduletyping!

-- `.pair _ _` mismatch (expected type isn't `.prod _ _`-shaped).
/-- error: Cannot show (a.pair b).HasType [] T: `.pair _ _` always has a `.prod _ _`-shaped type, but the expected type T is not of that shape -/
#guard_msgs (whitespace := lax) in
example (a b : ModuleExpression) (T : ModuleTypeRep) :
    ModuleExpression.HasType (.pair a b) [] T := by
  moduletyping!

-- `.var _` mismatch: no context can supply an entry of an unrelated, opaque type `T`.
/-- error: Cannot show (ModuleExpression.var 0).HasType [] T: `.var 0` does not type-check in context [] at type T: that context does not provide a `0`-th entry of that type -/
#guard_msgs (whitespace := lax) in
example (T : ModuleTypeRep) : ModuleExpression.HasType (.var 0) [] T := by
  moduletyping!

-- `.var _`'s bound, genuinely un-dischargeable by `moduletyping`: `A :: Γ` is a real (if
-- partly opaque) context, so unifying the *type* of `.var 1` structurally peels the concrete
-- `A` and lands on `Γ[0]'_`, unifying with the target via proof irrelevance and leaving the
-- outer bound `1 < (A :: Γ).length` as a genuine residual goal. It's actually true — `hΓ`
-- witnesses `Γ` is nonempty — but `hΓ` is `Nonempty`-wrapped rather than a plain arithmetic
-- hypothesis, so `simp`/`omega` (which only look at arithmetic hypotheses) can't see it.
/-- error: Cannot show (ModuleExpression.var 1).HasType (A :: Γ) Γ[0]:
    `.var 1` occurs in typing context A :: Γ, which does not (provably) contain more than 1 element(s) (need `1 < (A :: Γ).length`) -/
#guard_msgs (whitespace := lax) in
example (A : ModuleTypeRep) (Γ : ModuleContext) (hΓ : Nonempty (0 < Γ.length)) :
    ModuleExpression.HasType (.var 1) (A :: Γ) (Γ[0]'hΓ.some) := by
  moduletyping!

-- No fail-fast: both branches of a `.pair` are independently un-closable, and both reasons are
-- reported together in one error instead of stopping at the first.
/-- error: Cannot show ((ModuleExpression.proc p).pair body.abs).HasType [] (T.prod U): `.proc _` always has a `.proc sig`-shaped type, but the expected type T is not of that shape

Cannot show ((ModuleExpression.proc p).pair body.abs).HasType [] (T.prod U): `.abs _` always has an `.arr _ _`-shaped (function) type, but the expected type U is not of that shape -/
#guard_msgs (whitespace := lax) in
example {sig : ProcedureSignature} (p : Procedure sig) (body : ModuleExpression)
    (T U : ModuleTypeRep) :
    ModuleExpression.HasType (.pair (.proc p) (.abs body)) [] (.prod T U) := by
  moduletyping!
/-! ### Smoke tests -/

example : ModuleExpression.Normal .unit := by normalmodule

example {sig : ProcedureSignature} (p : Procedure sig) :
    ModuleExpression.Normal (.proc p) := by normalmodule

example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) :
    ModuleExpression.Normal (.procHoles ne p) := by normalmodule

example : ModuleExpression.Normal (.var 3 : ModuleExpression) := by normalmodule

example (a b : ModuleExpression) (ha : a.Normal) (hb : b.Normal) :
    ModuleExpression.Normal (.pair a b) := by normalmodule

example (body : ModuleExpression) (hbody : body.Normal) :
    ModuleExpression.Normal (.abs body) := by normalmodule

-- `.app` of a bare `.procHoles` node to a non-tuple normal argument: the `.appProcHoles` branch.
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) :
    ModuleExpression.Neutral (.app (.procHoles ne p) (.var 0)) := by normalmodule

-- `.app` of a genuine variable head: the `.app` branch, not `.appProcHoles`.
example (arg : ModuleExpression) (harg : arg.Normal) :
    ModuleExpression.Neutral (.app (.var 0) arg) := by normalmodule

example : ModuleExpression.Neutral (.fst (.var 0 : ModuleExpression)) := by normalmodule

-- `.pair _ _` can never be `Neutral` (only `Normal`); no branch of `normalmodule`'s core script
-- applies to this goal at all, so it now fails outright (rather than silently leaving the goal
-- untouched) — the error is `first`'s report of its last alternative's failure.
/-- error: Tactic `apply` failed: could not unify the conclusion of `@ModuleExpression.Normal.neutral`
  ModuleExpression.Normal ?e
with the goal
  (a.pair b).Neutral

Note: The full type of `@ModuleExpression.Normal.neutral` is
  ∀ [inst : ProgramSpec] {e : ModuleExpression}, e.Neutral → e.Normal

inst✝ : ProgramSpec
a b : ModuleExpression
⊢ (a.pair b).Neutral -/
#guard_msgs (whitespace := lax) in
example (a b : ModuleExpression) : ModuleExpression.Neutral (.pair a b) := by
  normalmodule

-- `normalmodule!` fails loudly on the same goal, pinpointing *why* `.pair` can't be `Neutral`.
/-- error: Cannot show (a.pair b).Neutral: `.pair _ _` is always `Normal` (via `.pair`), never `Neutral` -/
#guard_msgs (whitespace := lax) in
example (a b : ModuleExpression) : ModuleExpression.Neutral (.pair a b) := by
  normalmodule!

/-- error: Cannot show ModuleExpression.unit.Neutral: `.unit` is always `Normal` (via `.unit`), never `Neutral` — it has no variable/`.procHoles`-application head for a redex to get stuck on -/
#guard_msgs (whitespace := lax) in
example : ModuleExpression.Neutral (.unit : ModuleExpression) := by
  normalmodule!

/-- error: Cannot show (ModuleExpression.proc p).Neutral: `.proc _` is always `Normal` (via `.proc`), never `Neutral` -/
#guard_msgs (whitespace := lax) in
example {sig : ProcedureSignature} (p : Procedure sig) :
    ModuleExpression.Neutral (.proc p) := by
  normalmodule!

/-- error: Cannot show (ModuleExpression.procHoles ne p).Neutral: `.procHoles _ _` is always `Normal` (via `.procHoles`) when bare; it's only ever `Neutral` once applied to an argument (`.app`), never on its own -/
#guard_msgs (whitespace := lax) in
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) :
    ModuleExpression.Neutral (.procHoles ne p) := by
  normalmodule!

/-- error: Cannot show body.abs.Neutral: `.abs _` is always `Normal` (via `.abs`), never `Neutral` -/
#guard_msgs (whitespace := lax) in
example (body : ModuleExpression) : ModuleExpression.Neutral (.abs body) := by
  normalmodule!

-- Opaque subterm, no hypothesis: `assumption` fails, no constructor matches an fvar head.
/-- error: Cannot show m.Normal: `m` is an opaque subterm; no `Normal`/`Neutral` hypothesis for it is in scope (`assumption` failed) -/
#guard_msgs (whitespace := lax) in
example (m : ModuleExpression) : ModuleExpression.Normal m := by
  normalmodule!

-- The `.appProcHoles` side condition, genuinely undecidable: `arg` is opaque (so `decide` can't
-- reduce it) and only `Normal arg` is in context, not `¬ IsProcTuple arg`.
/-- error: Cannot show ((ModuleExpression.procHoles ne p).app arg).Neutral: could not show `arg` is not a hole-free procedure tuple (needed so the `.procHoles`-applied-to-`arg` node stays stuck, i.e. genuinely `Neutral`) -/
#guard_msgs (whitespace := lax) in
example {holes : HoleSigs} {sig : ProcedureSignature} (ne : holes.NonEmpty)
    (p : ProcedureWithHoles holes sig) (arg : ModuleExpression) (harg : arg.Normal) :
    ModuleExpression.Neutral (.app (.procHoles ne p) arg) := by
  normalmodule!
/-! ### `reduce_simp_head` smoke tests

Written as `∃ m, reduce x = m`, proved by `⟨_, by reduce_simp_head⟩`: the witness `_` is a
genuine metavariable the tactic assigns via unification, unlike `example : reduce x = _ := ...`
directly (there, the `_` sits in the *stated type*, which Lean fully elaborates — including
resolving its own holes — before the tactic block ever runs, so it can't be left for the tactic
to fill; confirmed empirically, "don't know how to synthesize placeholder"). The anonymous
constructor's fields, by contrast, are genuinely elaborated together with the tactic proof. -/

example : ∃ m, ModuleExpression.reduce (.fst (.pair .unit .unit)) = m := ⟨_, by reduce_simp_head⟩
example : ∃ m, ModuleExpression.reduce (.app (.abs .unit) .unit) = m := ⟨_, by reduce_simp_head⟩

example (m n : ModuleExpression) (h : m.ReductionStep n) :
    ∃ m', ModuleExpression.reduce m = m' := ⟨_, by reduce_simp_head⟩
/-! ### Smoke tests -/

example : ModuleExpression.reduce (.fst (.pair .unit .unit)) = .unit := by reduce_simp

example : ModuleExpression.reduce (.app (.abs .unit) .unit) = .unit := by reduce_simp

example (m n : ModuleExpression) (h : m.ReductionStep n) (hn : n.Normal) :
    ModuleExpression.reduce m = n := by
  reduce_simp

example (m n : ModuleExpression) (h : m.MultiStepReduction n) (hn : n.Normal) :
    ModuleExpression.reduce m = n := by
  reduce_simp

example (m n : ModuleExpression) (h : ModuleExpression.convertible m n) (hn : n.Normal) :
    ModuleExpression.reduce m = n := by
  reduce_simp

example (m : ModuleExpression) (h : ModuleExpression.reduce m = .unit) :
    ModuleExpression.reduce (.fst (.pair m .unit)) = .unit := by
  reduce_simp

-- The pair as a whole isn't `Normal` — its first component `.fst (.pair .unit .unit)` is a
-- genuine redex — so the `reduce_of_normal` rule can't collapse it in one visit at the top;
-- `reduce_pair_cong_left` (inside `reduce_simp_head`) reduces that component, and `simp`'s
-- traversal revisits the result, which *is* now directly `Normal`.
example (b : ModuleExpression) (hb : b.Normal) :
    ModuleExpression.reduce (.pair (.fst (.pair .unit .unit)) b) = .pair .unit b := by
  reduce_simp

-- A `reduce ...` term whose argument itself already contains a nested `reduce`: `simp`'s
-- traversal must simplify that inner occurrence too, not just the outer one.
example (a c : ModuleExpression) (ha : a.Normal) (hc : c.Normal) :
    ModuleExpression.reduce (.pair (ModuleExpression.reduce a) c) = .pair a c := by
  reduce_simp

end GaudisCrypt
