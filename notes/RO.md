


-- noncomputable
-- opaque adv : output -> Program state (Option input)

-- noncomputable
-- opaque oracle : input -> Program state output

-- noncomputable
-- def loop_body (out : output) : Program state (Option output) := do
--   match ← adv out with
--     | none => return none
--     | some inp =>
--       let out <- oracle inp
--       return some out


-- noncomputable
-- def repeat_until (body : a -> Program s (Bool × a)) (initial: a) : Program s a :=
--   sorry

-- noncomputable
-- def program_for_in {β} (b : β) (f : β → Program s (ForInStep β)) : Program s β :=
--   do
--       repeat_until (fun x ↦ do
--           let result <- f x
--           match result with
--             | ForInStep.done y => return (false, y)
--             | ForInStep.yield y => return (true, y))
--             b

-- noncomputable
-- instance : ForIn (Program s) Lean.Loop Unit where
--   forIn {β} _ (b : β) (f : Unit → β → Program s (ForInStep β)) : Program s β :=
--     program_for_in b (f ())

-- noncomputable
-- def loop : Program state Unit := do
--   let mut out : Option output := some default
--   while out ≠ none do
--     out <- loop_body (Option.get! out)
--   return ()

-- axiom oracle_input : Variable input
-- axiom oracle_output : Variable output
-- axiom want_more : Variable Bool

-- axiom adv2 : Program state Unit
-- axiom oracle2 : input -> Program state output
-- axiom adversary_result : Variable Bool
-- axiom oracle_init : Program state Unit

-- axiom skip : Program s Unit

-- noncomputable
-- def loop2 : Program state Bool := do
--   Program.set want_more true
--   oracle_init
--   while_loop (Program.get want_more) (do
--     adv2
--     if ← Program.get want_more then
--       Program.set oracle_output (← oracle2 (← Program.get oracle_input))
--     else
--       skip
--   )
--   Program.get adversary_result

-- noncomputable
-- def random_oracle_query (inp : input) : Program state output := do
--   return (← Program.get random_oracle_state) inp

-- noncomputable
-- def lazy_query (inp : input) : Program state output := do
--   let h <- Program.get lazy_state
--   let cached := h inp
--   match cached with
--   | some x => return x
--   | none =>
--     let value <- Program.uniform
--     Program.set lazy_state (fun x => if x=inp then some value else h x)
--     return value




Prove: lazy = random_oracle

Sketch:

Let d i := the state (a distribution) after the i-th iteration (non lazy)
Let d' i := ..... (lazy)

Assume for simplicity: type of adv state in non-lazy is input -> Option output.
Advantage: now we can use the *same* variable for adv_state

For d : SubProbability state
Let f d : SubProbability state := do
  let st <- d
  let h <- get_var oracle_state st
  let y : in->out <- uniform
  let h' := fun x => some (h.getD x (y x))
  let st' := set_var oracle_state st
  return st'

That is, take a distribution of state, and where the oracle function is `none`, assign uniform.

Claim 1: f (lazy_init st) = eager_init st

Claim 2: If f d' = d, then f (d'; adv) = d; adv
// adv doesn't touch `oracle_state`.

Claim 3: If f d' = d, then f (d'; lazy_query x) = d; eager_query x.
// Proof idea:
// wlog: d' is deterministic (then by linearity)
// case distinction on d' = none | some y
// each case: simple

Consequence: f (d' i) = d i
Consequence: for all variables != oracle_state, we have the same value always


--- Alternative proof:

Let convert : Program s Unit = do
  let h <- Program.get oracle_state
  let y : in->out <- uniform
  let h' := fun x => some (h.getD x (y x))
  set_var oracle_state h'

Claim 1: (lazy_init; convert) == eager_init

Claim 2: (adv; convert) == (convert; adv)

Claim 3: (lazy_query; convert) == (convert; eager_query)

From these claims, it follows that

lazy_init; adv; lazy_query; ... adv; lazy_query
= (up to oracle_state)
lazy_init; adv; lazy_query; ... adv; lazy_query; convert
= (Claims 2+3, induction)
lazy_init; convert; adv; eager_query; ... adv; eager_query
= (Claim 1)
eager_init; adv; eager_query; ... adv; eager_query


(Works also in easycrypt world, but needs a tactic of the kind:

(convert; O) =indist= (P; convert)
and
(I; convert) =indist= J
then
J; A^O =indist= I; A^P

