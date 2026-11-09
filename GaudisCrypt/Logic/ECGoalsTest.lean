import GaudisCrypt.Logic.ECGoals

/-! Tests of `on_goals` (EC's goal selectors). -/

example : (1 = 1 ∧ 2 ≤ 3) ∧ (3 = 3 ∧ 4 = 4) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  -- EC's `1,3: trivial` (the first and the third)
  on_goals 1, 3 => rfl
  -- goals left: `2 ≤ 3`, `4 = 4`; EC's `-1: trivial`
  on_goals -1 => rfl
  guard_target = 2 ≤ 3
  decide

example : 1 = 1 ∧ 2 = 2 ∧ 3 = 3 ∧ 4 ≤ 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- EC's `1..-2: trivial`
  on_goals 1..-2 => rfl
  guard_target = 4 ≤ 5
  decide
