import GaudisCrypt.Language.Variables

/-! Tests for `Variables`: the key of a `VariableName` is filled in as a literal, `NameNe` and
disjointness of variable slots are found by instance search, and `setParams` writes the
parameter slots. -/

namespace GaudisCrypt

/-! ### Variable names -/

-- the key is filled in as a literal, and `nonempty` by instance search, through the constructor …
/--
info: { name := "x", type := Int, nonempty := ⋯, key := @OfNat.ofNat Nat (nat_lit 121) (instOfNatNat (nat_lit 121)),
  keyCorrect := ⋯ } : VariableName
-/
#guard_msgs in
set_option pp.explicit true in
#check VariableName.mk "x" Int

-- … and through structure-instance notation, where `..` stands for `key` (the proof field is
-- filled in by its tactic)
/--
info: { name := "x", type := Int, nonempty := ⋯, key := @OfNat.ofNat Nat (nat_lit 121) (instOfNatNat (nat_lit 121)),
  keyCorrect := ⋯ } : VariableName
-/
#guard_msgs in
set_option pp.explicit true in
#check ({ name := "x", type := Int, .. } : VariableName)

-- a name that is not a literal still elaborates; its key is then `encode s` itself
/--
info: fun s ↦ { name := s, type := Int, nonempty := ⋯, key := VariableName.encode s, keyCorrect := ⋯ } : String → VariableName
-/
#guard_msgs in
set_option pp.explicit true in
#check fun s : String => VariableName.mk s Int

-- an empty type is rejected
/--
error: failed to synthesize instance of type class
  Nonempty Empty

Hint: Adding the command `deriving instance Nonempty for Empty` may allow Lean to derive the missing instance.
-/
#guard_msgs in
#check VariableName.mk "x" Empty

example : VariableName.NameNe (.mk "x" Int) (.mk "y" Int) := inferInstance
example : VariableName.NameNe (.mk "count" Nat) (.mk "cnt" Nat) := inferInstance
example : VariableName.NameNe (.mk "random_oracle_state" Nat) (.mk "random_oracle_stats" Nat) :=
  inferInstance
example : VariableName.mk "x" Int ≠ VariableName.mk "y" Bool := VariableName.ne_of_nameNe

-- through an `abbrev` (reducible), but not through a plain `def`
abbrev testVarX : VariableName := .mk "x" Int
def testVarY : VariableName := .mk "y" Int
example : VariableName.NameNe testVarX (.mk "y" Int) := inferInstance

/--
error: failed to synthesize instance of type class
  testVarX.NameNe testVarY

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : VariableName.NameNe testVarX testVarY := inferInstance

-- same name: not found, whatever the types
/--
error: failed to synthesize instance of type class
  { name := "x", type := ℤ, nonempty := ⋯, key := 121, keyCorrect := ⋯ }.NameNe
    { name := "x", type := ℤ, nonempty := ⋯, key := 121, keyCorrect := ⋯ }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : VariableName.NameNe (.mk "x" Int) (.mk "x" Int) := inferInstance

/--
error: failed to synthesize instance of type class
  { name := "x", type := ℤ, nonempty := ⋯, key := 121, keyCorrect := ⋯ }.NameNe
    { name := "x", type := ℕ, nonempty := ⋯, key := 121, keyCorrect := ⋯ }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : VariableName.NameNe (.mk "x" Int) (.mk "x" Nat) := inferInstance

-- equality depends on name and type only, not on how the key was written
example : VariableName.mk "x" Int = @VariableName.mk "x" Int ⟨0⟩ (VariableName.encode "x") rfl :=
  VariableName.ext' rfl rfl

/-! ### Variable slots -/

-- slots of different literal names are disjoint, whatever the types
example : Lens.Disjoint (varLens (.mk "x" Int)) (varLens (.mk "y" Int)) := inferInstance
example : Lens.Disjoint (varLens (.mk "x" Int)) (varLens (.mk "y" Bool)) := inferInstance

-- the same name with two types is not found disjoint (the slots are different, but instance
-- search only compares names)
/--
error: failed to synthesize instance of type class
  (varLens { name := "x", type := ℤ, nonempty := ⋯, key := 121, keyCorrect := ⋯ }).Disjoint
    (varLens { name := "x", type := Bool, nonempty := ⋯, key := 121, keyCorrect := ⋯ })

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Lens.Disjoint (varLens (.mk "x" Int)) (varLens (.mk "x" Bool)) := inferInstance

-- `setParams` writes the parameter slots.  Its slots carry the key `encode "x"`, not the literal
-- `121`; the `VariableName.reduceEncode` simproc evaluates it, so `simp` sees one slot …
example : VariableAssignment.setParams ["x", "y"] [Int, Bool] rfl (3, true)
    VariableAssignment.init (.mk "x" Int) = (3 : Int) := by
  classical
  simp only [VariableAssignment.setParams, varLens_set]
  simp

-- the dsimproc on its own (`dsimp only` fails when nothing is rewritten)
example : VariableName.encode "x" = 121 := by
  dsimp only [VariableName.reduceEncode]

-- … and leaves the other slots alone
example (m : VariableAssignment) : VariableAssignment.setParams ["x", "y"] [Int, Bool] rfl
    (3, true) m (.mk "z" Int) = m (.mk "z" Int) :=
  VariableAssignment.setParams_apply_of_notMem _ _ _ _ _ _ (by decide)

-- local slots stay disjoint inside the program state, and are disjoint from the globals
example : Lens.Disjoint (varLens (.mk "x" Int)).intoLocal (varLens (.mk "y" Bool)).intoLocal :=
  inferInstance
example (g : Lens Nat VariableAssignment) :
    Lens.Disjoint (varLens (.mk "x" Int)).intoLocal g.intoGlobal :=
  inferInstance

end GaudisCrypt
