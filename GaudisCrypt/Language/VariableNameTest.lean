import GaudisCrypt.Language.VariableName

/-! Tests for `VariableName`: the key is filled in as a literal, and `NameNe` is found by
instance search. -/

namespace GaudisCrypt

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
  { name := "x", type := Int, nonempty := ⋯, key := 121, keyCorrect := ⋯ }.NameNe
    { name := "x", type := Int, nonempty := ⋯, key := 121, keyCorrect := ⋯ }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : VariableName.NameNe (.mk "x" Int) (.mk "x" Int) := inferInstance

/--
error: failed to synthesize instance of type class
  { name := "x", type := Int, nonempty := ⋯, key := 121, keyCorrect := ⋯ }.NameNe
    { name := "x", type := Nat, nonempty := ⋯, key := 121, keyCorrect := ⋯ }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : VariableName.NameNe (.mk "x" Int) (.mk "x" Nat) := inferInstance

-- equality depends on name and type only, not on how the key was written
example : VariableName.mk "x" Int = @VariableName.mk "x" Int ⟨0⟩ (VariableName.encode "x") rfl :=
  VariableName.ext' rfl rfl

end GaudisCrypt
