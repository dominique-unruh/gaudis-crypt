import Lean

/-!
# Variable names

A `VariableName` is a program variable's name together with its type.  Besides the name it
carries a natural-number `key`, the name's encoding `VariableName.encode name`, stored as a
**literal**.  The key exists for instance search: two names with different literal keys are
told apart by `VariableName.NameNe` in a single unification step, whatever their length, which
is what lets disjointness of two variables be found automatically.  (Instance search cannot
compare strings in one step: a string literal is opened into a list of characters, and every
character then costs a step and a level of recursion.  `Nat` literals are the one kind of data
the unifier has built-in arithmetic for.  See `NEW_PROCEDURES.md`, §1.3.)

`key` and its correctness proof `keyCorrect` are filled in automatically: `key` is an implicit
argument of the constructor, and the `variable_name_key` tactic behind `keyCorrect` evaluates
`encode name` when `name` is a string literal and assigns `key` the resulting literal.  So one
writes `⟨"x", Int⟩` or `{ name := "x", type := Int }` and gets `@VariableName.mk "x" Int 121 ⋯`.
-/

namespace GaudisCrypt

/-- Bijective base-`0x110000` numeration of a character list, least significant digit first:
character `c` is the digit `c.toNat + 1` (in `1 … 0x110000`, since a code point is below
`0x110000`), and the empty list is `0`.  Reduces by `rfl` in the kernel on literals (the
corresponding encoding of the UTF-8 bytes does not: `String.toUTF8` gets stuck). -/
def VariableName.encodeChars : List Char → Nat
  | []      => 0
  | c :: cs => c.toNat + 1 + 0x110000 * encodeChars cs

/-- The key of a variable name: an injective, computable encoding of strings as naturals
(`encode_injective`).  Quadratic in the length of the string — each step multiplies the
accumulated number, about 21 bits per character, by a constant — which is microseconds at any
plausible name length.  (An `O(n log n)` version is possible: with base `2 ^ 21`, merge
neighbouring blocks with `a ||| (b <<< w)` in `log n` passes, each pass recursing on the list
and the passes on a counter.  Both recursions are structural, so it still reduces by `rfl`,
which `variable_name_key` relies on.  Splitting at the midpoint instead would need well-founded
recursion, which does not reduce.) -/
def VariableName.encode (s : String) : Nat := encodeChars s.toList

/-- A code point is below `0x110000`. -/
private theorem toNat_lt_0x110000 (c : Char) : c.toNat < 0x110000 := by
  rcases c with ⟨v, h⟩
  unfold UInt32.isValidChar Nat.isValidChar at h
  simp only [Char.toNat]
  omega

theorem VariableName.encodeChars_injective : Function.Injective encodeChars := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons d ds => simp only [encodeChars] at h; omega
  | cons c cs ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp only [encodeChars] at h; omega
    | cons d ds =>
      simp only [encodeChars] at h
      have hc := toNat_lt_0x110000 c
      have hd := toNat_lt_0x110000 d
      have h₁ : c.toNat = d.toNat := by omega
      have h₂ : encodeChars cs = encodeChars ds := by omega
      rw [Char.toNat_inj.mp h₁, ih h₂]

theorem VariableName.encode_injective : Function.Injective encode :=
  fun _ _ h => String.toList_injective (encodeChars_injective h)

open Lean Meta Elab Tactic in
/-- Close `?key = VariableName.encode name`.  If `name` is a string literal, compute the
encoding and assign `?key` the resulting `Nat` *literal*, so that instance search can compare
keys.  Otherwise `?key` becomes `VariableName.encode name` itself: the name is still a valid
variable name, but `VariableName.NameNe` will not be found for it by instance search. -/
elab "variable_name_key" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, key, rhs) := ty.eq?
    | throwError "variable_name_key: expected a goal `key = VariableName.encode name`, got{indentExpr ty}"
  let name ← instantiateMVars rhs.appArg!
  let value ← match name with
    | .lit (.strVal s) => pure (mkNatLit (VariableName.encode s))
    | _ => pure rhs
  unless ← isDefEq key value do
    throwError "variable_name_key: the key{indentExpr key}\nis not{indentExpr value}"
  goal.refl

/-- A program variable's name and type.  `key` is `encode name` as a literal and is filled in
automatically, together with its proof (see the module docstring).  Two `VariableName`s are
equal iff their names and types are (`nonempty` is a proposition, and `key`/`keyCorrect` are
determined by the name).

The type has to be nonempty, so that an assignment of values to all variable names exists at
all (`NEW_PROCEDURES.md`, §1.1).  The instance is found by instance search. -/
structure VariableName : Type 1 where
  name : String
  type : Type
  [nonempty : Nonempty type]
  {key : Nat}
  keyCorrect : key = VariableName.encode name := by variable_name_key

/-- `a < b`, for natural-number literals, found by instance search in one step: unifying
`?k + a + 1 =?= b` is solved by the unifier's literal-offset rule as `?k := b - a - 1`, at any
size of the literals.  (The unknown has to be the leftmost summand for that rule to apply.) -/
class NatLt (a b : Nat) : Prop where
  lt : a < b

instance (a k : Nat) : NatLt a (k + a + 1) := ⟨by omega⟩

/-- `a ≠ b`, for natural-number literals, found by instance search via `NatLt`. -/
class NatNe (a b : Nat) : Prop where
  ne : a ≠ b

instance (a b : Nat) [h : NatLt a b] : NatNe a b := ⟨Nat.ne_of_lt h.lt⟩
instance (a b : Nat) [h : NatLt b a] : NatNe a b := ⟨(Nat.ne_of_lt h.lt).symm⟩

/-- Two variable names whose names differ.  Found by instance search from the literal keys,
for names given as constructor applications (as `⟨"x", Int⟩` elaborates); since `encode` is
injective, it is found exactly when the names differ. -/
class VariableName.NameNe (v w : VariableName) : Prop where
  ne : v.name ≠ w.name

instance (n₁ n₂ : String) (T₁ T₂ : Type) (i₁ : Nonempty T₁) (i₂ : Nonempty T₂) (k₁ k₂ : Nat)
    (h₁ : k₁ = VariableName.encode n₁) (h₂ : k₂ = VariableName.encode n₂) [h : NatNe k₁ k₂] :
    VariableName.NameNe (@VariableName.mk n₁ T₁ i₁ k₁ h₁) (@VariableName.mk n₂ T₂ i₂ k₂ h₂) :=
  ⟨fun e => h.ne (by rw [h₁, h₂]; exact congrArg VariableName.encode e)⟩

theorem VariableName.ne_of_nameNe {v w : VariableName} [h : NameNe v w] : v ≠ w :=
  fun e => h.ne (congrArg VariableName.name e)

/-- A variable name is determined by its name and type. -/
theorem VariableName.ext' {v w : VariableName} (hn : v.name = w.name) (ht : v.type = w.type) :
    v = w := by
  cases v with | @mk n T i k hk =>
  cases w with | @mk n' T' i' k' hk' =>
  simp only at hn ht
  subst hn ht hk hk'
  rfl

end GaudisCrypt
