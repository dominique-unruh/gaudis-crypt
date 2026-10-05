import Lean
import Mathlib.Data.Fintype.Basic
import GaudisCrypt.Language.Semantics

/-!
# Variables

The memory model of the new procedures (`NEW_PROCEDURES.md`, §2.1, §2.3, §4.2):

* `VariableName` — a program variable's name together with its type (see below).
* `VariableAssignment` — a value for every `VariableName`, with `VariableAssignment.init` as the
  initial (unspecified) assignment, and `varLens v` onto the slot of `v`.  Two `varLens` are
  disjoint by instance search when the names are literals that differ.
* `ProgramState` — the `globals` (still a `State` under `[ProgramSpec]`, refactor (I) of §1.4)
  together with the `locals` of the running procedure, with `globalL`/`localL` and
  `Lens.intoGlobal`/`Lens.intoLocal`.
* `VariableAssignment.setParams` — write an argument tuple into the parameter slots.
* `VariableAssignment.embed`/`rename` — view an assignment through an injective name map
  (types are kept, so no casts), used for flattening.

Nothing uses these yet.

## Variable names

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

/-! ## Global state and argument tuples

Defined here rather than in `Programs.lean`, which builds on this file.

The global state lives in `Type 1`, the universe of `VariableAssignment`, so that `State` and
`ProgramState` share a universe. -/

class ProgramSpec : Type 2 where
  state : Type 1

def State [spec : ProgramSpec] := spec.state

/-- Reducible on purpose: at a concrete parameter list the tuple type has to be visible to
unification at `reducible` transparency, or everything stated about `_ × _` gets stuck on it —
typeclass resolution (`OfNat (typeListToTuple [Nat]) 5` for a numeral argument of a `call`,
`Lens.Disjoint` of two projection lenses) is where it shows. -/
@[reducible] def typeListToTuple : List Type → Type
  | []      => Unit
  | [x]     => x
  | x :: xs => x × typeListToTuple xs

/-! ## Variable names -/

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

/-- The variable name `n : v.type`: `v` with its name replaced (and the key recomputed, as a
non-literal `encode n`).  `(v.withName n).type` is `v.type` by definition, which is what lets
`embed` move values between slots without casts. -/
def VariableName.withName (v : VariableName) (n : String) : VariableName :=
  @VariableName.mk n v.type v.nonempty (VariableName.encode n) rfl

@[simp] theorem VariableName.withName_name (v : VariableName) (n : String) :
    (v.withName n).name = n := rfl

@[simp] theorem VariableName.withName_withName (v : VariableName) (a b : String) :
    (v.withName a).withName b = v.withName b := rfl

theorem VariableName.withName_self (v : VariableName) : v.withName v.name = v :=
  VariableName.ext' rfl rfl

/-! ## Variable assignments -/

/-- A value for every variable name.  Inhabited (`init`) because every `VariableName` has a
nonempty type.  Reducible, so that `m v` typechecks at every transparency (rewriting needs
this). -/
abbrev VariableAssignment : Type 1 := (v : VariableName) → v.type

/-- The initial assignment: an unspecified value in every slot (`NEW_PROCEDURES.md`, §1.1). -/
noncomputable def VariableAssignment.init : VariableAssignment :=
  fun v => Classical.choice v.nonempty

/-- Reading a slot under a renamed variable name, when the new name is the old one. -/
theorem VariableAssignment.apply_withName (m : VariableAssignment) (v : VariableName) {n : String}
    (h : n = v.name) : m (v.withName n) = m v := by
  subst h
  cases v with | @mk n T i k hk => subst hk; rfl

theorem VariableAssignment.apply_withName_congr (m : VariableAssignment) (v : VariableName)
    {a b : String} (h : a = b) : m (v.withName a) = m (v.withName b) := by
  subst h; rfl

open Classical in
/-- The lens onto the slot of variable `v`.  Writing uses `Function.update`, with classical
decidable equality of variable names (their types are arbitrary, so there is no other). -/
noncomputable def varLens (v : VariableName) : Lens v.type VariableAssignment where
  get m := m v
  set x m := Function.update m v x
  set_get m x := Function.update_self v x m
  set_set m x y := Function.update_idem x y m
  get_set m := Function.update_eq_self v m

@[simp] theorem varLens_get (v : VariableName) (m : VariableAssignment) :
    (varLens v).get m = m v := rfl

open Classical in
theorem varLens_set (v : VariableName) (x : v.type) (m : VariableAssignment) :
    (varLens v).set x m = Function.update m v x := rfl

/-- Slots of different variable names are disjoint. -/
theorem varLens_disjoint {v w : VariableName} (h : v ≠ w) : Lens.Disjoint (varLens v) (varLens w) :=
  ⟨fun m x y => by classical exact Function.update_comm h.symm y x m⟩

/-- Slots of differently named variables are disjoint, found by instance search when both names
are literals (`VariableName.NameNe`).  Stated for constructor applications: for a variable `v`,
the slot type `v.type` is a projection the instance index cannot match against a concrete type,
while `(VariableName.mk n T).type` reduces to `T`. -/
instance varLens.instDisjoint (n₁ n₂ : String) (T₁ T₂ : Type) (i₁ : Nonempty T₁)
    (i₂ : Nonempty T₂) (k₁ k₂ : Nat) (h₁ : k₁ = VariableName.encode n₁)
    (h₂ : k₂ = VariableName.encode n₂)
    [VariableName.NameNe (@VariableName.mk n₁ T₁ i₁ k₁ h₁) (@VariableName.mk n₂ T₂ i₂ k₂ h₂)] :
    Lens.Disjoint (varLens (@VariableName.mk n₁ T₁ i₁ k₁ h₁))
      (varLens (@VariableName.mk n₂ T₂ i₂ k₂ h₂)) :=
  varLens_disjoint VariableName.ne_of_nameNe

/-! ## Writing arguments into parameter slots -/

/-- Write an argument tuple `typeListToTuple tys` into the slots `names.zip tys`, first
parameter first (so on a duplicate name the later parameter wins).  The `Nonempty` instance each
slot's `VariableName` needs comes from the argument itself.  Lists of different lengths (excluded
by the length hypothesis) leave the assignment unchanged. -/
noncomputable def VariableAssignment.setParams : (names : List String) → (tys : List Type) →
    names.length = tys.length → typeListToTuple tys → VariableAssignment → VariableAssignment
  | [], [], _, _, m => m
  | [n], [T], _, a, m =>
    haveI : Nonempty T := ⟨a⟩
    (varLens (.mk n T)).set a m
  | n :: n' :: ns, T :: T' :: Ts, h, (a, as), m =>
    haveI : Nonempty T := ⟨a⟩
    setParams (n' :: ns) (T' :: Ts) (by simpa using h) as ((varLens (.mk n T)).set a m)
  | _, _, _, _, m => m

/-- `setParams` leaves every slot outside the parameter names alone. -/
theorem VariableAssignment.setParams_apply_of_notMem : (names : List String) → (tys : List Type) →
    (h : names.length = tys.length) → (args : typeListToTuple tys) → (m : VariableAssignment) →
    (v : VariableName) → v.name ∉ names → setParams names tys h args m v = m v
  | [], [], _, _, _, _, _ => by rw [setParams]
  | [n], [T], _, a, m, v, hv => by
    classical
    haveI : Nonempty T := ⟨a⟩
    have hne : v ≠ .mk n T := fun e => hv (by simp [e])
    exact Function.update_of_ne hne _ _
  | n :: n' :: ns, T :: T' :: Ts, h, (a, as), m, v, hv => by
    classical
    haveI : Nonempty T := ⟨a⟩
    have hne : v ≠ .mk n T := fun e => hv (by simp [e])
    rw [setParams, setParams_apply_of_notMem (n' :: ns) (T' :: Ts) _ as _ v
      (fun h' => hv (List.mem_cons_of_mem _ h'))]
    exact Function.update_of_ne hne _ _
  | [], _ :: _, h, _, _, _, _ => absurd h (by simp)
  | _ :: _, [], h, _, _, _, _ => absurd h (by simp)
  | [_], _ :: _ :: _, h, _, _, _, _ => absurd h (by simp)
  | _ :: _ :: _, [_], h, _, _, _, _ => absurd h (by simp)

/-! ## Renaming -/

open Classical in
/-- View an assignment through an injective name map `ι`: slot `n : T` of the view is slot
`ι n : T` of the assignment.  Writing a view back overwrites exactly the slots in the range of
`ι`.  Types are kept, so no casts are needed (`NEW_PROCEDURES.md`, §4.2). -/
noncomputable def VariableAssignment.embed (ι : String → String) (hι : ι.Injective) :
    Lens VariableAssignment VariableAssignment where
  get m v := m (v.withName (ι v.name))
  set m' m w := if w.name ∈ Set.range ι then m' (w.withName (Function.invFun ι w.name)) else m w
  set_get m m' := by
    funext v
    simp only [VariableName.withName_name, Set.mem_range_self, if_true,
      VariableName.withName_withName]
    exact m'.apply_withName v (Function.leftInverse_invFun hι v.name)
  set_set m x y := by
    funext w
    by_cases h : w.name ∈ Set.range ι <;> simp [h]
  get_set m := by
    funext w
    by_cases h : w.name ∈ Set.range ι
    · simp only [h, if_true, VariableName.withName_withName]
      exact m.apply_withName w (Function.invFun_eq h)
    · simp [h]

open Classical in
/-- **Cleaning lemma**: a slot seen through `embed ι` is the slot of the renamed variable. -/
theorem VariableAssignment.embed_chain_varLens (ι : String → String) (hι : ι.Injective)
    (v : VariableName) :
    (embed ι hι).chain (varLens v) = varLens (v.withName (ι v.name)) := by
  ext x m w
  change (if w.name ∈ Set.range ι then
      Function.update (fun u : VariableName => m (u.withName (ι u.name))) v x
      (w.withName (Function.invFun ι w.name)) else m w)
    = Function.update m (v.withName (ι v.name)) x w
  by_cases hw : w = v.withName (ι v.name)
  · subst hw
    rw [if_pos ⟨v.name, rfl⟩, Function.update_self]
    refine (VariableAssignment.apply_withName
      (Function.update (fun u : VariableName => m (u.withName (ι u.name))) v x) v
      (Function.leftInverse_invFun hι v.name)).trans ?_
    exact Function.update_self v x _
  · rw [Function.update_of_ne hw]
    by_cases h : w.name ∈ Set.range ι
    · have hne : w.withName (Function.invFun ι w.name) ≠ v := by
        intro e
        apply hw
        refine VariableName.ext' ?_ ?_
        · rw [← e]
          simp only [VariableName.withName_name]
          exact (Function.invFun_eq h).symm
        · rw [← e]; rfl
      rw [if_pos h, Function.update_of_ne hne]
      exact m.apply_withName w (Function.invFun_eq h)
    · rw [if_neg h]

/-- Renaming along a permutation of names: an isomorphism of assignments, slot `n : T` of
`rename π m` being slot `π n : T` of `m`. -/
noncomputable def VariableAssignment.rename (π : Equiv.Perm String) :
    VariableAssignment ≃ VariableAssignment where
  toFun m v := m (v.withName (π v.name))
  invFun m v := m (v.withName (π.symm v.name))
  left_inv m := by
    funext v
    simp only [VariableName.withName_name, VariableName.withName_withName]
    exact m.apply_withName v (π.apply_symm_apply v.name)
  right_inv m := by
    funext v
    simp only [VariableName.withName_name, VariableName.withName_withName]
    exact m.apply_withName v (π.symm_apply_apply v.name)

/-- `embed` along a permutation is the isomorphism lens of `rename`. -/
theorem VariableAssignment.embed_perm (π : Equiv.Perm String) :
    embed π π.injective = Lens.bijection (rename π).symm := by
  ext m' m w
  have hw : w.name ∈ Set.range π := ⟨π.symm w.name, π.apply_symm_apply _⟩
  simp only [embed, Lens.bijection, rename, Equiv.coe_fn_symm_mk, if_pos hw]
  refine VariableAssignment.apply_withName_congr m' w (π.injective ?_)
  rw [Function.invFun_eq hw, π.apply_symm_apply]

/-! ## Program states -/

section ProgramState

variable [ProgramSpec]

/-- The state a statement runs in: the program's `globals` and the running procedure's
`locals`.  The globals are still a `State` (refactor (I), `NEW_PROCEDURES.md` §1.4). -/
structure ProgramState where
  globals : State
  locals : VariableAssignment

/-- Lens onto the globals of a `ProgramState`. -/
def ProgramState.globalL : Lens State ProgramState where
  get s := s.globals
  set v s := { s with globals := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lens onto the locals of a `ProgramState`. -/
def ProgramState.localL : Lens VariableAssignment ProgramState where
  get s := s.locals
  set v s := { s with locals := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

instance ProgramState.disjoint_globalL_localL :
    Lens.Disjoint ProgramState.globalL ProgramState.localL :=
  ⟨fun _ _ _ => rfl⟩

instance ProgramState.disjoint_localL_globalL :
    Lens.Disjoint ProgramState.localL ProgramState.globalL :=
  ⟨fun _ _ _ => rfl⟩

/-- A lens into the locals, as a lens into the program state. -/
def Lens.intoLocal {a : Type*} (x : Lens a VariableAssignment) : Lens a ProgramState :=
  ProgramState.localL.chain x

/-- A lens into the globals, as a lens into the program state. -/
def Lens.intoGlobal {a : Type*} (x : Lens a State) : Lens a ProgramState :=
  ProgramState.globalL.chain x

/-- The local variable `n : T`: its slot in the locals, as a lens into the program state.  This
is what a parameter or `var` of a `proc` stands for.  The key of the variable name is filled in
at the use site by `variable_name_key`, so for a literal `n` it is a literal, and two local
variables with different literal names are found disjoint by instance search (through
`Lens.disjoint_intoLocal` and `varLens.instDisjoint`; an `abbrev`, so that instance search sees
the slot). -/
noncomputable abbrev localVarLens (n : String) (T : Type) [Nonempty T] {key : Nat}
    (keyCorrect : key = VariableName.encode n := by variable_name_key) : Lens T ProgramState :=
  (varLens (@VariableName.mk n T _ key keyCorrect)).intoLocal

instance Lens.disjoint_intoLocal_intoGlobal {a b : Type*} (x : Lens a VariableAssignment)
    (y : Lens b State) : Lens.Disjoint x.intoLocal y.intoGlobal :=
  ⟨fun _ _ _ => rfl⟩

instance Lens.disjoint_intoGlobal_intoLocal {a b : Type*} (x : Lens a State)
    (y : Lens b VariableAssignment) : Lens.Disjoint x.intoGlobal y.intoLocal :=
  ⟨fun _ _ _ => rfl⟩

instance Lens.disjoint_intoLocal {a b : Type*} (x : Lens a VariableAssignment)
    (y : Lens b VariableAssignment) [Lens.Disjoint x y] : Lens.Disjoint x.intoLocal y.intoLocal :=
  Lens.disjoint_chain _ x y

instance Lens.disjoint_intoGlobal {a b : Type*} (x : Lens a State) (y : Lens b State)
    [Lens.Disjoint x y] : Lens.Disjoint x.intoGlobal y.intoGlobal :=
  Lens.disjoint_chain _ x y

end ProgramState

end GaudisCrypt
