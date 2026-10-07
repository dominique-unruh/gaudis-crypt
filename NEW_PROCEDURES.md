# New procedure memory model — plan and analysis

Status: **plan**, written 2026-10-03 against `main` at `ba64a93`.  Implemented so far
(2026-10-04): `VariableName` with fields `name`, `type`, instance-implicit
`nonempty : Nonempty type`, implicit `key` (a literal) and `keyCorrect`, the injective
`VariableName.encode`, and the `NameNe` instance via `NatNe` keys.  This settles §1.3 in
favour of the `Nat` key, variant (d′), and §1.1 in favour of option B (the `Nonempty` proof
lives in the name, so `VariableAssignment := (v : VariableName) → v.type` is inhabited, with
`Classical.choice` as the initial value).  Phase 0 (universe generalisation) is done.  Phase 1 is
done.  All of it is in `GaudisCrypt/Language/Variables.lean` (+ `VariablesTest.lean`): the
above, and `VariableAssignment`,
`init`, `varLens` (disjointness by instance search), `setParams` (the `Nonempty` instance of each
parameter slot comes from the argument value), `embed`/`rename` (via
`VariableName.withName`), `ProgramState` with `globals : State`, `globalL`/`localL`,
`Lens.intoLocal`/`intoGlobal`.

Phase 6 (flattening, `Logic/Inline.lean`) is done (2026-10-06), along §4 with these choices:

* the injections of §4.3 are `Flatten.escape` (caller) and `Flatten.tag` (`n ↦ "@.n"`, callee;
  no round number is needed, since each round escapes the names of the one before).  A round's
  lenses `Flatten.trafo`/`Flatten.emb` rename by exactly these, so every round is the same;
* the cosmetic renaming of §4.5 is a pass of its own after all rounds (`Flatten.renameNames`):
  one permutation `Flatten.rename ren` of the whole statement, where `ren` gives each made-up
  name (`@.w`, `@@.w`, …) a readable one (`w`, or `w0` on a clash);
* the reset of §4.4 is `assign (resetSetter S) ⟨fun _ => ()⟩` (`resetSetter`, a `Setter Unit`
  that puts every local with a name in `S : Set String` back to `init` and ignores its value):
  the values put back are a `VariableAssignment`, in `Type 1`, so they cannot be the value of an
  `assign` themselves.  Flattening emits `emb.chainSetter (resetSetter Set.univ)`; later rounds
  and the cleanup renaming map the set, which the cleaning keeps in a normal form
  (`Flatten.cleanNameSet?`), so that it prints as, e.g.,
  `reset {"z", "w0"} ∪ Flatten.prefixed "@@." \ {"@@.z", "@@.w"};`.  The statement
  `reset S;` is the surface syntax for `assign (resetSetter S) ⟨fun _ => ()⟩` (Q8), and the
  printer prints that assignment as it; any other `Setter` on the program state is an l-value
  as it is (`lval%`).  The parameters are then
  written by one tuple assignment `z₁, …, zₙ <- (args);`;
* every side condition is a generic lemma (`Flatten.equivInLens_call`), proved once; the
  procedure level (`Flatten.procedureDenotation_congr`) needs the caller's parameter names to
  stay fixed, which `escape` does for every name not starting with `@`, and the cleanup renaming
  by not choosing them as new names.

## 0. The request, restated

1. `VariableName := String × Type`.
2. `VariableAssignment := (v : VariableName) → v.type`.
3. `structure ProgramState where global : VariableAssignment; local : VariableAssignment`.
4. `StmtWithHoles` loses its `l : Type` index and the `[ProgramSpec]` instance argument; every
   statement runs on `ProgramState` (was `ProcedureState l`).
5. `ProcedureWithHoles holes sig` keeps `body` and `return_val`, now over `ProgramState` (was over
   `ProcedureState (ProcedureScope …)`), drops `locals`, and gains `parameterNames`.
6. `parameterNames : List String`, with `parameterNames.length = sig.params.length` enforced.
7. `proc.parameters : List VariableName := parameterNames.zip sig.params`.
   *Intuition:* `global` is the global state; `local` holds the procedure's local variables,
   including the slots that carry the parameters.
8. `programDenotation`, the `call'` case: make a fresh `local` part, initialise it, write the
   evaluated arguments into `proc.parameters`, run the body, return to the caller's `local`.
9. `proc` parsing/printing: no more generated `let x : Lens … := Lens.intoParams …` telescope.  By
   convention `var x : Int` makes `x` stand for `(varLens ("x", Int)).intoLocal`.
10. `varLens (v : VariableName) : Lens v.type VariableAssignment` is the lens onto slot `v`.
11. Parsing must make sure that one `x` never means `("x", Int)` and `("x", String)` at the same
    time; the `var` declaration takes care of that.  Printing must not fail when a variable cannot
    be turned back into an identifier (the name is not a valid Lean name, or two types share it);
    such a variable stays printed as a `varLens` term.
12. Rewrite the flattening pipeline (`Logic/Inline.lean`) for the new model.  Keep its structure
    where it makes sense; helpers such as "map the local `VariableName`s of a Stmt/Proc" may
    make it simpler.
13. `hoare[ … ]` follows the same convention as statement parsing, except that the `var`s in the
    block determine which `VariableName`s, and in particular which types, the pre- and
    postcondition refer to.

Section 1 covers the design problems that need a decision before coding starts.  Sections 2–4
cover the core language, the syntax and the flattening.  Section 5 is the step-by-step plan,
section 6 lists further pitfalls, and section 7 the questions.

---

## 1. Problems with the data model as literally specified

### 1.1 `(v : VariableName) → v.type` is an empty type  ⚠ blocking

`VariableName` ranges over *every* `Type`, `Empty` included.  A function
`(v : String × Type) → v.2` therefore has to produce an element of `Empty` at `("x", Empty)`, so
`VariableAssignment ≃ Empty`.  Then `ProgramState` is empty, every `hoareStmt` holds vacuously,
`procedureDenotation` can never initialise a frame, and so on.  This must change.  Options:

| | definition | init value of a fresh local | notes |
|---|---|---|---|
| **A** | `VariableAssignment := (v : VariableName) → Nonempty v.2 → v.2` | `fun _ h => Classical.choice h` | `VariableName` stays exactly `String × Type`.  `varLens ⟨n, T⟩` needs `[Nonempty T]`, which instance search supplies.  Writing a parameter slot needs no proof (`Function.update m v (fun _ => a)`).  Proof irrelevance makes `m v h₁ ≡ m v h₂`, so the extra argument costs nothing. |
| **B** | `VariableName := String × NonemptyType` (core's `NonemptyType`) | `Classical.choice` | Puts the proof into the name.  `proc.parameters` then needs a `Nonempty` proof for each parameter type, so either `ProcedureSignature.params : List NonemptyType` (a big ripple through `procsig`, module types and `typeListToTuple`, which has to stay reducible) or an extra proof field. |
| **C** | `VariableName := String × (Σ T, Inhabited T)` | `v.2.2.default` | Matches today's `locals : List (Σ t, Inhabited t)` and keeps **default-initialisation semantics**.  The instance becomes part of the variable's identity (in practice one canonical instance per type).  Parameters need `Inhabited` instances (flattening already demands that today).  Same `proc.parameters` problem as B. |

**Recommendation: A.**  It is the smallest change to items 1, 2 and 7, and nothing else needs
proofs.  **The cost is a semantic change.**  Today a fresh local starts at `default` (a `Nat`
starts at `0`).  Under A or B it starts at an *unspecified* value, so a program that reads a local
before writing it is still deterministic, but nobody can prove what it reads.  Everything that
relies on `var i : Nat` starting at `0` breaks (check `Examples/`, `Lib/RO/*`, `InlineTest`).  Easy
mitigation: `var i : Nat := 0;` sugar that emits an explicit assignment.  Possible later
(decided against for now, 2026-10-04): a class `SaneDefault α` with an instance from
`Inhabited α` and a low-priority one from `Nonempty α` via `Classical.choice`.  No such class
exists in core or Mathlib; the closest are `Classical.inhabited_of_nonempty` and Mathlib's
`Classical.inhabited_of_nonempty'`, both `def`s.  It must **not** go into `VariableName`: it is
data, so a variable's identity would then depend on which instance was found.  Instead, the
`var` handling could emit `x <- SaneDefault.default;` for each declared local.  If default-init semantics
must be kept, take C.  See question Q1.

### 1.2 Universe bump  ⚠ large ripple

`String × Type : Type 1`, so `VariableAssignment` and `ProgramState` are in `Type 1`.  Today:

* `ProgramDenotation (state : Type)` in `Semantics.lean:25` is **monomorphic in `Type`**;
* several `Footprint` definitions fix `{m : Type}` (`Footprint.lean:461–492`, `orbit_setoid`,
  `global_getter`, `touched_getter`, `HasReset`, …);
* `StmtWithHoles`, `HoleSigs.Instantiation` and `ModuleTypeRep`'s denotation carry a universe
  that is tied to `ProgramSpec.{u}`.

So `ProgramDenotation`, `while_loop`, `zoom`, `wp`, the range framework and probably PRHL all
have to become universe-polymorphic in the state (`Type u`).  `SubProbability (a : Type u)` and
`Lens (a : Type u) (b : Type v)` already are.  This is mechanical work with occasional universe
unification trouble.  **Do it first, as a separate commit**, while everything still builds on
the old model (Phase 0 below).

The alternative is to avoid the bump: `VariableName := String × Code`, where `Code : Type` is a
universe of type codes with `decode : Code → Type`.  This also makes type equality decidable
(see 1.3).  But it closes the set of allowed variable types, or brings a `ProgramSpec`-like class
back to make it extensible.  Not recommended, but it is the only bump-free design.

### 1.3 Type equality is not decidable

`("x", Int) = ("x", Nat)` can be neither proved nor refuted in Lean (`Int ≃ Nat`).  So:

* `Function.update` (needed for `varLens.set`) needs `DecidableEq VariableName`.  It has to be
  `Classical.decEq`.  Declare **one** `noncomputable instance : DecidableEq VariableName` and use
  it everywhere, to avoid instance diamonds.  Semantics are noncomputable anyway.
* `Lens.Disjoint (varLens v) (varLens w)` holds iff `v ≠ w`.  It is only *usable* via
  `v.1 ≠ w.1`, which `decide` / the `String` literal simprocs can prove.  Two variables with the
  same name and different types are neither provably disjoint nor provably equal.  That is the
  semantic reason behind item 11: one name, one type per scope.
* **Instance synthesis and `"x" ≠ "y"`.**  A plain `instance : Lens.Disjoint (varLens v) (varLens w)`
  needs `v.1 ≠ w.1` from somewhere.  Today disjointness instances are found structurally
  (`Programs.disjoint_intoLocalVars` and friends), because slot chains are built from
  constructors (`ofst`/`osnd`).  What instance search can and cannot do here, tested on
  Lean v4.31.0 (scratch files, 2026-10-03) and checked against the source
  (`Lean/Meta/ExprDefEq.lean`, `Lean/Meta/Offset.lean`, `Lean/Meta/DiscrTree/Main.lean`):
  * **Two filters.**  Instance search first *retrieves* candidate instances from a discrimination
    tree keyed on the head symbols of their conclusions, and only then *unifies*.  An instance
    keyed on `false` is never even tried for a goal `IsFalse (Nat.beq 3 4)`, whatever the
    unifier could do.  To let the unifier work, use an instance whose conclusion is all
    variables (e.g. `instance : BoolEq a a`), which retrieval never filters out.
  * **The unifier has hard-coded rules for literals** (`isExprDefEqExpensive` tries them in this
    order, after `whnfCore`):
    * `isDefEqNative`: `Lean.reduceBool`/`Lean.reduceNat`, i.e. evaluation by compiled code;
    * `isDefEqNat`: on *ground* terms (no fvars or mvars), `Nat.succ/add/sub/mul/div/mod/pow/
      gcd/beq/ble/land/lor/xor/shiftLeft/shiftRight` applied to literals are evaluated with GMP.
      Tested: `BoolEq (Nat.beq 123456789012345678901 123456789012345678902) false` is found;
    * `isDefEqOffset`: `s + k₁ =?= t + k₂` and `s + k =?= v` with `k`, `v` literals (also
      `Nat.succ`) are reduced by subtracting.  The offset is read off the *right* operands:
      `(x + 3) + 1` is "`x` plus 4", and `x` may be an unknown;
    * `isDefEqStringLit`: `"…" =?= String.ofList cs` expands the literal to
      `String.ofList [Char.ofNat 120, …]`.  Tested: `StrEq "xy" (String.ofList ['x', 'y'])` is
      found via `instance : StrEq a a`.
  * **No decision procedure is run**: `decide (3 = 4)`, `decide ("x" = "y")` and `"x" == "y"` all
    fail even with the all-variables instance.  They reduce only by unfolding `Nat.decEq` /
    `String.decEq`, which are not reducible, and instance search unfolds only reducible
    definitions and instances.
  * Hence **`String` inequality *can* be decided in instance search**, structurally:
    1. open each literal into `String.ofList [Char.ofNat n₁, …]` through an all-variables
       instance with an `outParam` (`class StrEq (a : String) (b : outParam String)`);
    2. compare the character lists with one instance per case: head differs, or tail differs,
       or one list is empty (backtracking does the rest);
    3. compare characters by code point with a single offset instance
       `instance : NatLt a (k + a + 1)`.  The unifier turns `?k + a + 1 =?= b` into
       `?k := b - a - 1` in one step.  The order matters: `a + k + 1` does **not** work,
       because the unknown has to be the leftmost summand.

    Tested: `StrNe "x" "y"`, `StrNe "count" "cnt"` and
    `StrNe "random_oracle_state" "random_oracle_stats"` are found, and `StrNe "x" "x"` correctly
    fails.  Open: the experiment `sorry`s the two `Char.ofNat` injectivity facts.  Those are
    true for valid code points (it restricts to `< 0xd800`; a second range instance covers code
    points above the surrogates) but have to be proved.

    **Length limits** (measured, default options):
    * *total length of either string* ≤ about 125 characters, wherever the strings differ.
      Beyond that, opening the literal into a nested `List.cons` term hits `maxRecDepth` (512):
      `"x" ++ 125×"a"` vs `"y" ++ 125×"a"` fails, and so does `"x"` vs a 251-character string;
    * *common prefix* ≤ about 120 characters, because each shared character adds one instance to
      the solution, and `synthInstance.maxSize` is 128.  This limit goes away with "skip `k`
      characters" instances (`CharsNe (x₁ :: … :: x₈ :: xs) (y₁ :: … :: y₈ :: ys)` from
      `CharsNe xs ys`), which are sound because the tail-differs case never needs the heads to be
      equal.  Instance search caches subgoals, so the extra backtracking stays cheap.  With
      skip-8 and `maxRecDepth 4096`, 500- and 900-character common prefixes are decided, and
      equal 900-character strings fail, in about 1.5 s for the whole test file.

    `maxRecDepth` cannot be raised from inside an instance; it is an option at the use site.  So
    names longer than about 125 characters are out of reach without a `set_option`.  Variable
    names, including namespaced globals (`GaudisCrypt.Lib.RO.OneWayness.bad`, about 35
    characters), are far below that.  Exceeding a limit is a loud elaboration error ("maximum
    recursion depth has been reached"), never a wrong answer.  The tactic route (a) remains
    available for such cases.
  * For comparison: recursing one successor at a time (`NatNe (a+1) (b+1)` from `NatNe a b`) is
    linear in the *values*: `NatNe 100 101` is found, `NatNe 250 251` exceeds the default
    `synthInstance.maxSize`.  Lists are fine structurally (literals are `List.cons`
    applications).
  * Outside instance search, all of this is easy: `"x" ≠ "y" := by decide`,
    `("x" = "y") = False := by simp`, and `Function.update f "x" 5 "y" = f "y" := by simp` all go
    through.  (In this Lean version `String` is a UTF-8 `ByteArray` structure; `String.mk` is
    deprecated in favour of `String.ofList`.)

  This applies equally to design 2 of §9.  Ways to provide `[Lens.Disjoint x y]` (e.g. for
  `Lens.pair` in a tuple l-value `a, b <- …`):
  (e) **structural string instances** as above, so that
  `instance [StrNe n₁ n₂] : Lens.Disjoint (varLens n₁ _) (varLens n₂ _)` is found automatically,
  with `String` names kept.  These are the most general ones: they work wherever instance
  search runs.  They depend on unifier details (`isDefEqStringLit`, the offset rule, retrieval
  of all-variables instances), so pin them with tests;
  (a) the `[lval|]` macro supplies the instance explicitly,
  `Lens.pair x y (self := by gaudi_disjoint)`, where `gaudi_disjoint` unfolds to a name
  inequality and runs `decide`;
  (b) a `Fact (n₁ ≠ n₂)`-based instance plus explicit `Fact` instances (does not scale);
  (c) a `Setter.pair` with a tactic-discharged side condition (this also fixes the two l-value
  TODOs at the end of `ProgramSyntax.lean`);
  (d) **key variables by a `Nat` code instead of a `String`.**  Instance search *can* compare
  `Nat` literals of any size in one step, through the unifier's literal-offset rule.  Option (e)
  makes this unnecessary unless (e) turns out to be too slow or too fragile:
  ```lean
  class NatLt (a b : Nat) : Prop where lt : a < b
  instance (a k : Nat) : NatLt a (k + a + 1) := ⟨by omega⟩   -- `?k + a + 1 =?= b` ⇒ `?k := b - a - 1`
  instance [NatLt a b] : NatNe a b   -- and the mirrored instance
  ```
  Tested: `NatNe 987654321987654321 987654321987654322` (both orders), a 30-digit
  `NatLt`, and `NatLt 0 (2 ^ 64)` are all found, the kernel accepts the proofs, and
  `NatLt 7 7`, `NatLt 8 7`, `NatNe 42 42` correctly fail.  It scales: with **1,000,000-digit**
  literals built by a metaprogram (`mkNatLit`), instance search takes about 1 ms and the kernel
  (checked synchronously, `Elab.async false`) at most 1 ms.  This holds whether the numbers
  differ in the last digit, the first digit, or are far apart, and equal numbers are correctly
  rejected in under 1 ms.  The cost lies elsewhere: *parsing* a decimal numeral looks
  quadratic (100,000 digits 2.7 s, 300,000 digits 18.7 s per literal), and so is printing one
  (in error messages, `toString`).  Irrelevant at the sizes that matter here, since a name of
  20 characters is about 50 digits.  So with names encoded injectively as
  `Nat`s (UTF-8 bytes in base 256, behind a leading sentinel byte; a 20-character name is a
  ~170-bit number), `Lens.Disjoint (varLens n₁ _) (varLens n₂ _)` becomes an ordinary
  instance with `[NatNe n₁ n₂]`.  The macro has to emit the code as a literal
  (`varLens 0x0178 Int`), because instance search will not evaluate `encode "x"`.  Costs: raw terms show numbers, so a delaborator that decodes them
  is mandatory (`pp.gaudisCrypt false` output and error messages become hard to read), and a
  helper is needed to go from string to code in hand-written terms.  Gains: disjointness of
  variables is found by instance search everywhere it is needed (tuple l-values,
  `commute_of_disjoint_lens`, range-framework instances), not only where a macro can insert a
  tactic.  `DecidableEq Nat` is computable, and the kernel compares big literals with GMP.
  Variant (d′): keep the `String` as *the* name and add a `Nat` key with a proof,
  `structure VarName where name : String; key : Nat; key_eq : key = encode name`, where the
  macro emits `key` as a literal and `key_eq` is proved by `decide`.  The key need not even be
  injective: a hash will do, since different keys imply different names (sound), and a
  collision only means the instance is not found (fallback: tactic).  Native evaluation
  (`Lean.reduceBool`, `isDefEqNative`) is no alternative: it only accepts a closed *constant*
  (`reduceBool c` with `c` a constant name), not `reduceBool (decide (a ≠ b))` for arbitrary
  `a` and `b`.
  Recommendation: **(e)**, with a regression test file for the instance machinery; (a) as the
  fallback if (e) proves fragile across Lean updates.  (d) only if (e) is too slow on long names.

### 1.4 What is `global`?  Is `ProgramSpec` gone completely?

Item 3 makes `global : VariableAssignment`, and item 4 drops `[ProgramSpec]`.  Taken literally,
`ProgramSpec`/`State` disappear from the whole project, and global variables become slots of
`global` as well, e.g. `(varLens ("ro_state", T)).intoGlobal`.  Benefits:

* `axiom random_oracle_state : Lens … State` plus axiomatised disjointness can become
  *definitions* whose disjointness is a name inequality;
* the `ModuleExpression.lean:407` problem (no `[ProgramSpec]`-parameterised declaration is
  usable by the tactic) goes away.

Cost: the whole `Lib/RO` layer, `FV.lean`, `WeakestPreconditions.lean`, the PRHL files and the
examples (29 files mention `ProgramSpec`) have to migrate.
`Lib/RO/InstantiateCommon.lean:26` (`instance roSpec : ProgramSpec := ⟨state⟩` with a concrete
`state`) needs careful thought.  A cheap first step that keeps most of them compiling:
`abbrev State := VariableAssignment`, keep global variables as (axiomatised) `Lens T State`, and
delete `[ProgramSpec]` binders.

**Recommendation:** split into two independent refactors:
**(I)** locals and procedures (items 4–13), with `global : State` *temporarily* kept under
`[ProgramSpec]`; then **(II)** globals as a `VariableAssignment`, with `ProgramSpec` removed.
Doing (I) first keeps the diff reviewable and keeps `Lib/RO` out of it.  If (I) and (II) must
land together, Phase 0 also has to cover the RO layer.  See question Q2.

### 1.5 Parameter names: duplicates, and parameters vs. `var`s

* `parameterNames = ["x", "x"]` with types `[Int, Int]` makes `zip` produce the same variable
  twice.  Initialisation then writes the slot twice (the last argument wins).  This is well
  defined but almost certainly unintended.  Propose `parameterNames.Nodup` as a second proof
  field, which is decidable on `String` and discharged by `decide` in the macro.  See Q3.
* `proc (x : Int) { var x : Int; … }` (a redeclaration) and `var x : Int, x : Bool` must be parse
  errors (item 11).  A `var` with the same name *and* type as a parameter is still an error:
  silent aliasing is never what was meant.

---

## 2. Core-language changes (items 1–8, 10)

### 2.1 New definitions (`Language/Programs.lean`, or a new `Language/Variables.lean`)

```lean
def VariableName := String × Type          -- Type 1
abbrev VariableName.name (v : VariableName) : String := v.1
abbrev VariableName.type (v : VariableName) : Type   := v.2

noncomputable instance : DecidableEq VariableName := Classical.decEq _

-- option A of §1.1
def VariableAssignment := (v : VariableName) → Nonempty v.type → v.type
noncomputable def VariableAssignment.init : VariableAssignment := fun _ h => Classical.choice h

/-- Item 10. -/
noncomputable def varLens (v : VariableName) [Nonempty v.type] : Lens v.type VariableAssignment where
  get m   := m v inferInstance
  set x m := Function.update m v (fun _ => x)
  -- laws: Function.update_self / update_idem / update_eq_self (+ funext over the proof argument)

theorem varLens_disjoint {v w} [Nonempty v.type] [Nonempty w.type] (h : v.name ≠ w.name) :
    Lens.Disjoint (varLens v) (varLens w)        -- Function.update_comm

structure ProgramState where
  global : VariableAssignment        -- or `State` during refactor (I), see §1.4
  «local» : VariableAssignment        -- `local` is a keyword: field name needs «» or a rename

def ProgramState.globalL : Lens VariableAssignment ProgramState
def ProgramState.localL  : Lens VariableAssignment ProgramState
instance : Lens.Disjoint ProgramState.globalL ProgramState.localL     -- and the symmetric one

def Lens.intoLocal  (x : Lens a VariableAssignment) : Lens a ProgramState := ProgramState.localL.chain x
def Lens.intoGlobal (x : Lens a VariableAssignment) : Lens a ProgramState := ProgramState.globalL.chain x
-- disjointness: intoLocal/intoGlobal always (no hypothesis); intoLocal x / intoLocal y from x ⊥ y
```

`local` is a reserved keyword, and so is `global` in some contexts.  Write `«local»` or rename
to `locals`/`globals`.  Recommendation: `globals`/`locals`, which matches the intuition paragraph
of the request anyway.

### 2.2 Statements and procedures

```lean
inductive StmtWithHoles : HoleSigs → Type 1 where
  | skip
  | sample {a} : Setter a ProgramState → Getter (SubProbability a) ProgramState → StmtWithHoles h
  | call' {sig} : Setter sig.ret ProgramState
      → (paramNames : List String) → paramNames.length = sig.params.length
      → StmtWithHoles .empty                    -- callee body
      → Getter sig.ret ProgramState             -- callee return value
      → Getter sig.ParamType ProgramState       -- arguments, read in the caller's state
      → StmtWithHoles h
  | hole {sig} (n : HoleIndex h sig) : Setter sig.ret ProgramState → Getter sig.ParamType ProgramState → StmtWithHoles h
  | seq | ifThenElse | while    -- unchanged, minus `l`

structure ProcedureWithHoles (holes : HoleSigs) (sig : ProcedureSignature) where
  parameterNames : List String
  parameterNames_length : parameterNames.length = sig.params.length := by rfl   -- autoParam
  -- parameterNames_nodup : parameterNames.Nodup := by decide                   -- Q3
  body       : StmtWithHoles holes
  return_val : Getter sig.ret ProgramState

def ProcedureWithHoles.parameters (p) : List VariableName := p.parameterNames.zip sig.params
```

Note that `call'` now carries **the parameter names** in place of `locals`, plus the length
proof.  `StmtWithHoles.call`, `instantiate`, `depth`, `instantiate_empty` and
`procedureWithHoles_eta` follow mechanically.

The universe is fixed at `Type 1` (no more `ProgramSpec.{u}`), and the same goes for
`HoleSigs.Instantiation`.  Check `ModuleTypeRep`'s denotation and `Module T`, which are currently
stated at `Type (max 1 instU)`.

### 2.3 Writing the arguments into the parameter slots

```lean
/-- Write a `typeListToTuple tys` argument tuple into the slots `names.zip tys`. -/
def VariableAssignment.setParams : (names : List String) → (tys : List Type) →
    names.length = tys.length → typeListToTuple tys → VariableAssignment → VariableAssignment
```

Recursion on both lists, with the same three-case split as `typeListToTuple`
(`[]` / `[x]` / `x :: y :: _`).  The tuple irregularity only shows up here and in `delab`/meta
code, not in the locals any more.  Since `Function.update` with `fun _ => a` needs no `Nonempty`
proof, option A has no proof obligations here.

### 2.4 Semantics (item 8)

```lean
| .call' x names hlen body ret args => do
    let argValues ← ProgramDenotation.get args
    let retVal ← ProgramDenotation.zoom ProgramState.globalL
                   (procedureDenotation ⟨names, hlen, body, ret⟩ argValues)
    ProgramDenotation.set x retVal

def procedureDenotation (proc : Procedure sig) (args : sig.ParamType) :
    ProgramDenotation VariableAssignment sig.ret := fun g => do
  let loc := VariableAssignment.setParams proc.parameterNames sig.params proc.parameterNames_length
               args VariableAssignment.init
  let (_, st') ← programDenotation proc.body ⟨g, loc⟩
  return (proc.return_val.get st', st'.globals)
```

This is structurally the same as today.  `zoom globalL` already discards the callee's frame and
keeps the caller's, so "create a temporary local part" is exactly the `⟨g, loc⟩` above.
`procWrap`, `procedureDenotation_eq_procWrap_gen` and `wp_procWrap` follow, with `L` gone.

### 2.5 Expression layer (`ExpressionSyntax.lean`)

`CurrentState S` / `Evaluatable S X T` lose the `S` parameter, along with the `outParam` tricks
that exist only to infer it.  Instances:

* `Getter T ProgramState`, `Lens T ProgramState` — read directly;
* `Lens T VariableAssignment` / `Getter T VariableAssignment` — **convention: a bare lens into a
  `VariableAssignment` is a global** (today: a bare lens into `State` is a global).  During
  refactor (I) this is still `Lens T State`.

`LiftLens` collapses to two instances (`VariableAssignment`/`State` ↦ `globalL.chain`,
`ProgramState` ↦ itself).  If globals are written as `Lens T ProgramState` (`.intoGlobal`) from
the start, mixed global/local tuple l-values type-check (one of the two TODOs at the end of
`ProgramSyntax.lean`).  Only the disjointness instance is then missing, which is §1.3.

---

## 3. Syntax: parsing and printing (items 9, 11, 13)

### 3.1 Parsing: use `letI`, not syntactic substitution

Item 9 asks that `x` be *replaced* by `(varLens ("x", Int)).intoLocal`.  Doing that by walking
the syntax tree and substituting identifiers is **wrong in general**: Lean binders inside the
body (`let x := …;` statements, `fun x => …`, `∑ x ∈ s, …`, `∀ x`, `match`, set-builder, `do`
notation, …) shadow `x`, and a syntactic walker cannot know them all.

Recommended: let Lean do the scoping.  The macro emits

```lean
letI x : Lens Int ProgramState := (varLens ("x", Int)).intoLocal
…body…
```

`letI` *inlines its value during elaboration* (the existing docs in `ProgramSyntax.lean` already
rely on this: "`letI`/`haveI` … inline their value during elaboration, so no binder of theirs
survives in the term").  So the elaborated term contains `(varLens ("x", Int)).intoLocal` at every
use, with no `let`, and shadowing is handled correctly by construction.  No meta code is needed.
Commit `2247c01` moved the Hoare triples from `letI` to `let` *precisely so that* names survive
for printing.  Under the new model the name lives in the `varLens` argument, so it is `letI`
again.

Fallback if `letI` ever inlines too eagerly or too lazily (e.g. under postponed elaboration
problems): make `proc` a term elaborator that elaborates under `withLetDecl` and then
`instantiate`s the let-bound fvar by its value (`Expr.replaceFVar`), after
`synthesizeSyntheticMVarsNoPostponing`.

Name → string: take `id.getId`, require it to be **atomic** (`Name.str .anonymous s`, after
`eraseMacroScopes`), and use `s`.  Reject hierarchical names in `var`/parameters: `a.b` versus
`«a.b»` would both map to the string `"a.b"`.

Parameters: `proc (x : Int, y : Bool)` gives `parameterNames := ["x", "y"]`, and `x`/`y` are bound
exactly like `var`s, so a parameter is just a local whose slot the call initialises.  The
`Lens.intoParams`/`Lens.intoLocalVars`/`ProcedureScope`/`mkChain`/`navSteps` machinery for
locals is deleted.  `mkChain`/`navSteps` stay, but only for **argument tuples**
(`hoare[ M (x, m) : … ]` and `mkArgTuple`).

Holes: unchanged.  They are still `let h : HoleIndex … := …`, which are not lenses, and are
printed by name as now.

### 3.2 Scoping pitfall: nested `proc` literals  ⚠

Today a frame's variables are lenses into *that frame's* `ProcedureState (ProcedureScope …)`
type, so using an outer procedure's local inside an inline callee is a **type error**.  After the
change every frame has the type `ProgramState`.  In

```
proc () { var x : Int; … call (proc () { x <- 1; return () }) (); … }
```

the inner `x` is the outer `letI`-bound name, so it elaborates to `(varLens ("x", Int)).intoLocal`
and **silently refers to the callee's own `x`**.  The type checker no longer catches it.
Mitigations, in increasing cost:

1. Accept it and document it ("program variables are frame-relative names").
2. Have `proc` shadow every outer program variable.  Each `var`/parameter `letI` also leaves a
   marker binder (e.g. `_gaudi_var_x : GaudiVarMarker := ⟨⟩`), and an inner `proc` re-binds every
   marked name in scope to an error term (`letI x := gaudiOutOfScope "x"`, which elaborates to a
   custom error).  The marker is erased by `letI` as well.
3. A full elaborator-level scope stack (custom `TermElabM` state).

Recommendation: 2, if easy; otherwise 1.  See Q6.

### 3.3 Printing (item 11)

Plan for `delabProc` (and `delabGaudiProg` and `delabHoareStmt`):

1. **Collect** every `Lens.intoLocal (varLens (n, T))` with literal `n` in body and return value
   (an `Expr` traversal; ignore occurrences under a nested `ProcedureWithHoles.mk`/`call'`
   callee, which belong to a different frame).  Add the parameters (`parameterNames.zip
   sig.params`).
2. **Decide** for each name `n` whether it is printable as an identifier:
   * exactly one type `T` for `n` in this frame (compare types with `isDefEq` at reducible, or
     with `==` up to `instantiateMVars`);
   * `Name.mkSimple n` round-trips: not empty, and not containing `»` (anything else can be printed
     with `«…»` quoting, which `mkIdent` does automatically, so `"x y"` prints as `«x y»`);
   * no clash: `n` is not a let/have binder name on the body's spine, and no *other* identifier in
     the printed output is `n` (e.g. a global constant `x`).  Check afterwards, like the existing
     `syntaxHasIdent` guard, and drop the variable from the printable set if the check fails.
3. **Re-introduce the binders at delab time**: `kabstract` each printable `varLens` term out of
   the body/return, wrap the result in `let n := varLens…; …` locally, and reuse the existing
   `withPeeledLets` + `delabGaudiStmts` path.  The fvars then print as `n`, and `§n` comes out for
   free.  This keeps almost all existing printing code.
4. Non-printable variables are not abstracted, so they print as
   `§((varLens ("x y", Int)).intoLocal)`.  This needs a decent printing of
   `varLens ("x", Int)`, and the result must re-parse to the same term (add a `#roundtrip` test).
5. `var` lines: the printable non-parameter variables, in first-occurrence order.  Order is
   irrelevant to the term (there is no locals list any more), so round-tripping is unaffected.
   A declared but unused `var` is lost on printing.  That is fine, because the term is the same.
6. Parameters must be printable, or the `proc (…)` header cannot be written.  If one is not,
   either the whole `proc` delaborator steps aside (Lean's default output), or the header syntax
   grows a string-literal form `proc ("x y" : Int)`.  See Q5.

Standalone statements (`GaudiProg[ … ]` with no surrounding `proc`) have no `var` header today.
Either add an optional leading `var` line to `GaudiProg[ ]` (recommended: same code path as
`hoare[ ] { var … }`), or print local variables there as raw `varLens` terms.  See Q4.

### 3.4 `hoare[ … ]` (item 13)

* **Statement triples** `hoare[ P ==> Q ] { var x : Int; … }`: the `var`s produce `letI`s around
  the body *and* around `P`/`Q`, so `§x` in a condition is the same `varLens ("x", Int)` slot of
  `locals` that the body uses.  The type `Int` comes from the declaration.  That is the "the vars
  indicate the variable names and types in pre/post" of item 13.  The spine `let`/`have`
  repetition (`wrapSpineBinders`) stays.  `hoareStmt` becomes
  `hoareStmt (A : ProgramState → Prop) (p : Stmt) (B : ProgramState → Prop)`, and the
  `ProcedureScope [] locals` carrier disappears.
* **Procedure triples** `hoare[ M (x, m) : P ==> Q ]`: two options.
  (a) Keep `hoareProc A p B` with `A : sig.ParamType → globals → Prop` and today's elaborator.
  Replace the `Getter.mk fun _ => slot.get args` lets by `letI`s and the `ProcedureState Unit`
  carrier by `ProgramState` with an `init` local part.
  (b) **Better, and newly possible:** state `A` over the *entry* `ProgramState` of the callee's
  frame, whose locals are `setParams … args init`.  Then `§x` in the precondition is literally
  `(varLens ("x", T)).intoLocal`, *the same term as in the body*.  Today it has to be the same
  slot chain, kept in sync by hand.  The names would come from `p.parameterNames`, so
  `@[gaudiProcParamNames]` is no longer needed for concrete procedures, only for abstract module
  fields.  Option (b) changes `hoareProc`'s type, and with it `hoareProc_as_hoareStmt` and every
  use.
* `hoareProc_as_hoareStmt`: `resL`/`argsL` and the `typeListToTuple.headL/tailL/cons` scaffolding
  become `varLens` slots `("res", ret)` plus fresh argument names in the caller's locals.  The
  argument names only have to differ from `"res"`, because the callee frame is separate.  Under
  option A of §1.1, `varLens ("res", sig.ret)` needs `Nonempty sig.ret`.  Either take it as a
  hypothesis, or observe that the triple is trivial when `sig.ret` is empty.

I am not sure what "the var's inside the left/right" refers to.  I read it as "the `var` block
of the program, versus the conditions written left of the block".  If it means the two programs
of a future relational (pRHL) `equiv[ c₁ ~ c₂ : P ==> Q ]` syntax, the same scheme applies per
side, with `x{1}`/`x{2}` resolving through the left and right `var` blocks.  See Q7.

---

## 4. Flattening (`Logic/Inline.lean`, item 12)

The existing pipeline (§§1–11 of `Inline.lean`) keeps its architecture: lenses everywhere,
`applyLens`, flatten / clean / re-associate passes, `EquivInLens` soundness.  What changes is
the *widening*.

### 4.1 What becomes simpler

There is no locals list and no type index on statements, so all of this disappears:
`ProcedureScope`, `localTypes`, `tupleApp`/`tupleSuffix`/`tupleBlock`/`tupleSplit`,
`ProcedureScope.mapVars`/`embedInLocalVars`, `ProcedureState.mapScope`, the five-lemma
interface, the tuple-irregularity base cases, `newLocals` in `FlattenStep`/`FlatteningResult`,
the "literal locals list" condition of §2, and `exposeStmt`/`retelescope` (there is no telescope
to zeta and rebuild, because the names *are* the `varLens` arguments).  Statement-level
`EquivInLens` becomes `Lens ProgramState ProgramState`, with no change of type.

### 4.2 The new widening: name injections

Renaming must preserve types definitionally, so rename **names only**:

```lean
/-- View an assignment through a name map: slot `(n, T)` of the result is slot `(ι n, T)` of `m`. -/
def VariableAssignment.embed (ι : String → String) (hι : ι.Injective) : Lens VariableAssignment VariableAssignment
  get m      := fun v => m (ι v.1, v.2)
  set m' m   := fun w => if h : w.1 ∈ Set.range ι then m' (choose h, w.2) else m w   -- no casts needed
```

(`(ι (choose h), w.2)` and `w` have the same second component, so no cast is involved.)  A
permutation `π : Equiv.Perm String` gives an *iso* `VariableAssignment.rename π`, the special
case with surjectivity.  Cleaning lemma, by `rfl`/`funext`:

```
(embed ι).chain (varLens (n, T)) = varLens (ι n, T)
```

so `trafo.chain ((varLens (n,T)).intoLocal) = (varLens (ι n, T)).intoLocal`.  With literal `n`
and a concrete `ι`, `ι n` reduces by `decide` or a string simproc.

### 4.3 Freshness by construction (no footprint obligations)

Getters and setters are opaque functions on `ProgramState`, so *which* locals a statement
touches is not syntactic.  The callee may even read the whole `locals`.  Picking "fresh names
not used by the caller" is therefore **unsound** without a footprint proof.  Instead, keep
today's trick and make the caller's and callee's regions disjoint by construction:

* `ι₁` (the caller, inside `trafo`): **escape** — `ι₁ n = n` unless `n` starts with a reserved
  marker `@`, in which case `ι₁ n = "@" ++ n`.  It is injective, and its image is the set of names
  that do not start with `@` plus those that start with `@@`.  On every normal identifier it is
  **the identity**, so the caller's variables keep their names.
* `ι₂` (the callee, inside `emb`): `n ↦ "@k." ++ n`, with `k` the round number.  Its image starts
  with `@` but not with `@@`, so it is disjoint from `ι₁`'s image.  This is proved once,
  generically.
* `trafo := ProgramState.mapLocal (embed ι₁)`, `emb := ProgramState.mapLocal (embed ι₂)`.  The
  side conditions of `equivInLens_flattenCall` (both preserve globals; writing through `emb` is
  invisible through `trafo`) follow from disjoint ranges.  They are no longer "`rfl` at concrete
  lists", but one generic lemma.

### 4.4 Re-initialising the callee's frame

Today: `w <- default;` per callee local, a finite list.  Now the callee's frame is a *whole*
`VariableAssignment` (all names), so the sound prelude is **one** statement that resets the
whole region,

```
emb-region <- init;      -- (ProgramState.localL.chain (embed ι₂)) := VariableAssignment.init
z₁ <- π₁ args; …         -- parameters, via (varLens (ι₂ zᵢ, Tᵢ)).intoLocal
```

followed by `body.applyLens emb` and the return store, as today.  The region reset is sound
without knowing anything about the callee, but it **does not print** as surface syntax.  Options:

1. Print it as a dedicated statement form (e.g. `reset @1;`), which needs new syntax plus a
   delaborator.
2. Drop it when the callee provably reads none of its locals before writing them.  That needs a
   footprint argument (the range framework, `Program.inRange` over a `LensRange` generated by the
   finitely many `varLens` the cleaned callee mentions).  Harder, but a nice use of the framework.
3. Replace it by per-variable resets `w <- Classical.choice …` for the variables the cleaned
   callee mentions, *if* a syntactic check confirms the callee body only accesses locals via
   literal `varLens`.  This still needs a proof that the remaining slots are untouched, so it is
   2 in disguise.

Recommendation: 1 now, 2 later.  See Q8.  Under option C of §1.1 the reset value would be
`default` per slot, which prints more naturally as `w <- default;` once the variable set is known.

### 4.5 Cosmetic renaming pass

The callee's variables come out as `@1.w`.  They are valid strings but print through `«@1.w»`,
or degrade.  Add a final **permutation pass**: `rename π` with `π` a product of `Equiv.swap`s
(`"@1.w" ↔ "w0"`, picking names unused in the printed result).  A permutation is an iso, so:

* **statement level:** fold it into `trafo` (`trafo' = rename π ∘ trafo`).  Sound with no side
  condition;
* **procedure level:** procedure-internal locals are invisible from outside, and `init` and
  `setParams` are invariant under permutation when `parameterNames` is permuted along.  So
  `procedureDenotation` is unchanged.  One lemma: `procedureDenotation (p.rename π) = procedureDenotation p`.

This is the "map local VariableNames in Stmt/Proc" helper from item 12:
`StmtWithHoles.mapLocals (ρ : Lens VariableAssignment VariableAssignment) := applyLens (ProgramState.mapLocal ρ)`,
`ProcedureWithHoles.renameLocals (π : Equiv.Perm String)`.  It is useful on its own as well, for
alpha-renaming procedures before comparing them.

Choosing `π`: the names "used" by the caller, read off the cleaned term (literal `varLens`
names).  If the term has opaque local accesses, this is not the true footprint, but `π` is
sound regardless.  Only the *printing* might then be misleading, and it is still faithful,
because the names are in the term.

### 4.6 What carries over unchanged

`Lens.chainGetter`/`chainSetter`, `applyLens` (minus the `l` index), `programDenotation_applyLens`
(with universe adjustments), the `zoom_*` lemmas, `EquivInLens` and its congruences,
`flattenSeq`, §11 `unfoldProcedure`/`inline*`, the call-numbering walk, and the test harness in
`InlineTest.lean`.  The "flattenable" condition (§2) becomes: `parameterNames` and `sig.params`
are literal lists.  Parameter types no longer need `Inhabited` under option A.

---

## 5. Step-by-step plan

Each phase ends with a green `lake build`.

**Phase 0 — universe generalisation (no semantic change).**
Make `ProgramDenotation`, `while_loop`, `zoom`, `wp*`, `Footprint`, `LensRange` and the PRHL
judgments universe-polymorphic in the state type.  Fix what breaks.  Keep it as its own commit.

**Phase 1 — variables.**
Add `VariableName`, `VariableAssignment` (option per Q1), `varLens` with its laws and
`varLens_disjoint`, `VariableAssignment.init`, `setParams`, `embed`/`rename` with their lemmas,
`ProgramState`, `globalL`/`localL`, `intoLocal`/`intoGlobal`, and the disjointness instances.
Put them in a new `Language/Variables.lean` with a `VariablesTest.lean`.  Additive only;
nothing uses them yet.

**Phase 2 — core switch (`Programs.lean`).**
`StmtWithHoles`, `ProcedureWithHoles`, `call'`, `instantiate`, `programDenotation`,
`procedureDenotation`, `procWrap`.  Delete `ProcedureState`, `ProcedureScope`, `localTypes`,
`localDefaults`, `localVariableInit`, `intoParams`/`intoLocalVars` and their instances.  Update
`RENAME.md`.

**Phase 3 — downstream semantics.**
`WeakestPreconditions.lean` (`procWrap`, `wp_procWrap`, `procedureWithHoles_eta`), `FV.lean`
(`globalL_liftSubProbability_*`), `Logic/Hoare.lean` (including `hoareProc_as_hoareStmt`),
`EagerProc.lean`, `TransferBy`, `Lib/RO/*`
(`InstantiateCommon`/`GlobEndpointExample`/`ROCouplingEquiv`, which use `ProcedureScope`
heavily), and `Examples/Pedersen`.  Expect the RO files to be the biggest chunk.  Keep a list of
proofs that relied on default-initialised locals (§1.1).

**Phase 4 — syntax.**
`ExpressionSyntax.lean` (`CurrentState`/`Evaluatable`/`LiftLens` simplification), the
`ProgramSyntax.lean` `proc` macro (`letI` scheme, name checks, `parameterNames`), the `[lval|]`
disjointness discharge (§1.3), the delaborators (§3.3), `GaudiProg[ var …; ]` (Q4), and
`ModuleSyntax.lean` (the `module` command builds procs; `@[gaudiProcParamNames]` stays for
`moduletype` fields and can be cross-checked against `parameterNames` for concrete procs).
Tests: update `ProgramSyntaxTest`/`ModuleSyntaxTest` and add `#roundtrip` cases for the
degradation paths (two types for one name, `«x y»`, a clash with a global constant, a nested
`proc` literal).

**Phase 5 — Hoare syntax.**
`HoareSyntax.lean` (both forms; decide (a)/(b) of §3.4), `HoareSyntaxTest.lean`, and
`Pedersen.lean` (`pedersen_correctness2` uses `hoare[ ]`).

**Phase 6 — flattening.**
Rewrite `Logic/Inline.lean` along §4.  Rewrite the plan comment at the top of the file first,
then the lens layer, then the meta code.  Keep the `#flatten*` test commands and adapt
`InlineTest.lean`'s expected outputs.

**Phase 7 (only if Q2 = together) — globals.**
`State := VariableAssignment`, remove `ProgramSpec`, and turn the RO globals into named slots.

---

## 6. Further pitfalls

* **`whnf`/reducibility of `typeListToTuple`.**  It is still needed for argument tuples
  (`sig.ParamType`) and keeps its `@[reducible]` reasons (see the docstring in `Programs.lean`).
  `localTypes` can go.
* **`Function.update` simp behaviour.**  `simp` must decide `("x", Int) ≠ ("y", Int)` to apply
  `Function.update_of_ne`.  `Prod.mk.injEq` plus the core `String` literal simprocs should do it.
  With the *same* name and different types, `simp` gets stuck on `Int = Nat`, which is another
  reason for the one-type-per-name rule.  Add a dedicated simp lemma
  `varLens_get_set_of_name_ne` with a `decide`-able hypothesis.
* **wp computations get heavier.**  Today a local read is a tuple projection (`rfl`).  Afterwards
  it is a `Function.update` chain over a classical `DecidableEq`.  Proofs in `Lib/RO` and
  `Examples/` that are now `rfl`/`simp` may need the new simp set.  Budget for it in Phase 3.
* **`call'` carrying a `Prop` field** (the length proof): matching or `whnf`-ing on `call'` in meta
  code has one more argument.  Update arities in every `getAppFnArgs` match: the delaborators,
  `callData?` in `Inline.lean`, and the `args.size == 7` guards.
* **Hygiene.**  A `var tmp` written inside a user macro gets a macro-scoped name.  Erasing the
  scopes makes two hygienic `tmp`s from different expansions *the same variable*, which is
  inherent in string names.  The duplicate-declaration check catches it within one `var` block.
  Document it.
* **`ModuleExpression` universe.**  `HoleSigs.Instantiation.{instU}` and the `Module` machinery
  are stated with an explicit universe tied to `ProgramSpec`.  Fixing it at `1` should simplify,
  but re-check the universe-inference note in `Programs.lean` (around `HoleSigs.Instantiation`).
* **Attic/CounterExamples**: `Attic/TypedModules.lean` and `CounterExamples/FV.lean` reference the
  old types.  Either leave Attic unbuilt or patch it minimally; it must not hold up the refactor.
* **Word of caution on `local` / `global` field names**: see §2.1.
* **Global names collide across libraries (Phase 7).**  If globals become string-named slots,
  two independent libraries that both declare a global `"state"` of the same type get *the same
  variable*, silently.  Today two axiomatised lenses are distinct unless disjointness is
  asserted.  Global names need namespacing, e.g. derived from the declaring constant's full
  `Name` (`GaudisCrypt.RO.random_oracle_state`), or a `Name`-valued `VariableName` (see Q9).
  This does not affect locals, which are frame-relative.
* **Variable identity is "up to defeq of the type".**  `("x", ℕ)`, `("x", Nat)`, and
  `("x", MyNat)` for `def MyNat := Nat` are all *the same* variable (the pairs are equal by
  `rfl`), even though they differ syntactically.  Conversely, two types that are propositionally
  but not definitionally equal give "different" variables whose disjointness cannot be proved.
  Consequences:
  * the one-type-per-name check (parsing and printing) must compare types with `isDefEq`, not
    `==` on `Expr`;
  * meta code that matches `varLens` occurrences (printing, the flattening passes' name
    collection, cleaning lemmas) must not assume one syntactic type per name;
  * `#roundtrip` may print `ℕ` where `Nat` was written.  That is fine, but tests should pin it.
* **`varLens` signature.**  With `varLens (v : VariableName) [Nonempty v.type]`, instance search
  has to see through `("x", Int).2`, and meta code has to match a `Prod.mk` inside an argument.
  Prefer `varLens (n : String) (T : Type) [Nonempty T]`, which builds the pair internally.  It
  gives cleaner instance search, simpler `Expr` matching, and simpler printing.
* **`simp`/`wp` cost.**  Today a local read after writes is a tuple projection (`rfl`).  Now the
  state after `k` assignments is a `Function.update` chain, and each read needs name inequalities
  against every write above it, so the work is quadratic in `k`.  Large procedures (RO games)
  may get noticeably slower to verify.  Mitigations: a simproc that evaluates `varLens` reads
  against literal update chains, and the commuting lemma `update_comm` oriented by name to put
  chains in a normal form.  Measure early, on one RO file, in Phase 3.
* **Procedures are no longer unique up to renaming.**  `proc (x) {…}` and `proc (y) {…}` with the
  body renamed are different terms (different `parameterNames`, different `varLens` strings)
  with the same denotation.  Previously params and locals were positional, so such
  alpha-variants were *the same term*.  Anything that proves procedure equalities by `rfl`
  (module reduction, `instantiate` lemmas, `ModuleExpression` normalisation tests) needs
  checking.  The renaming-invariance lemma of §4.5 becomes the general tool for this.
* **`hoareProc` option (b) (§3.4) — the postcondition must not see the callee's frame.**  The
  precondition over the entry `ProgramState` is harmless, because it is determined by `args` and
  globals.  A postcondition over the callee's *final* locals would expose internals: two
  procedures with equal `procedureDenotation` could satisfy different triples, which breaks the
  abstraction that `call'` provides by discarding the frame.  Keep the post over `(res, globals)`.
  It also means a postcondition still cannot mention entry parameters (the existing
  restriction).
* **Uninitialised reads are a fixed constant.**  Under option A, `init` is one fixed
  `Classical.choice` value, the same on every call and in every procedure.  This is sound and
  consistent with flattening (which must reset to the *same* `init`), but it is observable: a
  program can read an uninitialised local twice in different calls and get equal values.
  Proofs must never depend on that.  If true nondeterminism is wanted, the frame would have to be
  sampled, which needs a distribution on `VariableAssignment` and is not recommended.
* **Effort.**  `Lib/RO/InstantiateCommon.lean` (38 uses of the old scope API),
  `GlobEndpointExample.lean` (39), `ROCouplingEquiv.lean` (18) and `Logic/Inline.lean` (112) carry
  most of the migration.  Estimate Phase 3 and Phase 6 as the two big phases.

---

## 7. Questions

**Decided (2026-10-04):** Q1 → option B (`Nonempty` in the name, `Classical.choice` init);
Q2 → locals first, `global : State` stays under `[ProgramSpec]`; Q3 → yes, require
`parameterNames.Nodup`; Q6 → accept frame-relative capture and document it; Q7 → (a), keep
`hoareProc`'s shape; Q9 → `String`; Q10 → `Nat` keys, variant (d′); Q11 → type in the name.
Open, but only for late phases (defaults = the recommendations): Q4, Q5, Q8.

* **Q1 (blocking)** — §1.1: Option A (`Nonempty` argument, unspecified init), B, or C
  (`Inhabited` in the name, `default` init)?  Must existing default-init behaviour be preserved?
  Add `var x : T := e;` sugar?
* **Q2** — §1.4: is `global : VariableAssignment` meant now, removing `ProgramSpec` everywhere
  in the same refactor, or locals first, globals second?
* **Q3** — should `parameterNames.Nodup` be enforced as well?
* **Q4** — `GaudiProg[ … ]` standalone statements: add an optional `var` header, or print locals
  as raw `varLens` terms?
* **Q5** — a parameter name that cannot be printed as an identifier: give up on `proc` printing
  for that term, or add a `proc ("x y" : T)` form?
* **Q6** — §3.2 nested `proc` literals: accept frame-relative capture, or shadow outer names
  with an error marker?
* **Q7** — item 13, "left/right": the `var` block versus the conditions, or the two sides of a
  relational judgment?  And for `hoareProc`, option (a) (keep the shape) or (b) (pre/post over the
  callee's entry `ProgramState`)?
* **Q8** — §4.4: is a printed `reset` statement for the callee's frame acceptable as a first
  step?
* **Q9** — `VariableName` as `String` (as specified) or Lean `Name`?  `Name` avoids the
  hierarchical-name ambiguity of §3.1 but is a less canonical semantic object.  Recommendation:
  `String`, with the atomic-name restriction.
* **Q10** — §1.3: structural string instances (e), or a tactic-supplied `Lens.Disjoint` in tuple
  l-values (a), or the `Setter.pair` route (c)?
* **Q11** — §9: type-in-name (§§1–4) or untyped names with a typing-context index (§9)?  Was
  dropping the type index of `StmtWithHoles` (item 4) a goal in itself, or a means to get rid of
  the positional tuple?

---

## 8. Long-term risks

Problems that will not show up during the refactor, but later.  Marked **(§9)** where the
alternative design of §9 removes or weakens them.

* **L1 — Reusing statements gives dynamic scoping.**  Today a `Stmt L` is tied to its scope type,
  so a statement fragment defined in one place cannot be spliced into a procedure with a
  different scope without an explicit `applyLens`.  After the change every statement has the
  type `Stmt`.  A reusable fragment (`def sampleTmp : Stmt := GaudiProg[ var tmp …; ]`) spliced
  into a procedure that also uses `tmp` silently shares the variable.  This is the statement-level
  version of the nested-`proc` problem of §3.2, and it will bite as soon as there is a library of
  statement combinators.  Discipline: reusable fragments take their variables as lens
  arguments, or are procedures (calls get their own frame).  **(§9: weakened — different
  contexts give different types.)**
* **L2 — Parameter names must never become part of a procedure's interface.**  Module types
  record names in `@[gaudiProcParamNames]`, and implementations may use other names.  Any
  specification phrased through the *callee's* `parameterNames` stops transporting across
  instantiation.  Examples: `hoareProc` option (b) of §3.4, a future relational judgment on
  procedures, contracts in module types.  Principle: external specifications go through the
  argument tuple, or through names owned by the specification itself (the triple evaluates its
  own names, `setParams tripleNames args init`, not the procedure's).  Prove early that
  `procedureDenotation` is invariant under renaming (§4.5), and keep it that way.
* **L3 — Universe ceiling.**  Variable types live in `Type` (`Type 0`).
  * Universe-polymorphic library code (`{G : Type*} [Group G]`) has to be specialised to
    `Type 0` to be used in a variable.  This is already true for locals; it becomes true for
    globals in Phase 7.
  * Procedure-valued or module-valued variables (an oracle stored in the state, higher-order
    adversaries that keep oracles) are impossible: `Procedure` lives at least one universe
    above the state it acts on.  The old abstract-`State` design had the same limit for
    procedures, so this is not new, but the new design freezes it into `VariableName`.
* **L4 — Phrase adversary assumptions so that fresh globals come for free.**  Game hops often
  introduce fresh globals (a `bad` flag, ghost variables).  The adversary has to be disjoint from
  them, and today that is a per-variable assumption made up front.  With named globals,
  phrase the assumption *positively*: "the adversary touches only globals in namespace `A`".
  Then every later name outside `A` is disjoint automatically.  Decide this before writing
  many theorems against the new model; retrofitting theorem statements is expensive.
* **L5 — `letI` inlining is an elaborator implementation detail.**  Lean has changed `let`/`have`
  elaboration several times (non-dependent `have` as `letE`, simp's `zetaHave`/`letToHave`
  switches, which `Inline.lean` already had to deal with).  Pin the behaviour with a test
  ("the elaborated `proc` contains no `letE`"), and keep the `withLetDecl` + `replaceFVar`
  elaborator of §3.1 ready as a fallback.
* **L6 — Program variables inside tactic proofs.**  Invariants and intermediate assertions written
  inside `by` blocks are outside the surface syntax, so they have to spell
  `(varLens ("x", Int)).intoLocal`.  A typo (`"cnt"` for `"count"`) is still type-correct and
  denotes a different variable, so the proof just fails to go through, with no error pointing at
  the cause.  Needed: a term syntax for program variables in proofs (e.g. `lvar% x : Int`, or
  `open_vars p in …` that brings a procedure's variables into scope), and a delaborator for
  `Function.update` chains (`m[x := v]`) so that goals stay readable.  **(§9: weakened — names
  are checked against the context.)**
* **L7 — Renaming a variable is a semantic change.**  Proofs that mention a variable by its
  string break when the program renames it.  Today they break when variables are *reordered*
  instead.  Prefer proof scripts that obtain variables from the program term over ones that
  spell out string literals.
* **L8 — `DecidableEq` instance diamonds (type-in-name only).**  If `VariableName` is a `def` or
  `abbrev` of a product, `open Classical` (or any other route) can produce a second
  `DecidableEq` instance.  `Function.update` terms that differ only in that instance do not match
  syntactically, and `simp` then fails far from the cause.  Make `VariableName` a `structure`
  with exactly one instance.  **(§9: gone — `String` has a computable instance.)**
* **L9 — No executable fragment.**  Classical `DecidableEq` makes even deterministic state
  updates non-computable.  `SubProbability` already rules out running programs, but this also
  closes the door to a computable sub-semantics (testing by evaluation, extraction).
  **(§9: gone.)**
* **L10 — The name type limits future language features.**  Block-scoped locals, shadowing
  inside a procedure, loop-local variables and arrays as families of variables (`x[i]`) all
  need either parse-time renaming (with printing reconstructing the scopes) or a structured
  name type.  If any of these are plausible, decide on the name type now (`String`, `Name`, or
  an inductive), because changing it later is another migration of this size.
* **L11 — Quantum (OPEN, not checked).**  If quantum programs are a long-term goal: a memory
  that is a dependent function from names to values is a classical model.  Its quantum analogue
  would presumably be ℓ² over the set of assignments, which has infinitely many slots and an
  uncountable index set under type-in-name.  I have not checked whether the `LensRange`/commutant
  machinery, the frame/initialisation semantics or the "all names exist" memory carry over to
  that setting.  Worth checking before freezing the memory model.  (Under §9 a frame has only
  finitely many declared slots that carry information, which looks closer to the usual
  finite-register setting, but this is unverified as well.)
* **L12 — Verification performance** grows with program size (see "`simp`/`wp` cost" in §6).
  This is a long-term risk because RO games get bigger.

---

## 9. Alternative: untyped names, typed frames

### 9.1 Why the type keeps appearing

A lawful `Lens T S` for a name `n` needs slot `n` to hold a `T` in *every* state of `S`.  So if
names do not carry their type, the *state type* has to fix the type of each slot: the state
depends on a typing context.  That leaves exactly three designs:

1. **Type in the name** (§§1–4): every `(name, type)` pair is its own slot.  No index, but this
   is where the undecidable equality, the universe bump, the empty-type problem and the
   parse/print ambiguity come from.
2. **Typing context as a type index**: `Γ` maps names to types, and frames have type
   `VariableAssignment Γ`.
3. **One fixed, global context**: a closed universe of type codes, `VariableName := String × Code`
   with `decode : Code → Type`.  Equality is decidable and there is no index.  But the set of
   variable types is closed, or extensible only through a global registry class, which is
   `ProgramSpec` again.  Not recommended.

Dynamic typing (`String → Σ T, T`, with `varLens n T` casting on read) does **not** escape this
dichotomy: `set_get` fails on any state where slot `n` holds a value of another type, so the
result is not a lawful lens.  The range framework depends on the lens laws.

### 9.2 Design 2 in detail

```lean
/-- A typing context: declared names with their types; first entry wins; undeclared ↦ PUnit. -/
abbrev Ctx := List (String × Σ T : Type, Inhabited T)
@[reducible] def Ctx.type (Γ : Ctx) (n : String) : Type        -- lookup
def VariableAssignment (Γ : Ctx) := (n : String) → Γ.type n      -- : Type, no universe bump
def VariableAssignment.init (Γ) : VariableAssignment Γ          -- `default` per slot
def varLens (Γ : Ctx) (n : String) : Lens (Γ.type n) (VariableAssignment Γ)   -- Function.update, computable DecidableEq String

structure ProgramState (Γ : Ctx) where
  globals : State                    -- or a global context, see Phase 7
  locals  : VariableAssignment Γ

inductive StmtWithHoles : HoleSigs → Ctx → Type 1     -- index comes back, name-keyed

structure ProcedureWithHoles (holes) (sig) where
  ctx            : Ctx                               -- parameters and `var`s, as declared
  parameterNames : List String
  parameterTypes : parameterNames.map ctx.type = sig.params := by rfl
  body           : StmtWithHoles holes ctx
  return_val     : Getter sig.ret (ProgramState ctx)
```

Parsing `proc (x : Int) { var y : Bool; … }` gives `ctx := [("x", ⟨Int, _⟩), ("y", ⟨Bool, _⟩)]`
and `letI x : Lens Int (ProgramState ctx) := (varLens ctx "x").intoLocal`.  The type ascription
is checked at default transparency, where `ctx.type "x"` reduces to `Int`.  After that every use
of `x` sees `Int` syntactically.

**What this solves, compared with §§1–4:**

* equality of names is `String` equality: decidable, computable, no `Classical.decEq` (§1.3, L8,
  L9);
* no `(x, Int)` vs `(x, Nat)` problem: one name has one type *by construction* (first entry
  wins), so item 11 holds structurally, and printing reads the `var` list straight off `ctx`
  instead of inferring it.  The only degradation left is a name that is not an identifier;
* no universe bump: `VariableAssignment Γ : Type`, so Phase 0 is not needed (§1.2);
* no empty-type problem, and **default-initialisation semantics are kept** via the `Inhabited`
  entries (§1.1);
* `varLens` needs no casts: `Function.update` over `String` is dependent but cast-free;
* static scoping mostly comes back: a nested `proc` or a reused fragment with a *different*
  context is a type error (§3.2, L1).  Same-context capture remains possible;
* flattening gets its finite frames back.  An undeclared slot has type `PUnit` and carries no
  information, so a statement's effective footprint lies within its declared names *without
  any footprint proof*.  Consequences:
  * freshness of the callee's renamed names becomes a **decidable check against the caller's
    `ctx`**, so the escape injections of §4.3 are not needed;
  * names such as `w0` can be chosen directly, so the cosmetic renaming pass of §4.5 is not
    needed either;
  * the callee reset is per variable again, `w <- default;`, which prints (§4.4 goes away).

**What it costs:**

* item 4 is only half achieved: the positional `l`/`ProcedureScope` index goes, but a
  name-keyed `Ctx` index comes back.  Flattening still changes the statement's type
  (`Γ ↦ Γ'`), as it does today with `newLocals`;
* `Γ.type "x"` has to reduce.  Elaboration is fine, through the ascription above.  Terms coming
  out of *generic* lemmas (`wp` of a `varLens` write, say) mention `Γ.type n` and need `simp`
  lemmas or a simproc for `Ctx.type` at literal contexts.  Instance search at reducible
  transparency will not evaluate `String.decEq`: the same kind of trouble `typeListToTuple`
  already has, in a new place;
* generic definitions need casts along propositional equalities: `setParams` (one cast, via
  `parameterTypes`), and the flattening lenses (`Γ'.type (ρ n) = Γ.type n` for the renamed
  names).  At concrete contexts they reduce by `rfl`, as the current tuple lenses do;
* `Lens.Disjoint` of two `varLens` still needs `"x" ≠ "y"`, provided the same way as in §1.3
  (structural string instances, option (e), or a tactic);
* duplicate entries in a `Ctx` are dead (shadowed) variables.  Parsing rejects them; printing
  has to cope with them in terms built by hand.

### 9.3 Assessment

Design 2 removes most of the problems in §1 (universe bump, emptiness, undecidable equality,
parse/print ambiguity) and in §4 (escape injections, unprintable reset), plus L8 and L9.  It
weakens L1 and L6.  In exchange it brings back a type index, and with it type-level reduction of
`Ctx.type`.  That index is much tamer than the positional `ProcedureScope` tuple: it is keyed by
name, order-irrelevant for lookups, and extended by consing.

**Recommendation: design 2**, unless dropping the index was a goal in itself (Q11).  The plan in
§5 adapts directly: Phase 0 disappears, Phase 1 builds `Ctx`/`varLens Γ`, and the flattening
phase becomes much closer to today's `Inline.lean` (finite frames, prepended context entries),
with name-keyed lookups replacing the tuple surgery.

The global part (Phase 7) can use the same idea: a global `Ctx` that is *one* fixed context per
development.  That context is a section variable or class (`ProgramSpec` in a new form, with
namespaced names; see the collision item in §6).
