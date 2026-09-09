import Lean
import Lean.Elab.Term
import Mathlib.Data.Fintype.Basic
import GaudisCrypt.Language.Semantics
import GaudisCrypt.Language.Footprint

namespace GaudisCrypt

open GaudisCrypt
open GaudisCrypt

class ProgramSpec : Type _ where
  state : Type u

def State [spec : ProgramSpec] := spec.state


variable [ProgramSpec]

/-- The state a statement runs in: the `global` program state together with the
`local` state `l` (procedure parameters + local variables).  Replaces the former
`State × l` product so that the two halves are named. -/
structure ProcedureState (l : Type) where
  global : State
  -- Rename → scoped
  locals : l

/-- Lens onto the global part of a `ProcedureState`. -/
def ProcedureState.globalL {l : Type} : Lens State (ProcedureState l) where
  get s := s.global
  set v s := { s with global := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lens onto the local part of a `ProcedureState`. -/
def ProcedureState.scopedL {l : Type} : Lens l (ProcedureState l) where
  get s := s.locals
  set v s := { s with locals := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

def VariableName := String

structure ProcedureSignature where
  params : List Type
  ret : Type

/-- Reducible on purpose: at a concrete parameter list the tuple type has to be visible to
unification at `reducible` transparency, or everything stated about `_ × _` gets stuck on it —
typeclass resolution (`OfNat (typeListToTuple [Nat]) 5` for a numeral argument of a `call`,
`Lens.Disjoint` of two projection lenses) is where it shows. -/
@[reducible] def typeListToTuple : List Type → Type
  | []      => Unit
  | [x]     => x
  | x :: xs => x × typeListToTuple xs

/-- The declared types of a local-variable list, i.e. `ls.map (·.fst)`.

Spelled out by recursion rather than as `List.map` *because* it has to be reducible, for the
same reason `typeListToTuple` is: `List.map` is not, so `typeListToTuple (ls.map (·.fst))`
stays stuck at `reducible` transparency — `typeListToTuple` cannot match on an argument it
cannot evaluate, and the tuple type never becomes a `_ × _` that instance search can use.
With this, `Lens.Disjoint` of two local-variable lenses is synthesized on its own. -/
@[reducible] def localTypes : List (Σ t : Type, Inhabited t) → List Type
  | []             => []
  | ⟨t, _⟩ :: rest => t :: localTypes rest

omit [ProgramSpec] in
/-- `localTypes` is `List.map (·.fst)`, for interop with lemmas stated that way.  Deliberately
*not* `@[simp]`: rewriting towards `List.map` puts back exactly the non-reducible head that
`localTypes` exists to avoid. -/
theorem localTypes_eq_map (ls : List (Σ t : Type, Inhabited t)) :
    localTypes ls = ls.map (·.fst) := by
  induction ls with
  | nil => rfl
  | cons h t ih => cases h; simp [localTypes, ih]

/-- The local state of a procedure: parameter values (`params`) and local-variable
values (`localVars`).  Indexed by the parameter *types* and the local declarations only
(not the return type), so it can be formed before the return type is known — this is
what lets a `proc` with an omitted return type elaborate. -/
structure ProcedureScope (paramTypes : List Type)
    (locals : List (Σ t : Type, Inhabited t)) where
  params : typeListToTuple paramTypes
  localVars : typeListToTuple (localTypes locals)

/-- The local state for a full signature (delegates to `ProcedureScope`; reducible
so `sig.ProcedureScope locals` is defeq to `ProcedureScope sig.params locals`). -/
@[reducible] def ProcedureSignature.ProcedureScope (sig : ProcedureSignature)
    (locals : List (Σ t : Type, Inhabited t)) : Type :=
  _root_.GaudisCrypt.ProcedureScope sig.params locals

/-- Lens onto the parameter tuple of a `ProcedureScope`. -/
def ProcedureScope.paramsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens (typeListToTuple paramTypes) (ProcedureScope paramTypes locals) where
  get s := s.params
  set v s := { s with params := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lens onto the local-variable tuple of a `ProcedureScope`. -/
def ProcedureScope.localVarsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens (typeListToTuple (localTypes locals)) (ProcedureScope paramTypes locals) where
  get s := s.localVars
  set v s := { s with localVars := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- `params` and `localVars` are distinct fields of `ProcedureScope`, so writes through the two
    field lenses commute. -/
instance ProcedureScope.disjoint_localVarsL_paramsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens.Disjoint (ProcedureScope.localVarsL (paramTypes := paramTypes) (locals := locals))
      (ProcedureScope.paramsL (paramTypes := paramTypes) (locals := locals)) :=
  ⟨fun _ _ _ => rfl⟩

/-- The mirror image of `ProcedureScope.disjoint_localVarsL_paramsL`; `Lens.Disjoint.symm` is a
    theorem, not an instance, so search needs both orientations spelled out. -/
instance ProcedureScope.disjoint_paramsL_localVarsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens.Disjoint (ProcedureScope.paramsL (paramTypes := paramTypes) (locals := locals))
      (ProcedureScope.localVarsL (paramTypes := paramTypes) (locals := locals)) :=
  ⟨fun _ _ _ => rfl⟩

/-- Lift a lens into the parameter tuple to a lens into the full procedure state
(`scopedL ∘ paramsL`).  Analogous to `Lens.ofst`.  (Defined in the `Lens` namespace via
`_root_` so dot notation `lens.intoParams` resolves.) -/
def Lens.intoParams {a : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} (lens : Lens a (typeListToTuple paramTypes)) :
    Lens a (ProcedureState (ProcedureScope paramTypes locals)) :=
  ProcedureState.scopedL.chain (ProcedureScope.paramsL.chain lens)

/-- Procedure parameters are `Lens.intoParams` of their slot projections; distinct slots are
    disjoint, and `intoParams` (two `chain` layers) preserves that. -/
instance Programs.disjoint_intoParams {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (typeListToTuple paramTypes)}
    {y : Lens b (typeListToTuple paramTypes)} [Lens.Disjoint x y] :
    Lens.Disjoint (Lens.intoParams (locals := locals) x) y.intoParams :=
  Lens.disjoint_chain ProcedureState.scopedL _ _

/-- Lift a lens into the local-variable tuple to a lens into the full procedure state
(`scopedL ∘ localVarsL`).  Analogous to `Lens.ofst`. -/
def Lens.intoLocalVars {a : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    (lens : Lens a (typeListToTuple (localTypes locals))) :
    Lens a (ProcedureState (ProcedureScope paramTypes locals)) :=
  ProcedureState.scopedL.chain (ProcedureScope.localVarsL.chain lens)

/-- Local program variables are `Lens.intoLocalVars` of their slot projections; distinct slots
    are disjoint, and `intoLocalVars` (two `chain` layers) preserves that. -/
instance Programs.disjoint_intoLocalVars {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (typeListToTuple (localTypes locals))}
    {y : Lens b (typeListToTuple (localTypes locals))} [Lens.Disjoint x y] :
    Lens.Disjoint (Lens.intoLocalVars (paramTypes := paramTypes) x) y.intoLocalVars :=
  Lens.disjoint_chain ProcedureState.scopedL _ _

/-- A local variable is disjoint from *any* parameter: `params` and `localVars` are distinct fields
    of the scope record, so writes through projections of the two commute outright — no
    `Lens.Disjoint x y` hypothesis, and no lemma about the `chain` prefix they share. -/
instance Programs.disjoint_intoLocalVars_intoParams {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (typeListToTuple (localTypes locals))}
    {y : Lens b (typeListToTuple paramTypes)} :
    Lens.Disjoint (Lens.intoLocalVars (paramTypes := paramTypes) x)
      (Lens.intoParams (locals := locals) y) :=
  ⟨fun _ _ _ => rfl⟩

/-- The other orientation of `Programs.disjoint_intoLocalVars_intoParams`;
    `Lens.Disjoint.symm` is a theorem, not an instance, so search needs both spelled out. -/
instance Programs.disjoint_intoParams_intoLocalVars {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (typeListToTuple paramTypes)}
    {y : Lens b (typeListToTuple (localTypes locals))} :
    Lens.Disjoint (Lens.intoParams (locals := locals) x)
      (Lens.intoLocalVars (paramTypes := paramTypes) y) :=
  ⟨fun _ _ _ => rfl⟩

def ProcedureSignature.ParamType (sig : ProcedureSignature) := typeListToTuple sig.params

private def localDefaults : (ls : List (Σ t : Type, Inhabited t)) →
    typeListToTuple (localTypes ls)
  | [] => ()
  | [⟨_, inst⟩] => inst.default
  | ⟨_, inst⟩ :: h :: t => (inst.default, localDefaults (h :: t))

def ProcedureSignature.localVariableInit
    (sig : ProcedureSignature) (locals : List (Σ t : Type, Inhabited t))
    (params : typeListToTuple sig.params) : sig.ProcedureScope locals :=
  ⟨params, localDefaults locals⟩

/-- A sequence of procedure signatures, describing the holes of a program.

A **cons** list, head first: `.cons X (.cons Y .empty)` is the context of a body that calls `X`
and then `Y`.  Everything indexed by it agrees on that order — `HoleIndex.zero` is the head,
`HoleSigs.Instantiation` is the tuple with the head's procedure first, `toList`,
`toModuleTypeRepTuple` and `toModuleExpr` all put the head first, and the `uses (…)` display lists
it first.  So "hole 0" means one thing throughout: the first hole the body declares. -/
inductive HoleSigs where
  | empty : HoleSigs
  | cons  : ProcedureSignature → HoleSigs → HoleSigs

def HoleSigs.length : HoleSigs → Nat
  | .empty     => 0
  | .cons _ h => h.length.succ

def HoleSigs.NonEmpty : HoleSigs → Prop
| .empty => False
| _ => True

def HoleSigs.toList : HoleSigs → List ProcedureSignature
  | .empty      => []
  | .cons sig h => sig :: HoleSigs.toList h

inductive HoleIndex : HoleSigs → ProcedureSignature → Type _ where
  | zero {a} {Γ : HoleSigs} : HoleIndex (.cons a Γ) a
  | succ {a b} : HoleIndex Γ a → HoleIndex (.cons b Γ) a
  deriving DecidableEq

def HoleIndex.toFin {holes sig} : HoleIndex holes sig → Fin holes.length
  | .zero =>
      ⟨0, by simp [HoleSigs.length]⟩
  | .succ i =>
      let j : Fin _ := HoleIndex.toFin (holes := _) (sig := _) i
      ⟨j.val.succ, Nat.succ_lt_succ j.isLt⟩

theorem HoleIndex.toFin_inj {holes sig} :
    ∀ (i1 i2 : HoleIndex holes sig), i1.toFin = i2.toFin → i1 = i2
  | .zero,    .zero,    _ => rfl
  | .zero,    .succ i2, h => by
      have : (0 : Nat) = Nat.succ (i2.toFin.val) := by
        simpa [HoleIndex.toFin] using congrArg Fin.val h
      exact (Nat.succ_ne_zero _ this.symm).elim
  | .succ i1, .zero,    h => by
      have : Nat.succ (i1.toFin.val) = 0 := by
        simpa [HoleIndex.toFin] using congrArg Fin.val h
      exact (Nat.succ_ne_zero _ this).elim
  | .succ i1, .succ i2, h => by
      have hv : Nat.succ (i1.toFin.val) = Nat.succ (i2.toFin.val) := by
        simpa [HoleIndex.toFin] using congrArg Fin.val h
      have hv' : i1.toFin.val = i2.toFin.val := Nat.succ.inj hv
      have ht : i1.toFin = i2.toFin := Fin.ext hv'
      exact congrArg HoleIndex.succ (HoleIndex.toFin_inj i1 i2 ht)

noncomputable instance {holes sig} : Fintype (HoleIndex holes sig) := by
  refine Fintype.ofInjective (HoleIndex.toFin (holes := holes) (sig := sig))
    (by
      intro i1 i2 h
      exact HoleIndex.toFin_inj (holes := holes) (sig := sig) i1 i2 h)

abbrev Var [ProgramSpec] a := Lens a State
abbrev Expr [ProgramSpec] a := Getter a State

/-- Syntactic program (with arbitrary Lean terms as expressions) -/
inductive StmtWithHoles [ProgramSpec]: HoleSigs → Type → Type _ where
  | skip : StmtWithHoles h l
  -- | assign {a : Type} : Lens a (ProcedureState l) → Getter a (ProcedureState l) → StmtWithHoles h l
  | sample {a : Type} : Setter a (ProcedureState l) → Getter (SubProbability a) (ProcedureState l) → StmtWithHoles h l
  | call' {sig : ProcedureSignature} :
      -- We have to spell out all parts of the procedure, unfortunately
      -- (Lean forbids the mutual induction with `Procedure`)
      Setter sig.ret (ProcedureState l) → (locals : List (Σ t : Type, Inhabited t))
        → StmtWithHoles .empty (sig.ProcedureScope locals)
        → Getter sig.ret (ProcedureState (sig.ProcedureScope locals))
        → Getter sig.ParamType (ProcedureState l) → StmtWithHoles h l
  | hole {sig} (n: HoleIndex h sig) : Setter sig.ret (ProcedureState l) → Getter sig.ParamType (ProcedureState l) → StmtWithHoles h l
  | seq : StmtWithHoles h l → StmtWithHoles h l → StmtWithHoles h l                   -- c1; c2
  | ifThenElse : Getter Bool (ProcedureState l) → StmtWithHoles h l → StmtWithHoles h l → StmtWithHoles h l
  | while : Getter Bool (ProcedureState l) → StmtWithHoles h l → StmtWithHoles h l          -- while b do c

def Stmt [ProgramSpec] := StmtWithHoles .empty

structure ProcedureWithHoles [ProgramSpec] (holeSigs : HoleSigs) (sig : ProcedureSignature) where
  locals : List (Σ t : Type, Inhabited t)
  body : StmtWithHoles holeSigs (sig.ProcedureScope locals)
  return_val : Getter sig.ret (ProcedureState (sig.ProcedureScope locals))

def Procedure [ProgramSpec] sig := ProcedureWithHoles .empty sig

/-- The signature of a procedure-with-holes as a *term* — `sig` is otherwise only reachable as
an implicit argument of the type, which makes it awkward to name in generated code. -/
abbrev ProcedureWithHoles.signature [ProgramSpec] {holes sig}
    (_p : ProcedureWithHoles holes sig) : ProcedureSignature := sig

@[match_pattern]
def StmtWithHoles.call [ProgramSpec] {sig} (x : Setter sig.ret (ProcedureState l)) (proc : Procedure sig)
      (params : Getter sig.ParamType (ProcedureState l)) : StmtWithHoles h l :=
  StmtWithHoles.call' x proc.locals proc.body proc.return_val params

noncomputable
def StmtWithHoles.assign [ProgramSpec]
  (x : Setter a (ProcedureState l)) (e : Getter a (ProcedureState l)) : StmtWithHoles h l :=
  StmtWithHoles.sample x ⟨fun st => pure (e.get st)⟩

def Stmt.call [ProgramSpec] {sig} (x : Setter sig.ret (ProcedureState l)) (proc : Procedure sig)
      (params : Getter sig.ParamType (ProcedureState l)) : Stmt l
     := StmtWithHoles.call x proc params

/-- The procedures filling the holes `holes`, as a **tuple**: right-nested, with `HoleIndex.zero`
— the *last*-appended hole — as the first component, the same order as
`HoleSigs.Instantiation.toList` and `HoleSigs.Instantiation.toModuleExpr`.  No holes at all is
`PUnit`, so what one writes is

```
p.instantiate (c₁, c₂, c₃)   -- three holes, in the order the body declares them
p.instantiate c              -- one hole: the tuple is its element
```

and nothing else is needed to build one: `Prod.mk` is the only constructor involved.  Reading a
hole out is `HoleSigs.Instantiation.lookup`.

A one-hole instantiation is the procedure itself rather than a pair with `PUnit`, which is what
keeps the written form free of a trailing `⟨⟩`.  The cost is that knowing `Instantiation (cons sig
holes)` is a pair takes *two* constructors, not one — so every function that recurses on `holes`
and takes an instantiation apart splits on both levels, `cons _ .empty` beside `cons _ (.cons ..)`.
Do that split in the function itself; routing it through `head`/`tail` helpers instead makes them
stuck at a variable `holes`, and then nothing about them is `rfl` any more.

It is a tuple rather than the function `∀ {sig}, HoleIndex holes sig → Procedure sig` it used to
be so that instantiations can be *written* and *read* as ordinary Lean tuples — the function form
made every instantiation an implicit-lambda chain, in the source and in every goal that mentioned
one.  The price is that `holes` has to be concrete for the type to reduce: an instantiation at a
symbolic `holes` can still be taken as a hypothesis and looked up (`lookup` recurses on the index,
which refines `holes`), but not built or taken apart without recursing on `holes` in step.

The universe is written out only because `PUnit` would otherwise take one of its own: nothing in the
`.empty` branch constrains its level, so `Type _` gives the definition a universe parameter that no
argument determines, and a use site inside an inductive (`ModuleExpression.ReductionStep`) then has
nothing to infer it from.  Spelled this way the signature is the one the function representation
had, `[ProgramSpec] → HoleSigs → Type (max 1 u)` — no generality is lost. -/
def HoleSigs.Instantiation.{instU} [ProgramSpec.{instU}] : HoleSigs → Type (max 1 instU)
  | .empty           => PUnit
  | .cons sig .empty => Procedure sig
  | .cons sig holes  => Procedure sig × HoleSigs.Instantiation holes

/-- The procedure filling hole `idx`.  Recursion is on the index, which refines `holes` as it goes
— which is what lets this work at a `holes` that is still a variable. -/
def HoleSigs.Instantiation.lookup : {holes : HoleSigs} → {sig : ProcedureSignature} →
    holes.Instantiation → HoleIndex holes sig → Procedure sig
  | .cons _ .empty,     _, inst, .zero   => inst
  | .cons _ .empty,     _, _,    .succ j => nomatch j
  | .cons _ (.cons ..), _, inst, .zero   => inst.1
  | .cons _ (.cons ..), _, inst, .succ j => HoleSigs.Instantiation.lookup inst.2 j

/-- The only hole of a one-hole instantiation is the instantiation itself. -/
@[simp] theorem HoleSigs.Instantiation.lookup_zero_single {sig : ProcedureSignature}
    (inst : (HoleSigs.cons sig .empty).Instantiation) :
    inst.lookup HoleIndex.zero = inst := rfl

/-- The first hole of a tuple of two or more: its first component. -/
@[simp] theorem HoleSigs.Instantiation.lookup_zero_cons {holes : HoleSigs}
    {sig sig' : ProcedureSignature}
    (inst : (HoleSigs.cons sig (.cons sig' holes)).Instantiation) :
    inst.lookup HoleIndex.zero = inst.1 := rfl

/-- Any later hole: the rest of the tuple. -/
@[simp] theorem HoleSigs.Instantiation.lookup_succ {holes : HoleSigs}
    {sig sig' sig'' : ProcedureSignature}
    (inst : (HoleSigs.cons sig (.cons sig' holes)).Instantiation)
    (i : HoleIndex (HoleSigs.cons sig' holes) sig'') :
    inst.lookup (HoleIndex.succ i) = inst.2.lookup i := rfl

/-- Convert an instantiation into a plain list of procedures (tagged by their signature),
in the same right-nested order as the tuple itself and as `HoleSigs.Instantiation.toModuleExpr`.

The head of the list corresponds to the most-recently appended hole signature. -/
def HoleSigs.Instantiation.toList :
    {holes : HoleSigs} → holes.Instantiation → List (Σ sig, Procedure sig)
  | .empty,               _    => []
  | .cons sig .empty,     inst => [⟨sig, inst⟩]
  | .cons sig (.cons ..), inst => ⟨sig, inst.1⟩ :: HoleSigs.Instantiation.toList inst.2

/-- Instantiate all holes in a statement using `resolve`, turning each `.hole` into a
    `.call'` of the resolved procedure.  Hole-free constructors are simply re-typed. -/
def StmtWithHoles.instantiate {holes : HoleSigs} {l : Type}
    (stmt : StmtWithHoles holes l)
    (instantiation : holes.Instantiation) :
    Stmt l := match stmt with
  | .skip            => .skip
  -- | .assign x e      => .assign x e
  | .sample x e      => .sample x e
  | .call' x ls b r p => .call' x ls b r p
  | .hole n x p      => StmtWithHoles.call x (instantiation.lookup n) p
  | .seq s1 s2       =>
      .seq (s1.instantiate instantiation) (s2.instantiate instantiation)
  | .ifThenElse c t e =>
      .ifThenElse c (StmtWithHoles.instantiate t instantiation)
                    (StmtWithHoles.instantiate e instantiation)
  | .while c t       => .while c (StmtWithHoles.instantiate t instantiation)

def ProcedureWithHoles.instantiate {holes : HoleSigs} {sig}
    (proc : ProcedureWithHoles holes sig)
    (instantiation : holes.Instantiation)
     : Procedure sig :=
  ⟨proc.locals, StmtWithHoles.instantiate proc.body instantiation, proc.return_val⟩


/-- A structural size measure used to justify termination of `programDenotation`.
    The auto-generated `sizeOf` for `StmtWithHoles` is trivially `0` (the inductive
    lives in a higher universe because its constructors quantify over `a : Type`), so
    we define our own. -/
def StmtWithHoles.depth {h l} : StmtWithHoles h l → Nat
  | .skip           => 0
  | .sample _ _     => 0
  | .hole _ _ _     => 0
  | .call' _ _ body _ _ => body.depth + 1
  | .seq p q        => max p.depth q.depth + 1
  | .ifThenElse _ p q => max p.depth q.depth + 1
  | .while _ p      => p.depth + 1

/-- A hole-free statement has nothing to instantiate: every constructor is re-typed as itself, and
the `.hole` case cannot occur (`HoleIndex .empty _` is empty).  Recursion is on `depth` — the
statement's own index `HoleSigs.empty` is not a variable, so the equation compiler cannot recurse
on it structurally. -/
theorem StmtWithHoles.instantiate_empty {l : Type} (inst : HoleSigs.empty.Instantiation) :
    ∀ s : Stmt l, s.instantiate inst = s
  | .skip => rfl
  | .sample _ _ => rfl
  | .call' _ _ _ _ _ => rfl
  | .seq s1 s2 => by
      simp only [StmtWithHoles.instantiate, instantiate_empty inst s1, instantiate_empty inst s2]
  | .ifThenElse _ s1 s2 => by
      simp only [StmtWithHoles.instantiate, instantiate_empty inst s1, instantiate_empty inst s2]
  | .while _ s => by simp only [StmtWithHoles.instantiate, instantiate_empty inst s]
termination_by s => s.depth
decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-- Instantiating a procedure that has no holes leaves it alone. -/
@[simp] theorem ProcedureWithHoles.instantiate_empty {sig} (p : ProcedureWithHoles .empty sig)
    (inst : HoleSigs.empty.Instantiation) : p.instantiate inst = p := by
  obtain ⟨locals, body, ret⟩ := p
  simp only [ProcedureWithHoles.instantiate, StmtWithHoles.instantiate_empty]

mutual
noncomputable
def programDenotation : Stmt l → ProgramDenotation (ProcedureState l) Unit
| .skip => ProgramDenotation.skip
-- | .assign x e => do let v <- ProgramDenotation.get e; ProgramDenotation.set x v
| .sample x e => do let μ : SubProbability _ <- ProgramDenotation.get e; let v <-
    μ.toProgramDenotation; ProgramDenotation.set x v
| .seq p q => do let _ <- programDenotation p; programDenotation q
| .ifThenElse c p q => do if ← ProgramDenotation.get c then programDenotation p else
    programDenotation q
| .while c p => while_loop (ProgramDenotation.get c) (programDenotation p)
| .call' (sig:=sig) (x : Setter sig.ret _) locals body ret args => do
    let proc : Procedure sig := ⟨locals, body, ret⟩
    let argValues <- ProgramDenotation.get args
    let retVal <- ProgramDenotation.zoom ProcedureState.globalL (procedureDenotation proc argValues)
    ProgramDenotation.set x retVal
termination_by stmt => (stmt.depth, 0)
decreasing_by all_goals simp [StmtWithHoles.depth, Prod.lex_def]

noncomputable
def procedureDenotation {sig} (proc : Procedure sig) (args : sig.ParamType) :
   ProgramDenotation State sig.ret := fun st => do
    let procLocalSt := sig.localVariableInit proc.locals args
    let (_, procFinalSt) <-
      programDenotation (l := sig.ProcedureScope proc.locals) proc.body ⟨st, procLocalSt⟩
    let retVal := proc.return_val.get procFinalSt
    return (retVal, procFinalSt.global)
termination_by (proc.body.depth, 1)
decreasing_by simp [Prod.lex_def]

end
/-- The procedure denotation as an explicit wrapper: initialise locals, run the
    body, extract `(return_val, global)`. -/
noncomputable def procWrap {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (initL : L)
    (B : ProgramDenotation (ProcedureState L) Unit) : ProgramDenotation State sig.ret :=
  fun st => B ⟨st, initL⟩ >>= fun p => pure (rv.get p.2, p.2.global)

/-- `procedureDenotation` of an instantiated procedure is `procWrap` of its body
    (generic over the holes and their instantiation). -/
theorem procedureDenotation_eq_procWrap_gen {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType) (inst : holes.Instantiation) :
    procedureDenotation (A.instantiate inst) args
      = procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate inst)) := by
  funext st; simp only [procedureDenotation, ProcedureWithHoles.instantiate, procWrap]


end GaudisCrypt
