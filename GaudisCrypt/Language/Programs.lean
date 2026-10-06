import Lean
import Lean.Elab.Term
import Mathlib.Data.Fintype.Basic
import GaudisCrypt.Language.Semantics
import GaudisCrypt.Language.Footprint
import GaudisCrypt.Language.Variables

namespace GaudisCrypt

open GaudisCrypt
open GaudisCrypt

variable [ProgramSpec]

structure ProcedureSignature where
  params : List Type
  ret : Type

def ProcedureSignature.ParamType (sig : ProcedureSignature) := typeListToTuple sig.params

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

/-- Syntactic program (with arbitrary Lean terms as expressions).  Every statement runs on a
`ProgramState`: the globals, and the locals of the running procedure (its parameters among
them). -/
inductive StmtWithHoles [ProgramSpec] : HoleSigs → Type _ where
  | skip : StmtWithHoles h
  | sample {a : Type} : Setter a ProgramState → Getter (SubProbability a) ProgramState →
      StmtWithHoles h
  | call' {sig : ProcedureSignature} :
      -- We have to spell out all parts of the procedure, unfortunately
      -- (Lean forbids the mutual induction with `Procedure`)
      Setter sig.ret ProgramState
        → (parameterNames : List String) → parameterNames.length = sig.params.length
        → parameterNames.Nodup
        → StmtWithHoles .empty                    -- callee body
        → Getter sig.ret ProgramState             -- callee return value
        → Getter sig.ParamType ProgramState       -- arguments, read in the caller's state
        → StmtWithHoles h
  | hole {sig} (n : HoleIndex h sig) : Setter sig.ret ProgramState →
      Getter sig.ParamType ProgramState → StmtWithHoles h
  | seq : StmtWithHoles h → StmtWithHoles h → StmtWithHoles h                   -- c1; c2
  | ifThenElse : Getter Bool ProgramState → StmtWithHoles h → StmtWithHoles h → StmtWithHoles h
  | while : Getter Bool ProgramState → StmtWithHoles h → StmtWithHoles h          -- while b do c

def Stmt [ProgramSpec] := StmtWithHoles .empty

/-- A procedure: its body and return value run on a `ProgramState`, and on a call the arguments
are written into the local slots named `parameterNames` (with the types `sig.params`), see
`ProcedureWithHoles.initLocals`. -/
structure ProcedureWithHoles [ProgramSpec] (holeSigs : HoleSigs) (sig : ProcedureSignature) where
  parameterNames : List String
  parameterNames_length : parameterNames.length = sig.params.length := by rfl
  parameterNames_nodup : parameterNames.Nodup := by decide
  body : StmtWithHoles holeSigs
  return_val : Getter sig.ret ProgramState

def Procedure [ProgramSpec] sig := ProcedureWithHoles .empty sig

/-- The signature of a procedure-with-holes as a *term* — `sig` is otherwise only reachable as
an implicit argument of the type, which makes it awkward to name in generated code. -/
abbrev ProcedureWithHoles.signature [ProgramSpec] {holes sig}
    (_p : ProcedureWithHoles holes sig) : ProcedureSignature := sig

/-- The locals a call of `p` with arguments `args` starts with: the arguments in the parameter
slots, everything else at `VariableAssignment.init`. -/
noncomputable def ProcedureWithHoles.initLocals {holes sig} (p : ProcedureWithHoles holes sig)
    (args : sig.ParamType) : VariableAssignment :=
  VariableAssignment.setParams p.parameterNames sig.params p.parameterNames_length args
    VariableAssignment.init

@[match_pattern]
def StmtWithHoles.call [ProgramSpec] {sig} (x : Setter sig.ret ProgramState) (proc : Procedure sig)
      (params : Getter sig.ParamType ProgramState) : StmtWithHoles h :=
  StmtWithHoles.call' x proc.parameterNames proc.parameterNames_length proc.parameterNames_nodup
    proc.body proc.return_val params

noncomputable
def StmtWithHoles.assign [ProgramSpec]
  (x : Setter a ProgramState) (e : Getter a ProgramState) : StmtWithHoles h :=
  StmtWithHoles.sample x ⟨fun st => pure (e.get st)⟩

/-- The setter that puts the region `R` of the locals back to `VariableAssignment.init`, the
value every local has when a procedure starts; the value written, `()`, is ignored.  `R` is a
whole `VariableAssignment` (or a part of one renamed, see `VariableAssignment.embed`), which lives
in `Type 1`, so it cannot itself be the value of an `assign`; `assign R.resetSetter ⟨fun _ => ()⟩`
is the reset.  Flattening (`Logic/Inline.lean`) emits it for the frame of the callee it
inlines. -/
noncomputable
def Lens.resetSetter (R : Lens VariableAssignment ProgramState) : Setter Unit ProgramState where
  set _ σ := R.set VariableAssignment.init σ
  set_set σ _ _ := R.set_set σ _ _

def Stmt.call [ProgramSpec] {sig} (x : Setter sig.ret ProgramState) (proc : Procedure sig)
      (params : Getter sig.ParamType ProgramState) : Stmt
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
nothing to infer it from. -/
def HoleSigs.Instantiation [ProgramSpec] : HoleSigs → Type 1
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
def StmtWithHoles.instantiate {holes : HoleSigs}
    (stmt : StmtWithHoles holes)
    (instantiation : holes.Instantiation) :
    Stmt := match stmt with
  | .skip            => .skip
  | .sample x e      => .sample x e
  | .call' x ns hl hn b r p => .call' x ns hl hn b r p
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
  ⟨proc.parameterNames, proc.parameterNames_length, proc.parameterNames_nodup,
    StmtWithHoles.instantiate proc.body instantiation, proc.return_val⟩


/-- A structural size measure used to justify termination of `programDenotation`.
    The auto-generated `sizeOf` for `StmtWithHoles` is trivially `0` (the inductive
    lives in a higher universe because its constructors quantify over `a : Type`), so
    we define our own. -/
def StmtWithHoles.depth {h} : StmtWithHoles h → Nat
  | .skip           => 0
  | .sample _ _     => 0
  | .hole _ _ _     => 0
  | .call' _ _ _ _ body _ _ => body.depth + 1
  | .seq p q        => max p.depth q.depth + 1
  | .ifThenElse _ p q => max p.depth q.depth + 1
  | .while _ p      => p.depth + 1

/-- A hole-free statement has nothing to instantiate: every constructor is re-typed as itself, and
the `.hole` case cannot occur (`HoleIndex .empty _` is empty).  Recursion is on `depth` — the
statement's own index `HoleSigs.empty` is not a variable, so the equation compiler cannot recurse
on it structurally. -/
theorem StmtWithHoles.instantiate_empty (inst : HoleSigs.empty.Instantiation) :
    ∀ s : Stmt, s.instantiate inst = s
  | .skip => rfl
  | .sample _ _ => rfl
  | .call' _ _ _ _ _ _ _ => rfl
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
  obtain ⟨names, hlen, hnodup, body, ret⟩ := p
  simp only [ProcedureWithHoles.instantiate, StmtWithHoles.instantiate_empty]

noncomputable
def programDenotation : Stmt → ProgramDenotation ProgramState Unit
| .skip => ProgramDenotation.skip
| .sample x e => do let μ : SubProbability _ <- ProgramDenotation.get e; let v <-
    μ.toProgramDenotation; ProgramDenotation.set x v
| .seq p q => do let _ <- programDenotation p; programDenotation q
| .ifThenElse c p q => do if ← ProgramDenotation.get c then programDenotation p else
    programDenotation q
| .while c p => while_loop (ProgramDenotation.get c) (programDenotation p)
| .call' (sig:=sig) (x : Setter sig.ret _) names hlen hnodup body ret args => do
    let proc : Procedure sig := ⟨names, hlen, hnodup, body, ret⟩
    let argValues <- ProgramDenotation.get args
    -- `procedureDenotation proc argValues`, spelled out (see there)
    let retVal <- ProgramDenotation.zoom ProgramState.globalL fun st =>
      (programDenotation body ⟨st, proc.initLocals argValues⟩).hbind fun p =>
        pure (ret.get p.2, p.2.globals)
    ProgramDenotation.set x retVal
termination_by stmt => stmt.depth
decreasing_by all_goals simp [StmtWithHoles.depth]; try omega

/-- Run `proc` on fresh locals (`ProcedureWithHoles.initLocals`); the callee's locals are
discarded at the end, only the globals are kept.  The state and the result live in different
universes, hence `hbind` in place of `do`.

Not mutual with `programDenotation`, whose `call'` case repeats this body. -/
noncomputable
def procedureDenotation {sig} (proc : Procedure sig) (args : sig.ParamType) :
   ProgramDenotation State sig.ret := fun st =>
    (programDenotation proc.body ⟨st, proc.initLocals args⟩).hbind fun p =>
      pure (proc.return_val.get p.2, p.2.globals)

/-- The `call'` case of `programDenotation`, with the callee run folded into
`procedureDenotation`. -/
-- TODO-CLAUDE Analogue theorem programDenotation_call for call instead of call'
theorem programDenotation_call' {sig : ProcedureSignature} (x : Setter sig.ret ProgramState)
    (names hlen hnodup) (body : Stmt) (ret : Getter sig.ret ProgramState)
    (args : Getter sig.ParamType ProgramState) :
    programDenotation (.call' x names hlen hnodup body ret args) = (do
      let argValues <- ProgramDenotation.get args
      let retVal <- ProgramDenotation.zoom ProgramState.globalL
        (procedureDenotation ⟨names, hlen, hnodup, body, ret⟩ argValues)
      ProgramDenotation.set x retVal) := by
  rw [programDenotation]; rfl
/-- The procedure denotation as an explicit wrapper: initialise locals, run the
    body, extract `(return_val, globals)`. -/
noncomputable def procWrap {sig : ProcedureSignature}
    (rv : Getter sig.ret ProgramState) (initL : VariableAssignment)
    (B : ProgramDenotation ProgramState Unit) : ProgramDenotation State sig.ret :=
  fun st => (B ⟨st, initL⟩).hbind fun p => pure (rv.get p.2, p.2.globals)

/-- `procedureDenotation` of an instantiated procedure is `procWrap` of its body
    (generic over the holes and their instantiation). -/
theorem procedureDenotation_eq_procWrap_gen {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType) (inst : holes.Instantiation) :
    procedureDenotation (A.instantiate inst) args
      = procWrap A.return_val (A.initLocals args)
          (programDenotation (A.body.instantiate inst)) := by
  rfl


end GaudisCrypt
