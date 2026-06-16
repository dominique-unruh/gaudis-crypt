import Lean
import Lean.Elab.Term
import GaudisCrypt.Language.Semantics

namespace GaudisCrypt.Language.Programs

open GaudisCrypt.Language.Lens

class ProgramSpec : Type _ where
  state : Type u

def State [spec : ProgramSpec] := spec.state

variable [ProgramSpec]

/-- The state a statement runs in: the `global` program state together with the
`local` state `l` (procedure parameters + local variables).  Replaces the former
`State × l` product so that the two halves are named. -/
structure ProcedureState (l : Type) where
  global : State
  locals : l

/-- Lens onto the global part of a `ProcedureState`. -/
def ProcedureState.globalL {l : Type} : Lens State (ProcedureState l) where
  get s := s.global
  set v s := { s with global := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lens onto the local part of a `ProcedureState`. -/
-- TODO: rename to .localsL
def ProcedureState.localL {l : Type} : Lens l (ProcedureState l) where
  get s := s.locals
  set v s := { s with locals := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

def VariableName := String

structure ProcedureSignature where
  params : List Type
  ret : Type

-- TODO is this used?
class LocalState : Type _ where
  params : List Type
  locals : List Type

def paramListToTuple : List Type → Type
  | []      => Unit
  | [x]     => x
  | x :: xs => x × paramListToTuple xs

/-- The local state of a procedure: parameter values (`params`) and local-variable
values (`vars`).  Indexed by the parameter *types* and the local declarations only
(not the return type), so it can be formed before the return type is known — this is
what lets a `proc` with an omitted return type elaborate. -/
structure LocalVariableState (paramTypes : List Type)
    (locals : List (Σ t : Type, Inhabited t)) where
  params : paramListToTuple paramTypes
  vars : paramListToTuple (locals.map (·.fst))

/-- The local state for a full signature (delegates to `LocalVariableState`; reducible
so `sig.LocalVariableState locals` is defeq to `LocalVariableState sig.params locals`). -/
@[reducible] def ProcedureSignature.LocalVariableState (sig : ProcedureSignature)
    (locals : List (Σ t : Type, Inhabited t)) : Type :=
  _root_.GaudisCrypt.Language.Programs.LocalVariableState sig.params locals

/-- Lens onto the parameter tuple of a `LocalVariableState`. -/
def LocalVariableState.paramsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens (paramListToTuple paramTypes) (LocalVariableState paramTypes locals) where
  get s := s.params
  set v s := { s with params := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lens onto the local-variable tuple of a `LocalVariableState`. -/
def LocalVariableState.varsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens (paramListToTuple (locals.map (·.fst))) (LocalVariableState paramTypes locals) where
  get s := s.vars
  set v s := { s with vars := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lift a lens into the parameter tuple to a lens into the full procedure state
(`localL ∘ paramsL`).  Analogous to `Lens.ofst`.  (Defined in the `Lens` namespace via
`_root_` so dot notation `lens.intoParams` resolves.) -/
def _root_.GaudisCrypt.Language.Lens.Lens.intoParams {a : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} (lens : Lens a (paramListToTuple paramTypes)) :
    Lens a (ProcedureState (LocalVariableState paramTypes locals)) :=
  ProcedureState.localL.chain (LocalVariableState.paramsL.chain lens)

/-- Lift a lens into the local-variable tuple to a lens into the full procedure state
(`localL ∘ varsL`).  Analogous to `Lens.ofst`. -/
def _root_.GaudisCrypt.Language.Lens.Lens.intoVars {a : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    (lens : Lens a (paramListToTuple (locals.map (·.fst)))) :
    Lens a (ProcedureState (LocalVariableState paramTypes locals)) :=
  ProcedureState.localL.chain (LocalVariableState.varsL.chain lens)

def ProcedureSignature.ParamType (sig : ProcedureSignature) := paramListToTuple sig.params

private def localDefaults : (ls : List (Σ t : Type, Inhabited t)) → paramListToTuple (ls.map (·.fst))
  | [] => ()
  | [⟨_, inst⟩] => inst.default
  | ⟨_, inst⟩ :: h :: t => (inst.default, localDefaults (h :: t))

def ProcedureSignature.localVariableInit
    (sig : ProcedureSignature) (locals : List (Σ t : Type, Inhabited t))
    (params : paramListToTuple sig.params) : sig.LocalVariableState locals :=
  ⟨params, localDefaults locals⟩

/-- A sequences of procedure signatures, intended to be used to describe the type
    of holes in a program -/
inductive HoleSigs where
  | empty  : HoleSigs
  | append : HoleSigs → ProcedureSignature → HoleSigs

def HoleSigs.NonEmpty : HoleSigs → Prop
| .empty => False
| _ => True

def HoleSigs.toList : HoleSigs → List ProcedureSignature
  | .empty => []
  | .append h sig => HoleSigs.toList h ++ [sig]

inductive HoleIndex : HoleSigs → ProcedureSignature → Type _ where
  | zero {a} {Γ : HoleSigs} : HoleIndex (Γ.append a) a
  | succ {a b} : HoleIndex Γ a → HoleIndex (Γ.append b) a

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
        → StmtWithHoles .empty (sig.LocalVariableState locals)
        → Getter sig.ret (ProcedureState (sig.LocalVariableState locals))
        → Getter sig.ParamType (ProcedureState l) → StmtWithHoles h l
  | hole {sig} (n: HoleIndex h sig) : Setter sig.ret (ProcedureState l) → Getter sig.ParamType (ProcedureState l) → StmtWithHoles h l
  | seq : StmtWithHoles h l → StmtWithHoles h l → StmtWithHoles h l                   -- c1; c2
  | ifThenElse : Getter Bool (ProcedureState l) → StmtWithHoles h l → StmtWithHoles h l → StmtWithHoles h l
  | while : Getter Bool (ProcedureState l) → StmtWithHoles h l → StmtWithHoles h l          -- while b do c

def Stmt [ProgramSpec] := StmtWithHoles .empty

structure ProcedureWithHoles [ProgramSpec] (holeSigs : HoleSigs) (sig : ProcedureSignature) where
  locals : List (Σ t : Type, Inhabited t)
  body : StmtWithHoles holeSigs (sig.LocalVariableState locals)
  return_val : Getter sig.ret (ProcedureState (sig.LocalVariableState locals))

def Procedure [ProgramSpec] sig := ProcedureWithHoles .empty sig

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

def HoleSigs.Instantiation (holes : HoleSigs) := ∀ {sig}, HoleIndex holes sig → Procedure sig

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
  | .hole n x p      => StmtWithHoles.call x (instantiation n) p
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

mutual
noncomputable
def programDenotation : Stmt l → Program (ProcedureState l) Unit
| .skip => Program.skip
-- | .assign x e => do let v <- Program.get e; Program.set x v
| .sample x e => do let μ : SubProbability _ <- Program.get e; let v <- μ.toProgram; Program.set x v
| .seq p q => do let _ <- programDenotation p; programDenotation q
| .ifThenElse c p q => do if ← Program.get c then programDenotation p else programDenotation q
| .while c p => while_loop (Program.get c) (programDenotation p)
| .call' (sig:=sig) (x : Setter sig.ret _) locals body ret args => do
    let proc : Procedure sig := ⟨locals, body, ret⟩
    let argValues <- Program.get args
    let retVal <- Program.zoom ProcedureState.globalL (procedureDenotation proc argValues)
    Program.set x retVal
termination_by stmt => (stmt.depth, 0)
decreasing_by all_goals simp [StmtWithHoles.depth, Prod.lex_def]

noncomputable
def procedureDenotation {sig} (proc : Procedure sig) (args : sig.ParamType) :
   Program State sig.ret := fun st => do
    let procLocalSt := sig.localVariableInit proc.locals args
    let (_, procFinalSt) <-
      programDenotation (l := sig.LocalVariableState proc.locals) proc.body ⟨st, procLocalSt⟩
    let retVal := proc.return_val.get procFinalSt
    return (retVal, procFinalSt.global)
termination_by (proc.body.depth, 1)
decreasing_by simp [Prod.lex_def]

end

end GaudisCrypt.Language.Programs
