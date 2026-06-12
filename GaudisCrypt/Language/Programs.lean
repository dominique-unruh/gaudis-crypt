import Lean
import Lean.Elab.Term
import PlonkLean.Language.Semantics

namespace Language.Programs

class ProgramSpec : Type _ where
  state : Type u

def State [spec : ProgramSpec] := spec.state

variable [ProgramSpec]

def VariableName := String

structure LocalVariables where
  params : List (VariableName × Type)
  locals : List (VariableName × Σ t : Type, Inhabited t)
  distinctNames : List.Nodup ((params.map Prod.fst) ++ (locals.map Prod.fst))

structure ProcedureSignature where
  locals : LocalVariables
  ret : Type

def paramListToTuple : List Type → Type
  | []      => Unit
  | [x]     => x
  | x :: xs => x × paramListToTuple xs

def LocalVariableState (lv : LocalVariables) : Type :=
  paramListToTuple ((lv.params.map Prod.snd) ++ (lv.locals.map (·.2.1)))

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
inductive StmtWithHoles [ProgramSpec] : HoleSigs → Type _ where
  | skip : StmtWithHoles h
  | assign {a : Type} : Var a → Expr a → StmtWithHoles h -- mutation
  | sample {a : Type} : Var a → Expr (SubProbability a) → StmtWithHoles h
  | call' {sig : ProcedureSignature} :
      -- We have to spell out all parts of the procedure, unfortunately
      -- (Lean forbids the mutual induction with `Procedure`)
      Var sig.ret → StmtWithHoles .empty → Expr sig.ret
        → Expr (paramListToTuple (sig.locals.params.map Prod.snd)) → StmtWithHoles h
  | hole {sig} (n: HoleIndex h sig) :
      Var sig.ret → Expr (paramListToTuple (sig.locals.params.map Prod.snd)) → StmtWithHoles h
  | seq : StmtWithHoles h → StmtWithHoles h → StmtWithHoles h                   -- c1; c2
  | ifThenElse : Expr Bool → StmtWithHoles h → StmtWithHoles h → StmtWithHoles h
  | while : Expr Bool → StmtWithHoles h → StmtWithHoles h          -- while b do c

def Stmt [ProgramSpec] := StmtWithHoles .empty

structure ProcedureWithHoles [ProgramSpec] (holeSigs : HoleSigs) (sig : ProcedureSignature) where
  body : StmtWithHoles holeSigs -- WARNING: procedure arguments are ignored so far
  return_val : Expr sig.ret

def Procedure [ProgramSpec] sig := ProcedureWithHoles .empty sig

@[match_pattern]
def StmtWithHoles.call [ProgramSpec] {sig} (x : Var sig.ret) (proc : Procedure sig)
      (params : Expr (paramListToTuple (sig.locals.params.map Prod.snd))) : StmtWithHoles h :=
  StmtWithHoles.call' x proc.body proc.return_val params

def Stmt.call [ProgramSpec] {sig} (x : Var sig.ret) (proc : Procedure sig)
                     (params : Expr (paramListToTuple (sig.locals.params.map Prod.snd))) : Stmt
     := StmtWithHoles.call x proc params

def HoleSigs.Instantiation (holes : HoleSigs) := ∀ {sig}, HoleIndex holes sig → Procedure sig

/-- Instantiate all holes in a statement using `resolve`, turning each `.hole` into a
    `.call'` of the resolved procedure.  Hole-free constructors are simply re-typed. -/
def StmtWithHoles.instantiate {holes : HoleSigs}
    (stmt : StmtWithHoles holes)
    (instantiation : holes.Instantiation) :
    Stmt := match stmt with
  | .skip            => .skip
  | .assign x e      => .assign x e
  | .sample x e      => .sample x e
  | .call' x b r p   => .call' x b r p
  | .hole n x p      => StmtWithHoles.call x (instantiation n) p
  | .seq s1 s2       =>
      .seq (s1.instantiate instantiation) (s2.instantiate instantiation)
  | .ifThenElse c t e =>
      .ifThenElse c (StmtWithHoles.instantiate t instantiation) (StmtWithHoles.instantiate e instantiation)
  | .while c t       => .while c (StmtWithHoles.instantiate t instantiation)

def ProcedureWithHoles.instantiate {holes : HoleSigs} {sig}
    (proc : ProcedureWithHoles holes sig)
    (instantiation : holes.Instantiation)
     : Procedure sig :=
  ⟨StmtWithHoles.instantiate proc.body instantiation, proc.return_val⟩

end Language.Programs
