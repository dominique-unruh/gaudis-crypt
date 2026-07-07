import Lean
import Lean.Elab.Term
import Mathlib.Data.Fintype.Basic
import GaudisCrypt.Language.Semantics
import GaudisCrypt.Footprint

namespace GaudisCrypt.Language.Programs

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt

class ProgramSpec : Type _ where
  state : Type u

def State [spec : ProgramSpec] := spec.state

class GranularProgramSpec extends ProgramSpec where
  granularity : Set (Footprint state)
  from_lenses : ∀ f ∈ granularity, f.FromLens
  disjoint : ∀ f ∈ granularity, ∀ g ∈ granularity, f ≠ g → f ≤ gᶜ

def IsGranularFootprint [spec : GranularProgramSpec] (f : Footprint spec.state) :=
  ∃ (F : Finset _), (∀ f ∈ F, f ∈ spec.granularity) ∧ f = sSup F

def IsSubGranularFootprint [spec : GranularProgramSpec] (f : Footprint spec.state) :=
  ∃ (F : Finset _), (∀ f ∈ F, f ∈ spec.granularity) ∧ f ≤ sSup F

structure GranularFootprint [spec : GranularProgramSpec] where
  footprint : Footprint State
  granular : IsGranularFootprint footprint

/-- **Atomicity of the granularity**: a granularity element below the join of a finite
    granularity family is one of the members or trivial.  If `p ∉ F` it is disjoint from every
    member, hence below `(sSup ↑F)ᶜ ≤ pᶜ` — and a lens footprint inside its own commutant is `⊥`
    (`Lens.footprint_eq_bot_of_le_compl`). -/
theorem GranularProgramSpec.mem_or_eq_bot_of_le_sSup [spec : GranularProgramSpec]
    {p : Footprint State} (hp : p ∈ spec.granularity)
    {F : Finset (Footprint State)} (hF : ∀ q ∈ F, q ∈ spec.granularity)
    (hle : p ≤ sSup ↑F) : p ∈ F ∨ p = ⊥ := by
  by_cases hmem : p ∈ F
  · exact Or.inl hmem
  · refine Or.inr ?_
    have hsup : (sSup ↑F : Footprint State) ≤ pᶜ := by
      refine sSup_le fun q hq => ?_
      have hqF : q ∈ F := hq
      have hne : p ≠ q := fun h => hmem (h ▸ hqF)
      calc q = qᶜᶜ := (Footprint.compl_compl q).symm
        _ ≤ pᶜ := Footprint.compl_le_compl (spec.disjoint p hp q (hF q hqF) hne)
    obtain ⟨l, hl⟩ := spec.from_lenses p hp
    rw [hl]
    exact l.footprint_eq_bot_of_le_compl (hl ▸ hle.trans hsup)

instance [spec : GranularProgramSpec] : PartialOrder GranularFootprint where
  le f g := f.footprint ≤ g.footprint
  le_refl _ := le_refl _
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  le_antisymm f g h₁ h₂ := by
    obtain ⟨ff, hf⟩ := f; obtain ⟨gf, hg⟩ := g
    obtain rfl : ff = gf := le_antisymm h₁ h₂
    rfl

instance [spec : GranularProgramSpec] : OrderBot GranularFootprint where
  bot := ⟨⊥, ∅, by simp, by simp; rfl⟩
  bot_le f := show (⊥ : Footprint State) ≤ f.footprint from bot_le

-- Actually even a lower-complete lattice, but I don't recall the typeclass name for that
open Classical in
noncomputable instance [spec : GranularProgramSpec] : Lattice GranularFootprint := by
  refine { (inferInstance : PartialOrder GranularFootprint) with
    sup := fun f g => ⟨f.footprint ⊔ g.footprint, ?_⟩
    le_sup_left := fun f g => show f.footprint ≤ f.footprint ⊔ g.footprint from le_sup_left
    le_sup_right := fun f g => show g.footprint ≤ f.footprint ⊔ g.footprint from le_sup_right
    sup_le := fun f g c h₁ h₂ =>
      show f.footprint ⊔ g.footprint ≤ c.footprint from sup_le h₁ h₂
    inf := fun f g =>
      ⟨sSup ↑(f.granular.choose.filter (fun p => p ≤ g.footprint)),
        f.granular.choose.filter (fun p => p ≤ g.footprint),
        fun p hp => f.granular.choose_spec.1 p (Finset.mem_of_mem_filter p hp), rfl⟩
    inf_le_left := fun f g => ?_
    inf_le_right := fun f g => ?_
    le_inf := fun a f g h₁ h₂ => ?_ }
  · -- the union of the two witnesses covers the join
    obtain ⟨F, hF, hf⟩ := f.granular
    obtain ⟨G, hG, hg⟩ := g.granular
    exact ⟨F ∪ G, fun p hp => (Finset.mem_union.mp hp).elim (hF p) (hG p),
      by rw [hf, hg, Finset.coe_union, sSup_union]; rfl⟩
  · -- inf ≤ f : the filtered witness is a sub-family of f's witness
    change sSup _ ≤ f.footprint
    refine le_trans (sSup_le_sSup (Finset.coe_subset.mpr (Finset.filter_subset _ _))) ?_
    exact le_of_eq f.granular.choose_spec.2.symm
  · -- inf ≤ g : every filtered atom is below g by the filter condition
    change sSup _ ≤ g.footprint
    refine sSup_le fun q hq => ?_
    exact (Finset.mem_filter.mp hq).2
  · -- le_inf : atomicity — every atom of a is ⊥ or an atom of f below g
    change a.footprint ≤ sSup _
    obtain ⟨A, hA, ha⟩ := a.granular
    rw [ha]
    refine sSup_le fun p hp => ?_
    have hpA : p ∈ A := hp
    have hpa : p ≤ a.footprint := ha ▸ le_sSup hp
    have hpF : p ∈ f.granular.choose ∨ p = ⊥ :=
      GranularProgramSpec.mem_or_eq_bot_of_le_sSup (hA p hpA) f.granular.choose_spec.1
        ((hpa.trans h₁).trans_eq f.granular.choose_spec.2)
    rcases hpF with hpF | rfl
    · exact le_sSup (Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨hpF, hpa.trans h₂⟩))
    · exact bot_le

open Classical in
/-- A **minimal granular cover** of a sub-granular footprint: a minimal sub-family of the
    witnessing granularity family that still covers `footprint`.  (This is the least granular
    footprint containing `footprint` *modulo* the open corner-projection/tensor question: every
    granular cover contains all atoms that `footprint` genuinely touches, but showing those atoms
    alone already cover `footprint` needs the product-corner structure theorem.  Minimality —
    no strict sub-family of the returned one covers — holds by construction;
    see `IsSubGranularFootprint.le_granular`.) -/
noncomputable def IsSubGranularFootprint.granular [spec : GranularProgramSpec]
    (footprint : Footprint State) (h : IsSubGranularFootprint footprint) : GranularFootprint :=
  have hne : (h.choose.powerset.filter
      fun G : Finset (Footprint State) => footprint ≤ sSup ↑G).Nonempty :=
    ⟨h.choose, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self _, h.choose_spec.2⟩⟩
  have hmin := (h.choose.powerset.filter
    fun G : Finset (Footprint State) => footprint ≤ sSup ↑G).exists_minimal hne
  ⟨sSup ↑hmin.choose, hmin.choose,
    fun p hp => h.choose_spec.1 p
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hmin.choose_spec.1).1 hp), rfl⟩

open Classical in
/-- The minimal granular cover contains what it covers. -/
theorem IsSubGranularFootprint.le_granular [spec : GranularProgramSpec]
    (footprint : Footprint State) (h : IsSubGranularFootprint footprint) :
    footprint ≤ (IsSubGranularFootprint.granular footprint h).footprint :=
  (Finset.mem_filter.mp
    ((h.choose.powerset.filter
        fun G : Finset (Footprint State) => footprint ≤ sSup ↑G).exists_minimal
      ⟨h.choose, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset_self _, h.choose_spec.2⟩⟩).choose_spec.1).2

theorem IsGranularFootprint.fromLens [spec : GranularProgramSpec] {f : Footprint State} (h : IsGranularFootprint f) :
  f.FromLens :=
  sorry

noncomputable def IsGranularFootprint.lens [spec : GranularProgramSpec] {f : Footprint State}
    (h : IsGranularFootprint f) : Lens (Quotient fᶜ.orbit_setoid) State :=
  h.fromLens.lens




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

def HoleSigs.length : HoleSigs → Nat
  | .empty => 0
  | .append h _ => h.length.succ

def HoleSigs.NonEmpty : HoleSigs → Prop
| .empty => False
| _ => True

def HoleSigs.toList : HoleSigs → List ProcedureSignature
  | .empty => []
  | .append h sig => HoleSigs.toList h ++ [sig]

inductive HoleIndex : HoleSigs → ProcedureSignature → Type _ where
  | zero {a} {Γ : HoleSigs} : HoleIndex (Γ.append a) a
  | succ {a b} : HoleIndex Γ a → HoleIndex (Γ.append b) a
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

/-- Convert an instantiation into a plain list of procedures (tagged by their signature),
in the same right-nested order as `HoleSigs.Instantiation.toModuleTuple`.

The head of the list corresponds to the most-recently appended hole signature. -/
def HoleSigs.Instantiation.toList : {holes : HoleSigs} → holes.Instantiation → List (Σ sig, Procedure sig)
  | .empty,       _    => []
  | .append _ sig, inst =>
      ⟨sig, inst .zero⟩ ::
        HoleSigs.Instantiation.toList (holes := _)
          (fun {sig'} idx => inst (.succ idx))

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
      programDenotation (l := sig.LocalVariableState proc.locals) proc.body ⟨st, procLocalSt⟩
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


end GaudisCrypt.Language.Programs
