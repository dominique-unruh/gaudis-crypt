-- CHAOS FILE

import GaudisCrypt.Language.Modules.InductiveFunctions
import GaudisCrypt.LensRange

open GaudisCrypt.Language.Modules
open GaudisCrypt.Language.Modules.InductiveFunctions
open GaudisCrypt.Language.Programs
open GaudisCrypt.Language.Lens

namespace FV

variable [ProgramSpec]

abbrev FV := LensRange State


def fv_getter (getter : Getter a s) : LensRange s := sorry

def fv_setter (setter : Setter a s) : LensRange s := sorry

def fv_reduce {a b} (lens : Lens a b) (range : LensRange b) : LensRange a := sorry

def fv_extend {a b} (lens : Lens a b) (range : LensRange a) : LensRange b := sorry

/-! ### Properties of `fv_reduce` / `fv_extend` needed for `fv_proc_instantiate`.

These are stated as axioms for review.  Once `fv_reduce`/`fv_extend` have real
definitions they should become theorems.  Note: the proof of `fv_proc_instantiate`
needs *no* properties of `fv_getter`/`fv_setter` — they are used opaquely. -/

/-- `fv_reduce` distributes over joins. -/
axiom fv_reduce_sup {a b} (lens : Lens a b) (r₁ r₂ : LensRange b) :
    fv_reduce lens (r₁ ⊔ r₂) = fv_reduce lens r₁ ⊔ fv_reduce lens r₂

/-- `fv_extend` distributes over joins. -/
axiom fv_extend_sup {a b} (lens : Lens a b) (r₁ r₂ : LensRange a) :
    fv_extend lens (r₁ ⊔ r₂) = fv_extend lens r₁ ⊔ fv_extend lens r₂

/-- `fv_reduce` is a retraction of `fv_extend`: pushing a footprint forward along a
    lens and pulling it back recovers it.  (Only `≤` is used in the proof.) -/
axiom fv_reduce_extend {a b} (lens : Lens a b) (r : LensRange a) :
    fv_reduce lens (fv_extend lens r) = r

def fv_transfer (range : LensRange (ProcedureState s)) : LensRange (ProcedureState t) :=
  fv_extend ProcedureState.globalL (fv_reduce ProcedureState.globalL range)


def fv_stmt {holes} : StmtWithHoles holes s → LensRange (ProcedureState s)
| .skip => ⊥
| .sample x e => fv_setter x ⊔ fv_getter e
| .call' x ls b r p =>
    fv_setter x ⊔ fv_transfer (fv_stmt b)⊔ fv_transfer (fv_getter r) ⊔ fv_getter p
| .hole n x p => fv_setter x ⊔ fv_getter p
| .seq s1 s2 => fv_stmt s1 ⊔ fv_stmt s2
| .ifThenElse c t e => fv_getter c ⊔ fv_stmt t ⊔ fv_stmt e
| .while c t => fv_getter c ⊔ fv_stmt t


-- Placeholder
def fv_proc {sig holes} (proc : ProcedureWithHoles holes sig) : LensRange State :=
  fv_reduce ProcedureState.globalL (fv_stmt proc.body) ⊔ fv_reduce ProcedureState.globalL (fv_getter proc.return_val)

/-- Folding `⊔` with an arbitrary base splits off the base. -/
private theorem fv_foldr_sup_base (base : LensRange State) (l : List (Σ sig, Procedure sig)) :
    List.foldr (fun p acc => fv_proc p.2 ⊔ acc) base l
      = base ⊔ List.foldr (fun p acc => fv_proc p.2 ⊔ acc) ⊥ l := by
  induction l with
  | nil => simp
  | cons p l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih, ← sup_assoc, sup_comm (fv_proc p.2) base, sup_assoc]

/-- Every instantiated hole's footprint is bounded by the fold over all of them. -/
private theorem fv_proc_le_toList :
    ∀ {holes sig} (n : HoleIndex holes sig) (args : holes.Instantiation),
      fv_proc (args n)
        ≤ args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State)
  | _, _, .zero, args => by
      simp only [HoleSigs.Instantiation.toList, List.foldr_cons]; exact le_sup_left
  | _, _, .succ n', args => by
      simp only [HoleSigs.Instantiation.toList, List.foldr_cons]
      exact le_trans (fv_proc_le_toList n' (fun idx => args idx.succ)) le_sup_right

omit [ProgramSpec] in
private theorem fv_extend_mono {a b} (lens : Lens a b) {r₁ r₂ : LensRange a} (h : r₁ ≤ r₂) :
    fv_extend lens r₁ ≤ fv_extend lens r₂ :=
  calc fv_extend lens r₁ ≤ fv_extend lens r₁ ⊔ fv_extend lens r₂ := le_sup_left
    _ = fv_extend lens (r₁ ⊔ r₂) := (fv_extend_sup lens r₁ r₂).symm
    _ = fv_extend lens r₂ := by rw [sup_eq_right.mpr h]

omit [ProgramSpec] in
private theorem fv_reduce_mono {a b} (lens : Lens a b) {r₁ r₂ : LensRange b} (h : r₁ ≤ r₂) :
    fv_reduce lens r₁ ≤ fv_reduce lens r₂ :=
  calc fv_reduce lens r₁ ≤ fv_reduce lens r₁ ⊔ fv_reduce lens r₂ := le_sup_left
    _ = fv_reduce lens (r₁ ⊔ r₂) := (fv_reduce_sup lens r₁ r₂).symm
    _ = fv_reduce lens r₂ := by rw [sup_eq_right.mpr h]

/-- Instantiating a statement only adds the (transferred) footprints of the procedures
plugged into its holes. -/
private theorem fv_stmt_instantiate_le {holes l} (stmt : StmtWithHoles holes l)
    (args : holes.Instantiation) :
    fv_stmt (stmt.instantiate args)
      ≤ fv_stmt stmt
        ⊔ fv_extend ProcedureState.globalL
            (args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State)) := by
  revert args
  induction stmt with
  | skip => intro args; simp only [StmtWithHoles.instantiate, fv_stmt]; exact bot_le
  | sample x e => intro args; simp only [StmtWithHoles.instantiate, fv_stmt]; exact le_sup_left
  | call' x ls b r p _ =>
      intro args; simp only [StmtWithHoles.instantiate, fv_stmt]; exact le_sup_left
  | hole n x p =>
      intro args
      have hmem : fv_proc (args n)
          ≤ args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State) :=
        fv_proc_le_toList n args
      have hb : fv_reduce ProcedureState.globalL (fv_stmt (args n).body)
          ≤ args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State) :=
        le_trans le_sup_left hmem
      have hr : fv_reduce ProcedureState.globalL (fv_getter (args n).return_val)
          ≤ args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State) :=
        le_trans le_sup_right hmem
      simp only [StmtWithHoles.instantiate, StmtWithHoles.call, fv_stmt, fv_transfer]
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_right (fv_extend_mono _ hb)
      · exact le_sup_of_le_right (fv_extend_mono _ hr)
      · exact le_sup_of_le_left le_sup_right
  | seq s1 s2 ih1 ih2 =>
      intro args
      simp only [StmtWithHoles.instantiate, fv_stmt]
      calc fv_stmt (s1.instantiate args) ⊔ fv_stmt (s2.instantiate args)
          ≤ (fv_stmt s1 ⊔ fv_extend ProcedureState.globalL
                (args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State)))
            ⊔ (fv_stmt s2 ⊔ fv_extend ProcedureState.globalL
                (args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State))) :=
            sup_le_sup (ih1 args) (ih2 args)
        _ = (fv_stmt s1 ⊔ fv_stmt s2) ⊔ fv_extend ProcedureState.globalL
                (args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State)) := by
            rw [sup_sup_sup_comm, sup_idem]
  | ifThenElse c t e iht ihe =>
      intro args
      simp only [StmtWithHoles.instantiate, fv_stmt]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
      · exact le_trans (iht args) (sup_le_sup_right (le_sup_of_le_left le_sup_right) _)
      · exact le_trans (ihe args) (sup_le_sup_right le_sup_right _)
  | «while» c t iht =>
      intro args
      simp only [StmtWithHoles.instantiate, fv_stmt]
      refine sup_le ?_ ?_
      · exact le_sup_of_le_left le_sup_left
      · exact le_trans (iht args) (sup_le_sup_right le_sup_right _)

theorem fv_proc_instantiate {holes sig} (proc : ProcedureWithHoles holes sig) args :
  fv_proc (proc.instantiate args) ≤
    List.foldr (fun p acc ↦ fv_proc p.snd ⊔ acc)
      (fv_proc proc) args.toList := by
  have key2 :
      fv_reduce ProcedureState.globalL (fv_stmt (proc.body.instantiate args))
        ≤ fv_reduce ProcedureState.globalL (fv_stmt proc.body)
            ⊔ args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State) := by
    refine le_trans (fv_reduce_mono _ (fv_stmt_instantiate_le proc.body args)) ?_
    rw [fv_reduce_sup, fv_reduce_extend]
  rw [fv_foldr_sup_base (fv_proc proc) args.toList]
  change fv_reduce ProcedureState.globalL (fv_stmt (proc.body.instantiate args))
        ⊔ fv_reduce ProcedureState.globalL (fv_getter proc.return_val)
      ≤ fv_proc proc ⊔ args.toList.foldr (fun p acc => fv_proc p.2 ⊔ acc) (⊥ : LensRange State)
  refine sup_le ?_ ?_
  · exact le_trans key2 (sup_le_sup_right le_sup_left _)
  · exact le_sup_of_le_left le_sup_right

def fvInductiveFunction : InductiveFunction (LensRange State) where
  nothing := ⊥
  proc (p : ProcedureWithHoles _ _) := fv_proc p
  join := (· ⊔ ·)

def fvMexpr {ctx t} (m : ModuleExpression ctx t) : (LensRange State) := fvInductiveFunction.evalMexpr m

def fv (m : Module t) : FV := fvInductiveFunction.eval m

scoped instance : Reducible fvInductiveFunction where
  comm := sup_comm
  assoc := sup_assoc
  join_idem := fun _ => sup_le le_rfl le_rfl
  join_mono_left := fun h => sup_le_sup_right h _
  join_mono_right := fun h => sup_le_sup_left h _
  le_join_left := fun _ _ => le_sup_left
  le_join_right := fun _ _ => le_sup_right
  delta_bound := fv_proc_instantiate

theorem fvMexpr_upper_bound : fv (m.toModule) ≤ fvMexpr m :=
  evalMexpr_upper_bound fvInductiveFunction m

theorem fv_app (a : Module (.arr A B)) (b : Module A) :
    fv (.app a b) ≤ fv a ⊔ fv b :=
    InductiveFunction.app _ _ _

theorem fv_pair (a : Module A) (b : Module B) :
    fv (.pair a b) = fv a ⊔ fv b :=
    InductiveFunction.pair _ _ _

theorem fv_fst (a : Module (.prod A B)) :
    fv (.fst a) ≤ fv a :=
    InductiveFunction.fst _ _

theorem fv_snd (a : Module (.prod A B)) :
    fv (.snd a) ≤ fv a :=
    InductiveFunction.snd _ _

@[simp]
theorem fv_unit (a : Module .unit) : fv a = ⊥ :=
 InductiveFunction.unit _ _

end FV
