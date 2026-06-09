import Mathlib.Data.List.AList
import Mathlib.Logic.Equiv.Defs
import Metatheory.STLCext.Normalization
import Metatheory.STLCext.Confluence
import PlonkLean.Language.Programs
import PlonkLean.Language.Modules


namespace Language.Modules

open Language.Programs
open Language.Modules
open scoped Language.Modules

variable [ProgramSpec]

def _root_.Language.Programs.HoleSigs.toModuleTypeTuple : HoleSigs → ModuleType
| .empty => .unit
| .append holes sig => .prod holes.toModuleTypeTuple (.proc sig)

private lemma typeListToProd_allProc_isArrowFree
    (sigs : List ProcedureSignature) :
    (moduleTypeToSTLC (typeListToProdGeneric ModuleType.prod ModuleType.unit
      (sigs.map ModuleType.proc))).isArrowFree := by
  induction sigs with
  | nil => simp [typeListToProdGeneric, moduleTypeToSTLC, Metatheory.STLCext.Ty.isArrowFree]
  | cons sig rest ih =>
    cases rest with
    | nil => simp [typeListToProdGeneric, moduleTypeToSTLC, Metatheory.STLCext.Ty.isArrowFree]
    | cons s ss =>
      simp only [List.map, typeListToProdGeneric, moduleTypeToSTLC,
                 Metatheory.STLCext.Ty.isArrowFree, Bool.and_eq_true]
      exact ⟨by simp, ih⟩

private lemma procedureHolesToArgumentType_isArrowFree
    (holes : HoleSigs) :
    (moduleTypeToSTLC (procedureHolesToArgumentType holes)).isArrowFree := by
  simp only [procedureHolesToArgumentType]
  exact typeListToProd_allProc_isArrowFree holes.toList

private lemma toModuleTypeTuple_isArrowFree (holes : HoleSigs) :
    (moduleTypeToSTLC holes.toModuleTypeTuple).isArrowFree := by
  induction holes with
  | empty => simp [HoleSigs.toModuleTypeTuple, moduleTypeToSTLC, Metatheory.STLCext.Ty.isArrowFree]
  | append _ _ ih =>
      simp [HoleSigs.toModuleTypeTuple, moduleTypeToSTLC, Metatheory.STLCext.Ty.isArrowFree, ih]


/-- Split the last component off a right-nested tuple over `l ++ [Y]`. -/
def tupleSnocSplit {Y : Type u} : (l : List (Type u)) →
    typeListToProdGeneric Prod PUnit (l ++ [Y]) →
    typeListToProdGeneric Prod PUnit l × Y
  | [],            v          => (PUnit.unit, v)
  | [_],           p          => p
  | _ :: x' :: xs, (a, rest)  =>
      let (t, y) := tupleSnocSplit (x' :: xs) rest
      ((a, t), y)

/-- Resolve a hole index to the procedure supplied for it in the argument tuple.
    `HoleIndex.zero` points at the most recently appended hole, which is the *last*
    entry of `holes.toList`, hence the last component of the tuple. -/
def moduleTupleHoleLookup : (holes : HoleSigs) →
    typeListToProdGeneric Prod PUnit (holes.toList.map Procedure) →
    ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Procedure sig
  | .empty,      _    => fun n => nomatch n
  | .append Γ a, args => fun n =>
      have heq : (Γ.append a).toList.map Procedure
               = Γ.toList.map Procedure ++ [Procedure a] := by simp [HoleSigs.toList]
      let split := tupleSnocSplit (Γ.toList.map Procedure) (heq ▸ args)
      match n with
      | .zero   => split.2
      | .succ m => holeLookup Γ split.1 m

/- /-- Plug the procedures in `args` into the corresponding holes of `proc`, replacing each
    `.hole` in the body with a `.call'` of the supplied procedure. -/
@[deprecated "Use ProcedureWithHoles.instantiate"]
def substituteProcedure {holes sig} (proc : ProcedureWithHoles holes sig)
  (args : typeListToProdGeneric Prod PUnit (holes.toList.map Procedure)) :
  Procedure sig := proc.instantiate (holeLookup holes args)
 -/

/-- Convert a basic STLC term of the translated argument-tuple type back into the nested
    tuple of procedures expected by `substituteProcedure`. -/
def basicTermToProcedureArgs : (sigs : List ProcedureSignature) →
    Metatheory.STLCext.BasicTerm
      (moduleTypeToSTLC (typeListToProdGeneric ModuleType.prod ModuleType.unit
        (sigs.map ModuleType.proc))) →
    typeListToProdGeneric Prod PUnit (sigs.map Procedure)
  | [],           _           => PUnit.unit
  | [_],          .value v    => v
  | _ :: s :: ss, .pair hd tl =>
      match hd with
      | .value v => (v, basicTermToProcedureArgs (s :: ss) tl)

open Metatheory.STLCext in
private def basicTermHoleLookup : (holes : HoleSigs) →
    BasicTerm (moduleTypeToSTLC holes.toModuleTypeTuple) →
    ∀ {sig : ProcedureSignature}, HoleIndex holes sig → Procedure sig
  | .empty, _ => fun n => nomatch n
  | .append Γ _, .pair rest (.value v) => fun n =>
      match n with
      | .zero   => v
      | .succ m => basicTermHoleLookup Γ rest m

open Metatheory.STLCext in
noncomputable def procedureToSTLC {holes sig}
  (proc : ProcedureWithHoles holes sig) : Term :=
    let inputType := moduleTypeToSTLC holes.toModuleTypeTuple
    let outputType := moduleTypeToSTLC (.proc sig)
    let inputArrowFree : inputType.isArrowFree := toModuleTypeTuple_isArrowFree holes
    let outputArrowFree : outputType.isArrowFree := by
      simp [outputType, moduleTypeToSTLC, Metatheory.STLCext.Ty.isArrowFree]
    let substitution : BasicTerm inputType → BasicTerm outputType :=
      fun basicTerm =>
        .value (proc.instantiate (basicTermHoleLookup holes basicTerm))
    .func (t := inputType) (u := outputType)
      (ht := inputArrowFree) (hu := outputArrowFree) ⟨holes, sig, proc⟩ substitution

/-- The STLC translation of a procedure-with-holes determines the procedure (and its
    hole/return signatures). -/
theorem procedureToSTLC_inj {holes holes' : HoleSigs} {sig sig' : ProcedureSignature}
    {p : ProcedureWithHoles holes sig} {p' : ProcedureWithHoles holes' sig'} :
    procedureToSTLC p = procedureToSTLC p' → holes = holes' ∧ sig = sig' ∧ p ≍ p' := by
  intro h
  simp only [procedureToSTLC] at h
  rw [Metatheory.STLCext.Term.func.injEq] at h
  obtain ⟨-, -, hdata, -⟩ := h
  -- hdata : (⟨holes, sig, p⟩ : FuncData) = ⟨holes', sig', p'⟩
  injection hdata with h1 h2
  subst h1
  injection (eq_of_heq h2) with h3 h4
  subst h3
  exact ⟨rfl, rfl, h4⟩

noncomputable def moduleExpressionToSTLC :
    ModuleExpression Γ T → Metatheory.STLCext.Term
  | .proc p => .value p
  | .procHoles _ p => procedureToSTLC p
  | .var n => .var n.toNat
  | .app M N => .app (moduleExpressionToSTLC M) (moduleExpressionToSTLC N)
  | .fst M => .fst (moduleExpressionToSTLC M)
  | .snd M => .snd  (moduleExpressionToSTLC M)
  | .abs M => .lam (moduleExpressionToSTLC M)
  | .pair M N => .pair (moduleExpressionToSTLC M) (moduleExpressionToSTLC N)

def moduleContextToSTLC : ModuleContext → Metatheory.STLCext.Context
| .empty => []
| .append Γ T => moduleTypeToSTLC T :: moduleContextToSTLC Γ

theorem moduleExpressionToSTLC_hasType (m : ModuleExpression Γ T) :
  Metatheory.STLCext.HasType (moduleContextToSTLC Γ) (moduleExpressionToSTLC m) (moduleTypeToSTLC T)
   := by induction m with
  | proc c =>
    simp only [moduleExpressionToSTLC, moduleTypeToSTLC]
    exact Metatheory.STLCext.HasType.value c
  | procHoles _ _ =>
    exact Metatheory.STLCext.HasType.func _ _
  | abs M ihM =>
    simp only [moduleExpressionToSTLC, moduleTypeToSTLC, moduleContextToSTLC] at *
    exact Metatheory.STLCext.HasType.lam ihM
  | pair M N ihM ihN =>
    simp only [moduleExpressionToSTLC, moduleTypeToSTLC]
    exact Metatheory.STLCext.HasType.pair ihM ihN
  | app M N ihM ihN =>
    simp only [moduleExpressionToSTLC]
    exact Metatheory.STLCext.HasType.app ihM ihN
  | fst M ihM =>
    simp only [moduleExpressionToSTLC]
    exact Metatheory.STLCext.HasType.fst ihM
  | snd M ihM =>
    simp only [moduleExpressionToSTLC]
    exact Metatheory.STLCext.HasType.snd ihM
  | var n =>
    simp only [moduleExpressionToSTLC]
    apply Metatheory.STLCext.HasType.var
    induction n with
    | zero =>
      simp [ModuleContextIdx.toNat, moduleContextToSTLC]
    | succ n ih =>
      simp [ModuleContextIdx.toNat, moduleContextToSTLC, ih]

def IsPair (m : ModuleExpression Δ (.prod T U)) : Prop :=
  match m with | .pair _ _ => true | _ => false

instance (m : ModuleExpression Δ (.prod T U)) : Decidable (IsPair m) :=
  match m with
  | .pair _ _ => isTrue rfl
  | .var _ | .app _ _ | .fst _ | .snd _ => isFalse Bool.false_ne_true

def IsPair.split [ProgramSpec] {m : ModuleExpression Δ (.prod T U)} (_ : IsPair m) :
    (ModuleExpression Δ T × ModuleExpression Δ U) :=
  match m with
   | .pair m1 m2 => (m1,m2)
   | .fst _ => False.elim (by simp [IsPair] at *)
   | .snd _ => False.elim (by simp [IsPair] at *)
   | .app _ _ => False.elim (by simp [IsPair] at *)
   | .var _ => False.elim (by simp [IsPair] at *)

def IsPair.fst {m : ModuleExpression Δ (.prod T U)} (h : IsPair m) : ModuleExpression Δ T :=
  h.split.1

def IsPair.snd {m : ModuleExpression Δ (.prod T U)} (h : IsPair m) : ModuleExpression Δ U :=
  h.split.2

def IsAbs (m : ModuleExpression Δ T) : Prop :=
  match m with | .abs _ => true | _ => false

instance : Decidable (IsAbs m) :=
  match m with
  | .abs _ => isTrue rfl
  | .var _ | .pair _ _ | .fst _ | .snd _ | .app _ _ | .proc _ | .procHoles _ _ =>
       isFalse Bool.false_ne_true

def IsAbs.body {m : ModuleExpression Δ (.arr T U)} (_ : IsAbs m) :
    ModuleExpression (Δ.append T) U :=
  match m with
   | .abs body => body
   | .fst _ | .snd _ | .var _ | .app _ _ => False.elim (by simp [IsAbs] at *)


lemma HoleSigs.toList_ne_nil {holes : HoleSigs} (h : holes.NonEmpty) : holes.toList ≠ [] := by
  cases holes with
  | empty => exact absurd h (by simp [HoleSigs.NonEmpty])
  | append Γ s => simp [HoleSigs.toList]

/-- Build the proc-tuple argument (a right-nested `.pair` of `.proc`s) from a tuple of
    procedures — the inverse of `IsProcTuple.toArgs`. -/
def procTupleOfArgs {Δ : ModuleContext} : (sigs : List ProcedureSignature) → sigs ≠ [] →
    typeListToProdGeneric Prod PUnit (sigs.map Procedure) →
    ModuleExpression Δ
      (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc))
  | [],           h, _         => absurd rfl h
  | [_],          _, p         => .proc p
  | _ :: s :: ss, _, (p, rest) => .pair (.proc p) (procTupleOfArgs (s :: ss) (by simp) rest)

/-- The erasure of a proc-tuple built by `procTupleOfArgs` is a `BasicTerm` (so it can drive
    the STLC `funcApp` reduction). -/
lemma isBasicType_procTupleOfArgs {Δ : ModuleContext} : (sigs : List ProcedureSignature) →
    (hne : sigs ≠ []) → (args : typeListToProdGeneric Prod PUnit (sigs.map Procedure)) →
    Metatheory.STLCext.Term.isBasicType
      (moduleTypeToSTLC
        (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc)))
      (moduleExpressionToSTLC (procTupleOfArgs (Δ := Δ) sigs hne args))
  | [], hne, _ => absurd rfl hne
  | [_], _, p => by
      simp [procTupleOfArgs, moduleExpressionToSTLC, moduleTypeToSTLC, typeListToProdGeneric,
        List.map, Metatheory.STLCext.Term.isBasicType]
  | _ :: s :: ss, _, (p, rest) => by
      simp only [procTupleOfArgs, moduleExpressionToSTLC, moduleTypeToSTLC, List.map,
        typeListToProdGeneric, Metatheory.STLCext.Term.isBasicType]
      exact ⟨trivial, isBasicType_procTupleOfArgs (Δ := Δ) (s :: ss) (by simp) rest⟩

/-- Round-trip: erasing a `procTupleOfArgs`, converting back to a `BasicTerm`, and reading the
    procedures out recovers the original tuple `args`. -/
lemma basicTermToProcedureArgs_toBasicTerm {Δ : ModuleContext} :
    (sigs : List ProcedureSignature) → (hne : sigs ≠ []) →
    (args : typeListToProdGeneric Prod PUnit (sigs.map Procedure)) →
    (hbasic : Metatheory.STLCext.Term.isBasicType
      (moduleTypeToSTLC
        (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc)))
      (moduleExpressionToSTLC (procTupleOfArgs (Δ := Δ) sigs hne args))) →
    basicTermToProcedureArgs sigs
        (Metatheory.STLCext.Term.toBasicTerm _
          (moduleExpressionToSTLC (procTupleOfArgs (Δ := Δ) sigs hne args)) hbasic)
      = args
  | [], hne, _, _ => absurd rfl hne
  | [_], _, _, _ => rfl
  | _ :: s :: ss, _, (p, rest), hbasic => by
      obtain ⟨hM, hN⟩ := hbasic
      exact congrArg (Prod.mk p)
        (basicTermToProcedureArgs_toBasicTerm (Δ := Δ) (s :: ss) (by simp) rest hN)

/-- Erasure to STLC ignores a type-cast of the module expression. -/
lemma moduleExpressionToSTLC_cast {Δ : ModuleContext} {T T' : ModuleType} (h : T = T')
    (m : ModuleExpression Δ T) :
    moduleExpressionToSTLC (h ▸ m) = moduleExpressionToSTLC m := by cases h; rfl

/-- Inverse round-trip: rebuilding a proc-tuple from the procedures read out of it (via
    `IsProcTuple.toArgs`) gives back the original term. -/
lemma procTupleOfArgs_toArgs {Δ : ModuleContext} : (sigs : List ProcedureSignature) →
    (hne : sigs ≠ []) →
    (m : ModuleExpression Δ
      (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc))) →
    (ipt : IsProcTuple m) →
    procTupleOfArgs sigs hne ipt.toArgs = m
  | [], hne, _, _ => absurd rfl hne
  | [_], _, .proc _, _ => rfl
  | [_], _, .var _, h => absurd h (by simp [IsProcTuple])
  | [_], _, .app _ _, h => absurd h (by simp [IsProcTuple])
  | [_], _, .fst _, h => absurd h (by simp [IsProcTuple])
  | [_], _, .snd _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.proc p) rest, h => by
      simp only [IsProcTuple.toArgs, procTupleOfArgs]
      rw [procTupleOfArgs_toArgs (s :: ss) (by simp) rest h]
  | _ :: s :: ss, _, .pair (.var _) _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.app _ _) _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.fst _) _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.snd _) _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .var _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .app _ _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .fst _, h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .snd _, h => absurd h (by simp [IsProcTuple])

/-- Reading the procedures out of the erasure of an arbitrary proc-tuple `m` recovers
    `ipt.toArgs` — the `IsProcTuple`-indexed analogue of `basicTermToProcedureArgs_toBasicTerm`. -/
lemma basicTermToProcedureArgs_toBasicTerm_toArgs {Δ : ModuleContext} :
    (sigs : List ProcedureSignature) → (hne : sigs ≠ []) →
    (m : ModuleExpression Δ
      (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc))) →
    (ipt : IsProcTuple m) →
    (hbasic : Metatheory.STLCext.Term.isBasicType
      (moduleTypeToSTLC
        (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc)))
      (moduleExpressionToSTLC m)) →
    basicTermToProcedureArgs sigs
        (Metatheory.STLCext.Term.toBasicTerm _ (moduleExpressionToSTLC m) hbasic) = ipt.toArgs
  | [], hne, _, _, _ => absurd rfl hne
  | [_], _, .proc _, _, _ => rfl
  | [_], _, .var _, h, _ => absurd h (by simp [IsProcTuple])
  | [_], _, .app _ _, h, _ => absurd h (by simp [IsProcTuple])
  | [_], _, .fst _, h, _ => absurd h (by simp [IsProcTuple])
  | [_], _, .snd _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.proc p) rest, h, hbasic => by
      obtain ⟨hM, hN⟩ := hbasic
      exact congrArg (Prod.mk p)
        (basicTermToProcedureArgs_toBasicTerm_toArgs (s :: ss) (by simp) rest h hN)
  | _ :: s :: ss, _, .pair (.var _) _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.app _ _) _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.fst _) _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .pair (.snd _) _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .var _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .app _ _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .fst _, h, _ => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, _, .snd _, h, _ => absurd h (by simp [IsProcTuple])


def cbvReductionStep (m : ModuleExpression Δ t) (nn : ¬ Normal m) :
    ModuleExpression Δ t :=
  match m with
  | @ModuleExpression.app _ _  A B hd arg =>
      if abs : IsAbs hd then
        substitute abs.body arg
      else if h : IsProcHoles hd ∧ IsProcTuple arg then
        let ⟨holes, sigs, proc, tconv⟩ := h.1.destruct
        have a : A = procedureHolesToArgumentType holes := by grind
        have b : B = ModuleType.proc sigs := by grind
        let ipt : IsProcTuple (a ▸ arg) := by grind
        let args' := ipt.toArgs
        let result := ModuleExpression.proc (substituteProcedure proc args')
        b ▸ result
      else
        if nn_hd : ¬ Normal hd then
          .app (cbvReductionStep hd nn_hd) arg
        else
          have nn_arg : ¬ Normal arg := fun ha => by
            by_cases hph : IsProcHoles hd
            · exact nn (.neutral (.appProcHoles hph ha (fun hpt => h ⟨hph, hpt⟩)))
            · have hne : Neutral hd := by
                cases not_not.mp nn_hd with
                | neutral ne => exact ne
                | abs _ => exact absurd rfl abs
                | constHoles => exact absurd trivial hph
              exact nn (.neutral (.app hne ha))
          .app hd (cbvReductionStep arg nn_arg)
  | .proc p => absurd .const nn
  | .procHoles _ p => absurd .constHoles nn
  | .abs body =>
      have nn' : ¬ Normal body := fun hb => nn (.abs hb)
      .abs (cbvReductionStep body nn')
  | .pair m1 m2 =>
      if nn1: ¬ Normal m1 then
        .pair (cbvReductionStep m1 nn1) m2
      else
        have nn2 : ¬ Normal m2 := fun h2 => nn (.pair (not_not.mp nn1) h2)
        .pair m1 (cbvReductionStep m2 nn2)
  | .fst m' =>
      if pair: IsPair m' then
        pair.fst
      else
        have nn' : ¬ Normal m' := fun hn => match hn with
          | .neutral ne => nn (.neutral (.fst ne))
          | .pair _ _ => False.elim (by simp [IsPair] at *)
        .fst (cbvReductionStep m' nn')
  | .snd m' =>
      if pair: IsPair m' then
        pair.snd
      else
        have nn' : ¬ Normal m' := fun hn => match hn with
          | .neutral ne => nn (.neutral (.snd ne))
          | .pair _ _ => False.elim (by simp [IsPair] at *)
        .snd (cbvReductionStep m' nn')
  | .var n => absurd (.neutral .var) nn

/-- Non-deterministic single-step reduction: all possible one-step reductions. -/
inductive ReductionStep : ModuleExpression Δ T → ModuleExpression Δ T → Prop where
  | beta    {body : ModuleExpression (ModuleContext.append Δ A) T} {arg : ModuleExpression Δ A} :
      ReductionStep (.app (.abs body) arg) (substitute body arg)
  | appL    {f f' : ModuleExpression Δ (.arr A T)} {arg : ModuleExpression Δ A} :
      ReductionStep f f' → ReductionStep (.app f arg) (.app f' arg)
  | appR    {f : ModuleExpression Δ (.arr A T)} {arg arg' : ModuleExpression Δ A} :
      ReductionStep arg arg' → ReductionStep (.app f arg) (.app f arg')
  | lam     {body body' : ModuleExpression (ModuleContext.append Δ A) B} :
      ReductionStep body body' → ReductionStep (.abs body) (.abs body')
  | pairL   {a a' : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
      ReductionStep a a' → ReductionStep (.pair a b) (.pair a' b)
  | pairR   {a : ModuleExpression Δ A} {b b' : ModuleExpression Δ B} :
      ReductionStep b b' → ReductionStep (.pair a b) (.pair a b')
  | fstPair {a : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
      ReductionStep (.fst (.pair a b)) a
  | fst     {e e' : ModuleExpression Δ (.prod A T)} :
      ReductionStep e e' → ReductionStep (.fst e) (.fst e')
  | sndPair {a : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
      ReductionStep (.snd (.pair a b)) b
  | snd     {e e' : ModuleExpression Δ (.prod A T)} :
      ReductionStep e e' → ReductionStep (.snd e) (.snd e')
  /-- δ-reduction: a procedure-with-holes applied to a ground proc-tuple argument is
      instantiated, producing the closed procedure `substituteProcedure proc args`. -/
  | delta   {holes : HoleSigs} {sigs : ProcedureSignature} {ne : holes.NonEmpty}
            {proc : ProcedureWithHoles holes sigs}
            (args : typeListToProdGeneric Prod PUnit (holes.toList.map Procedure)) :
      ReductionStep
        (.app (.procHoles ne proc) (procTupleOfArgs holes.toList (HoleSigs.toList_ne_nil ne) args))
        (.proc (substituteProcedure proc args))


private lemma moduleExpressionToSTLC_rename_shift (d : Nat)
    {Δ : ModuleContext} {T : ModuleType} (m : ModuleExpression Δ T) :
    ∀ (c : Nat) {Γ : ModuleContext}
      (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T)
      (_ : ∀ {T} (r : ModuleContextIdx Δ T), r.toNat < c → (ρ r).toNat = r.toNat)
      (_ : ∀ {T} (r : ModuleContextIdx Δ T), r.toNat ≥ c → (ρ r).toNat = r.toNat + d),
      moduleExpressionToSTLC (m.rename ρ) =
      Metatheory.STLCext.Term.shift d c (moduleExpressionToSTLC m) := by
  induction m with
  | proc p => intros; simp [ModuleExpression.rename, moduleExpressionToSTLC,
                            Metatheory.STLCext.Term.shift]
  | procHoles ne p =>
    intros
    simp [ModuleExpression.rename, moduleExpressionToSTLC, procedureToSTLC,
          Metatheory.STLCext.Term.shift]
  | var r =>
    intro c Γ ρ hlo hhi
    simp only [ModuleExpression.rename, moduleExpressionToSTLC, Metatheory.STLCext.Term.shift]
    by_cases h : r.toNat < c
    · simp only [h, ite_true]; congr 1; exact hlo _ h
    · simp only [h, ite_false]; congr 1
      have h' : r.toNat ≥ c := Nat.le_of_not_lt h
      have heq := hhi _ h'; omega
  | app f a ihf iha =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, moduleExpressionToSTLC, Metatheory.STLCext.Term.shift,
          ihf c ρ hlo hhi, iha c ρ hlo hhi]
  | fst e ih =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, moduleExpressionToSTLC,
          Metatheory.STLCext.Term.shift, ih c ρ hlo hhi]
  | snd e ih =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, moduleExpressionToSTLC,
          Metatheory.STLCext.Term.shift, ih c ρ hlo hhi]
  | pair a b iha ihb =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, moduleExpressionToSTLC, Metatheory.STLCext.Term.shift,
          iha c ρ hlo hhi, ihb c ρ hlo hhi]
  | abs body ih =>
    intro c Γ ρ hlo hhi
    simp only [ModuleExpression.rename, moduleExpressionToSTLC, Metatheory.STLCext.Term.shift]
    congr 1
    apply ih (c + 1) (liftRenaming ρ)
    · intro T r hr
      cases r with
      | zero => simp [liftRenaming, ModuleContextIdx.toNat]
      | succ r' =>
        simp only [liftRenaming, ModuleContextIdx.toNat] at *
        have := hlo r' (by omega); omega
    · intro T r hr
      cases r with
      | zero => simp [ModuleContextIdx.toNat] at hr
      | succ r' =>
        simp only [liftRenaming, ModuleContextIdx.toNat] at *
        have := hhi r' (by omega); omega

private lemma moduleExpressionToSTLC_substAll_level
    (N_stlc : Metatheory.STLCext.Term)
    {Δ' : ModuleContext} {T : ModuleType} (m : ModuleExpression Δ' T) :
    ∀ (k : Nat) {Γ : ModuleContext}
      (σ : ∀ {T}, ModuleContextIdx Δ' T → ModuleExpression Γ T)
      (_ : ∀ {T} (r : ModuleContextIdx Δ' T),
        moduleExpressionToSTLC (σ r) =
        Metatheory.STLCext.Term.subst k
          (Metatheory.STLCext.Term.shift k 0 N_stlc)
          (Metatheory.STLCext.Term.var r.toNat)),
      moduleExpressionToSTLC (substituteSimultaneously σ m) =
      Metatheory.STLCext.Term.subst k
        (Metatheory.STLCext.Term.shift k 0 N_stlc)
        (moduleExpressionToSTLC m) := by
  induction m with
  | proc p => intros
              simp [substituteSimultaneously, moduleExpressionToSTLC, Metatheory.STLCext.Term.subst]
  | procHoles ne p =>
    intros
    simp [substituteSimultaneously, moduleExpressionToSTLC, procedureToSTLC,
          Metatheory.STLCext.Term.subst]
  | var r =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, moduleExpressionToSTLC, hσ]
  | app f a ihf iha =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, moduleExpressionToSTLC, Metatheory.STLCext.Term.subst,
          ihf k σ hσ, iha k σ hσ]
  | fst e ih =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, moduleExpressionToSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | snd e ih =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, moduleExpressionToSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | pair a b iha ihb =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, moduleExpressionToSTLC, Metatheory.STLCext.Term.subst,
          iha k σ hσ, ihb k σ hσ]
  | abs body ih =>
    intro k Γ σ hσ
    simp only [substituteSimultaneously, moduleExpressionToSTLC, Metatheory.STLCext.Term.subst]
    congr 1
    have hshift : (Metatheory.STLCext.Term.shift k 0 N_stlc).shift1 =
        Metatheory.STLCext.Term.shift (k + 1) 0 N_stlc := by
      simp only [Metatheory.STLCext.Term.shift1]
      rw [show (1 : Int) = ((1 : Nat) : Int) from by norm_num,
          Metatheory.STLCext.Term.shift_shift]
      congr 1; omega
    rw [hshift]
    apply ih (k + 1) (liftSubstitution σ)
    intro T r
    cases r with
    | zero =>
      simp only [liftSubstitution, moduleExpressionToSTLC, ModuleContextIdx.toNat,
                 Metatheory.STLCext.Term.subst]
      simp [show ¬ (0 : Nat) > k + 1 from Nat.not_lt.mpr (Nat.zero_le _)]
    | succ r' =>
      simp only [liftSubstitution, ModuleContextIdx.toNat]
      rw [moduleExpressionToSTLC_rename_shift 1 (σ r') 0 (fun {_} r => .succ r)
        (fun {_} r hr => absurd hr (Nat.not_lt.mpr (Nat.zero_le _)))
        (fun {_} r _ => by simp [ModuleContextIdx.toNat])]
      rw [hσ r']
      have key := Metatheory.STLCext.Term.shift1_subst
          (Metatheory.STLCext.Term.var r'.toNat)
          (Metatheory.STLCext.Term.shift (↑k) 0 N_stlc) k
      simp only [Metatheory.STLCext.Term.shift1] at key hshift
      rw [show (↑(1 : Nat) : Int) = (1 : Int) from by norm_cast, key, hshift]
      simp only [Metatheory.STLCext.Term.shift,
                 show ¬ (r'.toNat < (0 : Nat)) from Nat.not_lt.mpr (Nat.zero_le _), ite_false]
      norm_cast

private lemma moduleExpressionToSTLC_subst
    {Δ : ModuleContext} {u T : ModuleType}
    (body : ModuleExpression (Δ.append u) T) (arg : ModuleExpression Δ u) :
    moduleExpressionToSTLC (substitute body arg) =
    Metatheory.STLCext.Term.subst0 (moduleExpressionToSTLC arg) (moduleExpressionToSTLC body) := by
  simp only [substitute]
  rw [moduleExpressionToSTLC_substAll_level (moduleExpressionToSTLC arg) body 0 (variableSubstitution arg)]
  · simp [Metatheory.STLCext.Term.shift_zero]
  · intro T r
    cases r with
    | zero =>
      simp only [variableSubstitution, ModuleContextIdx.toNat, Metatheory.STLCext.Term.subst]
      simp [Metatheory.STLCext.Term.shift_zero]
    | succ r' =>
      simp only [variableSubstitution, moduleExpressionToSTLC,
                 ModuleContextIdx.toNat, Metatheory.STLCext.Term.subst]
      simp [show r'.toNat + 1 > 0 from Nat.succ_pos _]

private theorem reduce_acc {Γ : ModuleContext} {T : ModuleType} (m : ModuleExpression Γ T) :
    Acc (fun p q : ModuleExpression Γ T =>
      Metatheory.STLCext.Step (moduleExpressionToSTLC q) (moduleExpressionToSTLC p)) m := by
  suffices h : ∀ M : Metatheory.STLCext.Term, Metatheory.STLCext.SN M →
      ∀ (n : ModuleExpression Γ T), moduleExpressionToSTLC n = M → Acc (fun p q =>
          Metatheory.STLCext.Step (moduleExpressionToSTLC q) (moduleExpressionToSTLC p)) n from
    h _ (Metatheory.STLCext.strong_normalization (moduleExpressionToSTLC_hasType m)) m rfl
  intro M sn
  induction sn with
  | intro _ h_acc ih =>
    intro n heq
    apply Acc.intro
    intro q step
    rw [heq] at step
    exact ih _ step q rfl

scoped instance (priority := 1001) {Γ : ModuleContext} {T : ModuleType} :
    WellFoundedRelation (ModuleExpression Γ T) :=
  ⟨fun p q => Metatheory.STLCext.Step (moduleExpressionToSTLC q) (moduleExpressionToSTLC p),
   ⟨reduce_acc⟩⟩

theorem cbvReductionStep_preservation
 {R : ∀ {Γ T}, ModuleExpression Γ T → ModuleExpression Γ T → Prop}
 (pair_left : ∀ {Γ T U} (m1 m1' : ModuleExpression Γ T) (m2 : ModuleExpression Γ U),
              R m1 m1' → R (.pair m1 m2) (.pair m1' m2))
 (pair_right : ∀ {Γ T U} (m1 : ModuleExpression Γ T) (m2 m2' : ModuleExpression Γ U),
               R m2 m2' → R (.pair m1 m2) (.pair m1 m2'))
 (app_left : ∀ {Γ T U} (m1 m1' : ModuleExpression Γ (.arr T U)) (m2 : ModuleExpression Γ T),
               R m1 m1' → R (.app m1 m2) (.app m1' m2))
 (app_right : ∀ {Γ T U} (m1 : ModuleExpression Γ (.arr T U)) (m2 m2' : ModuleExpression Γ T),
              R m2 m2' → R (.app m1 m2) (.app m1 m2'))
 (app_beta : ∀ {Γ T U} (body : ModuleExpression (.append Γ T) U) (arg : ModuleExpression Γ T),
              R (.app (.abs body) arg) (substitute body arg))
 (app_delta : ∀ {Γ holes sig} (ne : holes.NonEmpty) (proc : ProcedureWithHoles holes sig)
              (args : typeListToProdGeneric Prod PUnit (holes.toList.map Procedure)),
              R (.app (.procHoles ne proc)
                    (procTupleOfArgs (Δ := Γ) holes.toList (HoleSigs.toList_ne_nil ne) args))
                (.proc (substituteProcedure proc args)))
 (abs : ∀ {Γ T U} (body body' : ModuleExpression (.append Γ T) U),
        R body body' → R (.abs body) (.abs body'))
 (fst : ∀ {Γ T U} (m m' : ModuleExpression Γ (.prod T U)), R m m' → R (.fst m) (.fst m'))
 (fst_beta : ∀ {Γ T U} (a : ModuleExpression Γ T) (b : ModuleExpression Γ U),
             R (.fst (.pair a b)) a)
 (snd : ∀ {Γ T U} (m m' : ModuleExpression Γ (.prod T U)), R m m' → R (.snd m) (.snd m'))
 (snd_beta : ∀ {Γ T U} (a : ModuleExpression Γ T) (b : ModuleExpression Γ U),
             R (.snd (.pair a b)) b)
 (m : ModuleExpression Γ T) (nn : ¬ Normal m) :
 R m (cbvReductionStep m nn) := by
   induction m
   case proc c => exact absurd Normal.const nn
   case procHoles c => exact absurd Normal.constHoles nn
   case var n => exact absurd (Normal.neutral Neutral.var) nn
   case app hd arg =>
     rename_i inst' Δ A B f x
     simp only [cbvReductionStep]
     split_ifs with h_abs h_cond h_nh
     · -- `f` is an abstraction: β-reduction
       cases f with
       | abs body => simp only [IsAbs.body]; exact app_beta body _
       | procHoles _ _ => simp [IsAbs] at h_abs
       | var _ | app _ _ | fst _ | snd _ => simp [IsAbs] at h_abs
     · -- `f` is a procedure-with-holes applied to a proc-tuple: δ-reduction (via `app_delta`).
       obtain ⟨hph, harg⟩ := h_cond
       cases f with
       | procHoles ne proc =>
           convert app_delta ne proc harg.toArgs using 2
           exact (procTupleOfArgs_toArgs _ (HoleSigs.toList_ne_nil ne) x harg).symm
       | abs _ => exact absurd hph (by simp [IsProcHoles])
       | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
     · -- `f` is Normal: reduce the argument (it must be reducible, else the app is Normal)
       have nn_arg : ¬ Normal x := fun ha => by
         by_cases hph : IsProcHoles f
         · exact nn (.neutral (.appProcHoles hph ha (fun hpt => h_cond ⟨hph, hpt⟩)))
         · have hne : Neutral f := by
             cases h_nh with
             | neutral ne => exact ne
             | abs _ => exact absurd rfl h_abs
             | constHoles => exact absurd trivial hph
           exact nn (.neutral (.app hne ha))
       exact app_right _ _ _ (arg nn_arg)
     · -- `f` is reducible (neutral head)
       exact app_left _ _ _ (hd h_nh)
   case fst m =>
     rename_i inst' Δ A B e
     simp only [cbvReductionStep]
     split_ifs with h_pair
     · cases e with
       | pair p q => simp only [IsPair.fst, IsPair.split]; exact fst_beta p q
       | var _ | app _ _ | fst _ | snd _ => simp [IsPair] at h_pair
     · have nn' : ¬ Normal e := fun hn => match hn with
         | .neutral ne => nn (.neutral (.fst ne))
         | .pair _ _ => h_pair (by simp [IsPair])
       exact fst _ _ (m nn')
   case snd m =>
     rename_i inst' Δ A B e
     simp only [cbvReductionStep]
     split_ifs with h_pair
     · cases e with
       | pair p q => simp only [IsPair.snd, IsPair.split]; exact snd_beta p q
       | var _ | app _ _ | fst _ | snd _ => simp [IsPair] at h_pair
     · have nn' : ¬ Normal e := fun hn => match hn with
         | .neutral ne => nn (.neutral (.snd ne))
         | .pair _ _ => h_pair (by simp [IsPair])
       exact snd _ _ (m nn')
   case abs body =>
     rename_i inst' B Δ A e
     simp only [cbvReductionStep]
     exact abs _ _ (body (fun hb => nn (.abs hb)))
   case pair =>
     rename_i inst' Δ A B p q ihp ihq
     simp only [cbvReductionStep]
     split_ifs with h_nn1
     · have nn2 : ¬ Normal q := fun h2 => nn (.pair h_nn1 h2)
       exact pair_right _ _ _ (ihq nn2)
     · exact pair_left _ _ _ (ihp h_nn1)

theorem cbvReductionStep_is_reductionStep (m : ModuleExpression Γ T) (nn : ¬ Normal m) :
    ReductionStep m (cbvReductionStep m nn) :=
  cbvReductionStep_preservation (R := ReductionStep)
    (pair_left  := fun _ _ _ h => .pairL h)
    (pair_right := fun _ _ _ h => .pairR h)
    (app_left   := fun _ _ _ h => .appL h)
    (app_right  := fun _ _ _ h => .appR h)
    (app_beta   := fun _ _     => .beta)
    (app_delta  := fun _ _ args => .delta args)
    (abs        := fun _ _ h   => .lam h)
    (fst        := fun _ _ h   => .fst h)
    (fst_beta   := fun _ _     => .fstPair)
    (snd        := fun _ _ h   => .snd h)
    (snd_beta   := fun _ _     => .sndPair)
    m nn

omit [ProgramSpec] in
private lemma ModuleContextIdx.toNat_inj' {Γ : ModuleContext} :
  ∀ {T1 T2 : ModuleType} (r1 : ModuleContextIdx Γ T1) (r2 : ModuleContextIdx Γ T2),
    r1.toNat = r2.toNat → T1 = T2 ∧ HEq r1 r2
  | _, _, .zero,    .zero,    _ => ⟨rfl, HEq.rfl⟩
  | _, _, .zero,    .succ _,  h => by simp [ModuleContextIdx.toNat] at h
  | _, _, .succ _,  .zero,    h => by simp [ModuleContextIdx.toNat] at h
  | _, _, .succ r1', .succ r2', h => by
      simp only [ModuleContextIdx.toNat, Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at h
      obtain ⟨hT, hr⟩ := ModuleContextIdx.toNat_inj' r1' r2' h
      subst hT
      exact ⟨rfl, heq_of_eq (congrArg ModuleContextIdx.succ (eq_of_heq hr))⟩

omit [ProgramSpec] in
private lemma ModuleContextIdx.toNat_inj {Γ : ModuleContext} {T : ModuleType} :
  ∀ (r r' : ModuleContextIdx Γ T), r.toNat = r'.toNat → r = r'
  | .zero,   .zero,    _ => rfl
  | .zero,   .succ _,  h => by simp [ModuleContextIdx.toNat] at h
  | .succ _, .zero,    h => by simp [ModuleContextIdx.toNat] at h
  | .succ r, .succ r', h =>
       congrArg ModuleContextIdx.succ (ModuleContextIdx.toNat_inj r r' (Nat.succ.inj h))

def ModuleExpression.erasedEqual
  (m : ModuleExpression Γ T) (m' : ModuleExpression Γ' T') : Prop := match m, m' with
  | @ModuleExpression.proc _ _ sig p, @ModuleExpression.proc _ _ sig' p' => sig = sig' ∧ p ≍ p'
  | @ModuleExpression.procHoles _ _ holes sig _ p,
    @ModuleExpression.procHoles _ _ holes' sig' _ p' => holes = holes' ∧ sig = sig' ∧ p ≍ p'
  | .var r, .var r' => r.toNat = r'.toNat
  | .app f a, .app f' a' => ModuleExpression.erasedEqual f f' ∧ ModuleExpression.erasedEqual a a'
  | .fst e, .fst e' => ModuleExpression.erasedEqual e e'
  | .snd e, .snd e' => ModuleExpression.erasedEqual e e'
  | .pair a b, .pair a' b' => ModuleExpression.erasedEqual a a' ∧ ModuleExpression.erasedEqual b b'
  | .abs body, .abs body' => ModuleExpression.erasedEqual body body'
  | _, _ => False

private theorem moduleTypeToSTLC_injective {a b : ModuleType}
    (h : moduleTypeToSTLC a = moduleTypeToSTLC b) : a = b := by
  induction a generalizing b with
  | proc s => cases b <;> simp_all [moduleTypeToSTLC]
  | unit => cases b <;> simp_all [moduleTypeToSTLC]
  | arr A B ihA ihB =>
      cases b with
      | arr A' B' =>
          simp only [moduleTypeToSTLC, Metatheory.STLCext.Ty.arr.injEq] at h; rw [ihA h.1, ihB h.2]
      | _ => simp [moduleTypeToSTLC] at h
  | prod A B ihA ihB =>
      cases b with
      | prod A' B' =>
          simp only [moduleTypeToSTLC, Metatheory.STLCext.Ty.prod.injEq] at h; rw [ihA h.1, ihB h.2]
      | _ => simp [moduleTypeToSTLC] at h

omit [ProgramSpec] in
private theorem typeListToProd_proc_inj {l1 l2 : List ProcedureSignature}
      (h : typeListToProdGeneric ModuleType.prod ModuleType.unit (l1.map ModuleType.proc)
        = typeListToProdGeneric ModuleType.prod ModuleType.unit (l2.map ModuleType.proc)) :
     l1 = l2 := by
  revert l2 h
  induction l1 with
  | nil => intro l2 h; cases l2 with
    | nil => rfl
    | cons b bs => cases bs <;> simp_all [typeListToProdGeneric, List.map]
  | cons a as iha => intro l2 h; cases l2 with
    | nil => cases as <;> simp_all [typeListToProdGeneric, List.map]
    | cons b bs =>
        cases as with
        | nil => cases bs <;> simp_all [typeListToProdGeneric, List.map]
        | cons a' as' => cases bs with
          | nil => simp_all [typeListToProdGeneric, List.map]
          | cons b' bs' =>
              simp only [List.map, typeListToProdGeneric, ModuleType.prod.injEq,
                ModuleType.proc.injEq] at h
              obtain ⟨rfl, hrest⟩ := h
              rw [iha (l2 := b' :: bs') hrest]

-- TODO move to Syntax.lean
omit [ProgramSpec] in
private theorem HoleSigs.toList_injective :
    ∀ {h1 h2 : HoleSigs}, h1.toList = h2.toList → h1 = h2 := by
  intro h1
  induction h1 with
  | empty => intro h2 h; cases h2 with
    | empty => rfl
    | append hs s => simp [HoleSigs.toList] at h
  | append hs s ih => intro h2 h; cases h2 with
    | empty => simp [HoleSigs.toList] at h
    | append hs' s' =>
        simp only [HoleSigs.toList] at h
        obtain ⟨hl, hr⟩ := List.append_inj' h rfl
        obtain rfl := ih hl
        simp_all

omit [ProgramSpec] in
private theorem procedureHolesToArgumentType_injective {h1 h2 : HoleSigs}
    (h : procedureHolesToArgumentType h1 = procedureHolesToArgumentType h2) : h1 = h2 := by
  apply HoleSigs.toList_injective
  apply typeListToProd_proc_inj
  exact h

theorem moduleExpressionToSTLC_injective {Γ Γ' : ModuleContext} {T T' : ModuleType}
    (m : ModuleExpression Γ T) (m' : ModuleExpression Γ' T') :
    moduleExpressionToSTLC m = moduleExpressionToSTLC m' → ModuleExpression.erasedEqual m m' := by
  revert Γ' T' m'
  induction m with
  | proc p =>
    intro Γ' T' m' h
    cases m' <;> simp_all [moduleExpressionToSTLC, ModuleExpression.erasedEqual, procedureToSTLC]
  | procHoles ne p =>
    intro Γ' T' m' h
    cases m' with
    | procHoles ne' p' =>
        simp only [moduleExpressionToSTLC] at h
        exact procedureToSTLC_inj h
    | proc _ | var _ | app _ _ | fst _ | snd _ | abs _ | pair _ _ =>
        simp_all [moduleExpressionToSTLC, procedureToSTLC]
  | var r =>
    intro Γ' T' m' h
    cases m' <;> simp_all [moduleExpressionToSTLC, ModuleExpression.erasedEqual, procedureToSTLC]
  | app f a ihf iha =>
    intro Γ' T' m' h
    cases m' with
    | app f' a' =>
      simp only [moduleExpressionToSTLC, Metatheory.STLCext.Term.app.injEq] at h
      exact ⟨ihf f' h.1, iha a' h.2⟩
    | _ => simp [moduleExpressionToSTLC, procedureToSTLC] at h
  | fst e ih =>
    intro Γ' T' m' h
    cases m' with
    | fst e' =>
      simp only [moduleExpressionToSTLC, Metatheory.STLCext.Term.fst.injEq] at h
      exact ih e' h
    | _ => simp [moduleExpressionToSTLC, procedureToSTLC] at h
  | snd e ih =>
    intro Γ' T' m' h
    cases m' with
    | snd e' =>
      simp only [moduleExpressionToSTLC, Metatheory.STLCext.Term.snd.injEq] at h
      exact ih e' h
    | _ => simp [moduleExpressionToSTLC, procedureToSTLC] at h
  | pair a b iha ihb =>
    intro Γ' T' m' h
    cases m' with
    | pair a' b' =>
      simp only [moduleExpressionToSTLC, Metatheory.STLCext.Term.pair.injEq] at h
      exact ⟨iha a' h.1, ihb b' h.2⟩
    | _ => simp [moduleExpressionToSTLC, procedureToSTLC] at h
  | abs body ih =>
    intro Γ' T' m' h
    cases m' with
    | abs body' =>
      simp only [moduleExpressionToSTLC, Metatheory.STLCext.Term.lam.injEq] at h
      exact ih body' h
    | _ => simp [moduleExpressionToSTLC, procedureToSTLC] at h

theorem ModuleExpression.erasedEqual_refl (m : ModuleExpression Γ T) :
  ModuleExpression.erasedEqual m m := by
  induction m with
  | proc => exact ⟨rfl, HEq.refl _⟩
  | procHoles => exact ⟨rfl, rfl, HEq.refl _⟩
  | var r => simp [ModuleExpression.erasedEqual]
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | fst e ih => exact ih
  | snd e ih => exact ih
  | pair a b iha ihb => exact ⟨iha, ihb⟩
  | abs body ih => exact ih

theorem ModuleExpression.erasedEqual_pair_right (a : ModuleExpression Γ T)
  {b : ModuleExpression Γ U} {b' : ModuleExpression Γ U'} (h : ModuleExpression.erasedEqual b b') :
  ModuleExpression.erasedEqual (.pair a b) (.pair a b') :=
  ⟨ModuleExpression.erasedEqual_refl a, h⟩

theorem ModuleExpression.erasedEqual_pair_left
    {a : ModuleExpression Γ T} {a' : ModuleExpression Γ T'}
    (b : ModuleExpression Γ U) (h : ModuleExpression.erasedEqual a a') :
    ModuleExpression.erasedEqual (.pair a b) (.pair a' b) :=
  ⟨h, ModuleExpression.erasedEqual_refl b⟩

theorem reductionStep_stlc_compat (m m' : ModuleExpression Γ T) :
    ReductionStep m m' →
    Metatheory.STLCext.Step (moduleExpressionToSTLC m) (moduleExpressionToSTLC m') := by
  intro h
  induction h with
  | beta =>
      simp only [moduleExpressionToSTLC]
      rw [moduleExpressionToSTLC_subst]
      exact .beta _ _
  | appL _ ih => simp only [moduleExpressionToSTLC]; exact .appL ih
  | appR _ ih => simp only [moduleExpressionToSTLC]; exact .appR ih
  | lam _ ih  => simp only [moduleExpressionToSTLC]; exact .lam ih
  | pairL _ ih => simp only [moduleExpressionToSTLC]; exact .pairL ih
  | pairR _ ih => simp only [moduleExpressionToSTLC]; exact .pairR ih
  | fstPair => simp only [moduleExpressionToSTLC]; exact .fstPair _ _
  | fst _ ih  => simp only [moduleExpressionToSTLC]; exact .fst ih
  | sndPair => simp only [moduleExpressionToSTLC]; exact .sndPair _ _
  | snd _ ih  => simp only [moduleExpressionToSTLC]; exact .snd ih
  | delta args =>
      rename_i Δ holes sigs ne proc
      -- δ-step ⟷ STLC `funcApp`: the erased argument is basic (`isBasicType_procTupleOfArgs`),
      -- and reading the procedures back out recovers `args`
      -- (`basicTermToProcedureArgs_toBasicTerm`), so `funcApp`'s reduct is `.value (subst args)`.
      have hb := isBasicType_procTupleOfArgs (Δ := Δ) holes.toList (HoleSigs.toList_ne_nil ne) args
      have key := basicTermToProcedureArgs_toBasicTerm (Δ := Δ) holes.toList
        (HoleSigs.toList_ne_nil ne) args hb
      simp only [moduleExpressionToSTLC, procedureToSTLC]
      rw [show Metatheory.STLCext.Term.value (substituteProcedure proc args)
            = Metatheory.STLCext.BasicTerm.toTerm
                ((fun bt => Metatheory.STLCext.BasicTerm.value
                    (substituteProcedure proc (basicTermToProcedureArgs holes.toList bt)))
                  (Metatheory.STLCext.Term.toBasicTerm _
                    (moduleExpressionToSTLC
                      (procTupleOfArgs (Δ := Δ) holes.toList (HoleSigs.toList_ne_nil ne) args)) hb))
            from by simp only [Metatheory.STLCext.BasicTerm.toTerm]; rw [key]]
      exact Metatheory.STLCext.Step.funcApp _ _ _ hb

/-- For an argument of a procedure-tuple type, being a `BasicTerm` after erasure means it is
    a proc-tuple.  (So a non-proc-tuple argument blocks the STLC `funcApp` reduction.) -/
private lemma isBasicType_imp_isProcTuple {Δ : ModuleContext} :
    (sigs : List ProcedureSignature) →
    (arg : ModuleExpression Δ
        (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc))) →
    Metatheory.STLCext.Term.isBasicType
        (moduleTypeToSTLC
          (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc)))
        (moduleExpressionToSTLC arg) →
    IsProcTuple arg
  | [], arg, h => by
      cases arg <;>
        simp_all [moduleExpressionToSTLC, moduleTypeToSTLC, Metatheory.STLCext.Term.isBasicType]
  | [_], arg, h => by
      cases arg <;>
        simp_all [moduleExpressionToSTLC, moduleTypeToSTLC, Metatheory.STLCext.Term.isBasicType,
          IsProcTuple]
  | _ :: s :: ss, arg, h => by
      cases arg with
      | pair a b =>
          cases a with
          | proc p =>
              simp only [moduleExpressionToSTLC, moduleTypeToSTLC,
                Metatheory.STLCext.Term.isBasicType] at h
              exact isBasicType_imp_isProcTuple (s :: ss) b h.2
          | var _ | app _ _ | fst _ | snd _ =>
              simp only [moduleExpressionToSTLC, moduleTypeToSTLC,
                Metatheory.STLCext.Term.isBasicType] at h
              exact h.1.elim
      | var _ | app _ _ | fst _ | snd _ =>
          simp_all [moduleExpressionToSTLC, moduleTypeToSTLC, Metatheory.STLCext.Term.isBasicType]

theorem reductionStep_stlc_complete
  (m : ModuleExpression Γ T) (M' : Metatheory.STLCext.Term)
  (h : Metatheory.STLCext.Step (moduleExpressionToSTLC m) M') :
    ∃ m', ReductionStep m m' ∧ moduleExpressionToSTLC m' = M' := by
  induction m generalizing M' with
  | proc _ | procHoles _ _ | var _ => simp only [moduleExpressionToSTLC] at h; cases h
  | app f arg ihf iharg =>
      -- case-split on f first so moduleExpressionToSTLC f is a literal constructor
      -- after simp, enabling cases h without dependent-elim failures
      cases f with
      | abs body =>
          simp only [moduleExpressionToSTLC] at h
          cases h with
          | beta => exact ⟨substitute body arg, .beta, moduleExpressionToSTLC_subst body arg⟩
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp [moduleExpressionToSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.abs body) arg', .appR hnd, by simp [moduleExpressionToSTLC, heq]⟩
      | procHoles ne proc =>
          simp only [moduleExpressionToSTLC, procedureToSTLC] at h
          cases h with
          | appL step => nomatch step
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.procHoles ne proc) arg', .appR hnd,
                by simp [moduleExpressionToSTLC, procedureToSTLC, heq]⟩
          | funcApp d g N hbasic =>
              have ipt : IsProcTuple arg := isBasicType_imp_isProcTuple _ arg hbasic
              refine ⟨.proc (substituteProcedure proc ipt.toArgs), ?_, ?_⟩
              · convert ReductionStep.delta (proc := proc) ipt.toArgs using 2
                exact (procTupleOfArgs_toArgs _ (HoleSigs.toList_ne_nil ne) arg ipt).symm
              · simp only [moduleExpressionToSTLC, Metatheory.STLCext.BasicTerm.toTerm,
                  procedureHolesToArgumentType]
                rw [basicTermToProcedureArgs_toBasicTerm_toArgs _ (HoleSigs.toList_ne_nil ne)
                  arg ipt hbasic]
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [moduleExpressionToSTLC] at h
          cases h with
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp [moduleExpressionToSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app _ arg', .appR hnd, by simp [moduleExpressionToSTLC, heq]⟩
  | abs body ih =>
      simp only [moduleExpressionToSTLC] at h
      cases h with
      | lam step =>
          obtain ⟨body', hnd, heq⟩ := ih _ step
          exact ⟨.abs body', .lam hnd, by simp [moduleExpressionToSTLC, heq]⟩
  | pair a b iha ihb =>
      simp only [moduleExpressionToSTLC] at h
      cases h with
      | pairL step =>
          obtain ⟨a', hnd, heq⟩ := iha _ step
          exact ⟨.pair a' b, .pairL hnd, by simp [moduleExpressionToSTLC, heq]⟩
      | pairR step =>
          obtain ⟨b', hnd, heq⟩ := ihb _ step
          exact ⟨.pair a b', .pairR hnd, by simp [moduleExpressionToSTLC, heq]⟩
  | fst e ih =>
      -- case-split on e first for the same reason
      cases e with
      | pair e1 e2 =>
          simp only [moduleExpressionToSTLC] at h
          cases h with
          | fstPair => exact ⟨e1, .fstPair, rfl⟩
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp [moduleExpressionToSTLC, heq]⟩
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [moduleExpressionToSTLC] at h
          cases h with
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp [moduleExpressionToSTLC, heq]⟩
  | snd e ih =>
      cases e with
      | pair e1 e2 =>
          simp only [moduleExpressionToSTLC] at h
          cases h with
          | sndPair => exact ⟨e2, .sndPair, rfl⟩
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp [moduleExpressionToSTLC, heq]⟩
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [moduleExpressionToSTLC] at h
          cases h with
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp [moduleExpressionToSTLC, heq]⟩


-- TODO should be a simple corollary of reductionStep_stlc_compat
theorem cbvReductionStep_stlc_compat (m : ModuleExpression Γ T) (nn : ¬ Normal m) :
  Metatheory.STLCext.Step (moduleExpressionToSTLC m)
                          (moduleExpressionToSTLC (cbvReductionStep m nn)) := by
  induction m with
  | proc => exact absurd .const nn
  | procHoles => exact absurd .constHoles nn
  | var => exact absurd (.neutral .var) nn
  | app hd arg ihhd iharg =>
    -- With induction m: hd is the function (arrow type), arg is the argument
    simp only [cbvReductionStep, moduleExpressionToSTLC]
    split_ifs with h_abs h_cond h_nh
    · -- beta: hd (function) is .abs
      rw [moduleExpressionToSTLC_subst]
      have h_meq : moduleExpressionToSTLC hd =
          Metatheory.STLCext.Term.lam (moduleExpressionToSTLC h_abs.body) := by
        cases hd with
        | abs body => simp [IsAbs.body, moduleExpressionToSTLC]
        | procHoles _ _ => simp [IsAbs] at h_abs
        | var _ | app _ _ | fst _ | snd _ => simp [IsAbs] at h_abs
      rw [h_meq]
      exact Metatheory.STLCext.Step.beta _ _
    · -- δ: reduce to `reductionStep_stlc_compat` via a `ReductionStep.delta`.
      refine reductionStep_stlc_compat (hd.app arg) _ ?step
      obtain ⟨hph, harg⟩ := h_cond
      cases hd with
      | procHoles ne proc =>
          convert ReductionStep.delta (proc := proc) harg.toArgs using 2
          exact (procTupleOfArgs_toArgs _ (HoleSigs.toList_ne_nil ne) arg harg).symm
      | abs _ => exact absurd hph (by simp [IsProcHoles])
      | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    · -- hd is Normal: reduce the argument
      simp only [moduleExpressionToSTLC]
      have h_nn_arg : ¬ Normal arg := fun ha => by
        by_cases hph : IsProcHoles hd
        · exact nn (.neutral (.appProcHoles hph ha (fun hpt => h_cond ⟨hph, hpt⟩)))
        · have hne : Neutral hd := by
            cases h_nh with
            | neutral ne => exact ne
            | abs _ => simp [IsAbs] at h_abs
            | constHoles => exact absurd trivial hph
          exact nn (.neutral (.app hne ha))
      exact Metatheory.STLCext.Step.appR (iharg h_nn_arg)
    · -- appL: hd (function) not normal, reduce it
      simp only [moduleExpressionToSTLC]
      exact Metatheory.STLCext.Step.appL (ihhd h_nh)
  | fst m' ih =>
    simp only [cbvReductionStep, moduleExpressionToSTLC]
    split_ifs with h_pair
    · cases m' with
      | pair m1 m2 =>
        simp only [IsPair.fst, IsPair.split, moduleExpressionToSTLC]
        exact Metatheory.STLCext.Step.fstPair _ _
      | var _ | app _ _ | fst _ | snd _ => simp [IsPair] at h_pair
    · simp only [moduleExpressionToSTLC]
      have nn' : ¬ Normal m' := fun hn => match hn with
        | .neutral ne => nn (.neutral (.fst ne))
        | .pair _ _ => h_pair (by simp [IsPair])
      exact Metatheory.STLCext.Step.fst (ih nn')
  | snd m' ih =>
    simp only [cbvReductionStep, moduleExpressionToSTLC]
    split_ifs with h_pair
    · cases m' with
      | pair m1 m2 =>
        simp only [IsPair.snd, IsPair.split, moduleExpressionToSTLC]
        exact Metatheory.STLCext.Step.sndPair _ _
      | var _ | app _ _ | fst _ | snd _ => simp [IsPair] at h_pair
    · simp only [moduleExpressionToSTLC]
      have nn' : ¬ Normal m' := fun hn => match hn with
        | .neutral ne => nn (.neutral (.snd ne))
        | .pair _ _ => h_pair (by simp [IsPair])
      exact Metatheory.STLCext.Step.snd (ih nn')
  | abs body ih =>
    simp only [cbvReductionStep, moduleExpressionToSTLC]
    exact Metatheory.STLCext.Step.lam (ih (fun hb => nn (.abs hb)))
  | pair m1 m2 ih1 ih2 =>
    simp only [cbvReductionStep, moduleExpressionToSTLC]
    split_ifs with h1
    · -- split_ifs gives Normal m1 first (after not_not simplification)
      simp only [moduleExpressionToSTLC]
      have h2 : ¬ Normal m2 := fun h2 => nn (.pair h1 h2)
      exact Metatheory.STLCext.Step.pairR (ih2 h2)
    · simp only [moduleExpressionToSTLC]
      exact Metatheory.STLCext.Step.pairL (ih1 h1)


def reduce (m : ModuleExpression Γ T) : ModuleExpression Γ T :=
    if h : Normal m then m
    else
      reduce (cbvReductionStep m h)
termination_by m
decreasing_by exact cbvReductionStep_stlc_compat m h


def MultiStepReduction : ModuleExpression Γ T → ModuleExpression Γ T → Prop :=
  Rewriting.Star ReductionStep

theorem multiStepReduction_reduce {m : ModuleExpression Γ T} :
    MultiStepReduction m (reduce m) := by
  apply WellFoundedRelation.wf.induction (C := fun m => MultiStepReduction m (reduce m)) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact Rewriting.Star.refl _
  · exact Rewriting.Star.head (cbvReductionStep_is_reductionStep n h)
                              (ih _ (cbvReductionStep_stlc_compat n h))

theorem multiStepReduction_to_stlc_star {m m' : ModuleExpression Γ T}
    (h : MultiStepReduction m m') :
    Rewriting.Star Metatheory.STLCext.Step (moduleExpressionToSTLC m) (moduleExpressionToSTLC m')
    := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail hab hbc ih => exact Rewriting.Star.tail ih (reductionStep_stlc_compat _ _ hbc)

theorem moduleExpressionToSTLC_Normal_iff {m : ModuleExpression Γ T} :
    Normal m ↔ Rewriting.IsNormalForm Metatheory.STLCext.Step (moduleExpressionToSTLC m) := by
  constructor
  · intro hm
    suffices key : ∀ {Γ' : ModuleContext} {T' : ModuleType} (m' : ModuleExpression Γ' T'),
        (Normal m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (moduleExpressionToSTLC m')) ∧
        (Neutral m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (moduleExpressionToSTLC m') ∧
                     (∀ body, moduleExpressionToSTLC m' ≠ Metatheory.STLCext.Term.lam body) ∧
                     (∀ P Q, moduleExpressionToSTLC m' ≠ Metatheory.STLCext.Term.pair P Q)) from
      (key m).1 hm
    intro Γ' T' m'
    induction m' with
    | var n =>
      constructor
      · intro _ N h; simp only [moduleExpressionToSTLC] at h; cases h
      · intro _; refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
        · simp only [moduleExpressionToSTLC] at h; cases h
        · intro h; cases h
        · intro h; cases h
    | proc _ | procHoles _ _ =>
      constructor
      · intro _ N h; simp only [moduleExpressionToSTLC] at h; cases h
      · intro h; cases h
    | abs body ih =>
      constructor
      · intro hn N h
        simp only [moduleExpressionToSTLC] at h
        cases hn with
        | neutral hne => exact nomatch hne
        | abs hb => cases h with | lam step => exact (ih.1 hb) _ step
      · intro h; exact nomatch h
    | pair a b iha ihb =>
      constructor
      · intro hn N h
        simp only [moduleExpressionToSTLC] at h
        cases hn with
        | neutral hne => exact nomatch hne
        | pair ha hb =>
          cases h with
          | pairL step => exact (iha.1 ha) _ step
          | pairR step => exact (ihb.1 hb) _ step
      · intro h; exact nomatch h
    | app f arg ihf iharg =>
      constructor
      · intro hn N h
        simp only [moduleExpressionToSTLC] at h
        cases hn with
        | neutral hne =>
          cases hne with
          | app hf_n harg_n =>
            obtain ⟨ihf_step, ihf_lam, _⟩ := ihf.2 hf_n
            generalize hF : moduleExpressionToSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [moduleExpressionToSTLC] at hF
          | appProcHoles hph ha hpt =>
            cases f with
            | procHoles ne p =>
                simp only [moduleExpressionToSTLC, procedureToSTLC] at h
                cases h with
                | appL step => nomatch step
                | appR step => exact (iharg.1 ha) _ step
                | funcApp d g N' hbasic =>
                    exact absurd (isBasicType_imp_isProcTuple _ _ hbasic) hpt
            | abs _ => exact absurd hph (by simp [IsProcHoles])
            | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
      · intro hne
        cases hne with
        | app hf_n harg_n =>
          obtain ⟨ihf_step, ihf_lam, ihf_pair⟩ := ihf.2 hf_n
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [moduleExpressionToSTLC] at h
            generalize hF : moduleExpressionToSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [moduleExpressionToSTLC] at hF
          · intro h; cases h
          · intro h; cases h
        | appProcHoles hph ha hpt =>
          cases f with
          | procHoles ne p =>
              refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
              · simp only [moduleExpressionToSTLC, procedureToSTLC] at h
                cases h with
                | appL step => nomatch step
                | appR step => exact (iharg.1 ha) _ step
                | funcApp d g N' hbasic =>
                    exact absurd (isBasicType_imp_isProcTuple _ _ hbasic) hpt
              · intro h; cases h
              · intro h; cases h
          | abs _ => exact absurd hph (by simp [IsProcHoles])
          | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    | fst e ihe =>
      constructor
      · intro hn N h
        simp only [moduleExpressionToSTLC] at h
        cases hn with | neutral hne => cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : moduleExpressionToSTLC e = E at h
          cases h with
          | fstPair => exact absurd hE (ihe_pair _ _)
          | fst step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [moduleExpressionToSTLC] at h
            generalize hE : moduleExpressionToSTLC e = E at h
            cases h with
            | fstPair => exact absurd hE (ihe_pair _ _)
            | fst step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h
    | snd e ihe =>
      constructor
      · intro hn N h
        simp only [moduleExpressionToSTLC] at h
        cases hn with | neutral hne => cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : moduleExpressionToSTLC e = E at h
          cases h with
          | sndPair => exact absurd hE (ihe_pair _ _)
          | snd step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [moduleExpressionToSTLC] at h
            generalize hE : moduleExpressionToSTLC e = E at h
            cases h with
            | sndPair => exact absurd hE (ihe_pair _ _)
            | snd step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h
  · intro h
    by_contra hnn
    exact h _ (reductionStep_stlc_compat m _ (cbvReductionStep_is_reductionStep m hnn))

theorem multiStepReduction_stlc_complete (m : ModuleExpression Γ T) {M' : Metatheory.STLCext.Term}
    (h : Rewriting.Star Metatheory.STLCext.Step (moduleExpressionToSTLC m) M') :
    ∃ m' : ModuleExpression Γ T, MultiStepReduction m m' ∧ moduleExpressionToSTLC m' = M' := by
  induction h with
  | refl => exact ⟨m, Rewriting.Star.refl _, rfl⟩
  | tail hab hbc ih =>
    obtain ⟨m_b, hred_b, heq_b⟩ := ih
    rw [← heq_b] at hbc
    obtain ⟨m', hnd, heq'⟩ := reductionStep_stlc_complete m_b _ hbc
    exact ⟨m', Rewriting.Star.tail hred_b hnd, heq'⟩

private theorem ModuleExpression.erasedEqual_normal_neutral_eq
    {Γ : ModuleContext} {T1 T2 : ModuleType}
    (m : ModuleExpression Γ T1) (m' : ModuleExpression Γ T2)
    (h : ModuleExpression.erasedEqual m m') :
    (Normal m → T1 = T2 → HEq m m') ∧ (Neutral m → T1 = T2 ∧ HEq m m') := by
  induction m generalizing T2 with
  | proc p =>
    refine ⟨fun _ _ => ?_, fun hne => by cases hne⟩
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case proc p' =>
      obtain ⟨hsig, hp⟩ := h
      subst hsig
      exact heq_of_eq (congrArg ModuleExpression.proc (eq_of_heq hp))
  | procHoles ne p =>
    refine ⟨fun _ _ => ?_, fun hne => by cases hne⟩
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case procHoles ne' p' =>
      obtain ⟨hholes, hsig, hp⟩ := h
      subst hholes; subst hsig
      obtain rfl := eq_of_heq hp
      rfl
  | var r =>
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case var r' =>
      obtain ⟨hT, hr⟩ := ModuleContextIdx.toNat_inj' _ _ h
      subst hT
      have heq : HEq (ModuleExpression.var r) (ModuleExpression.var r') :=
        heq_of_eq (congrArg ModuleExpression.var (eq_of_heq hr))
      exact ⟨fun _ _ => heq, fun _ => ⟨rfl, heq⟩⟩
  | app f arg ihf iharg =>
    cases m' with
    | app f' arg' =>
      simp only [ModuleExpression.erasedEqual] at h
      obtain ⟨hf_eq, harg_eq⟩ := h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | app hf ha =>
            obtain ⟨hTf, hf_heq⟩ := (ihf f' hf_eq).2 hf
            obtain ⟨hA, hB⟩ := ModuleType.arr.inj hTf
            subst hA hB
            exact (eq_of_heq hf_heq) ▸ (eq_of_heq ((iharg arg' harg_eq).1 ha rfl)) ▸ HEq.rfl
          | appProcHoles hph ha hpt =>
            cases f with
            | procHoles ne p =>
                cases f' with
                | procHoles ne' p' =>
                    simp only [ModuleExpression.erasedEqual] at hf_eq
                    obtain ⟨hh, hs, hp⟩ := hf_eq
                    subst hh; subst hs; obtain rfl := eq_of_heq hp
                    obtain rfl := eq_of_heq ((iharg arg' harg_eq).1 ha rfl)
                    rfl
                | var _ | app _ _ | fst _ | snd _ | abs _ =>
                    simp [ModuleExpression.erasedEqual] at hf_eq
            | abs _ => exact absurd hph (by simp [IsProcHoles])
            | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
      · intro hne
        cases hne with
        | app hf ha =>
          obtain ⟨hTf, hf_heq⟩ := (ihf f' hf_eq).2 hf
          obtain ⟨hA, hB⟩ := ModuleType.arr.inj hTf
          subst hA hB
          exact ⟨rfl, (eq_of_heq hf_heq) ▸ (eq_of_heq ((iharg arg' harg_eq).1 ha rfl)) ▸ HEq.rfl⟩
        | appProcHoles hph ha hpt =>
          cases f with
          | procHoles ne p =>
              cases f' with
              | procHoles ne' p' =>
                  simp only [ModuleExpression.erasedEqual] at hf_eq
                  obtain ⟨hh, hs, hp⟩ := hf_eq
                  subst hh; subst hs; obtain rfl := eq_of_heq hp
                  obtain rfl := eq_of_heq ((iharg arg' harg_eq).1 ha rfl)
                  exact ⟨rfl, HEq.rfl⟩
              | var _ | app _ _ | fst _ | snd _ | abs _ =>
                  simp [ModuleExpression.erasedEqual] at hf_eq
          | abs _ => exact absurd hph (by simp [IsProcHoles])
          | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    | _ => simp [ModuleExpression.erasedEqual] at h
  | fst e ihe =>
    cases m' with
    | fst e' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | fst hne' =>
            obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
            obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
            subst hA hB
            exact heq_of_eq (congrArg ModuleExpression.fst (eq_of_heq he_heq))
      · intro hne
        cases hne with
        | fst hne' =>
          obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
          obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
          subst hA hB
          exact ⟨rfl, heq_of_eq (congrArg ModuleExpression.fst (eq_of_heq he_heq))⟩
    | _ => simp [ModuleExpression.erasedEqual] at h
  | snd e ihe =>
    cases m' with
    | snd e' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | snd hne' =>
            obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
            obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
            subst hA hB
            exact heq_of_eq (congrArg ModuleExpression.snd (eq_of_heq he_heq))
      · intro hne
        cases hne with
        | snd hne' =>
          obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
          obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
          subst hA hB
          exact ⟨rfl, heq_of_eq (congrArg ModuleExpression.snd (eq_of_heq he_heq))⟩
    | _ => simp [ModuleExpression.erasedEqual] at h
  | abs body ihbody =>
    cases m' with
    | abs body' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn hT
        cases hn with
        | neutral hne => cases hne
        | abs hb =>
          obtain ⟨hA, hB⟩ := ModuleType.arr.inj hT
          subst hA hB
          have hbody' := eq_of_heq ((ihbody body' h).1 hb rfl)
          subst hbody'
          exact HEq.rfl
      · intro hne
        cases hne
    | _ => simp [ModuleExpression.erasedEqual] at h
  | pair a b iha ihb =>
    cases m' with
    | pair a' b' =>
      simp only [ModuleExpression.erasedEqual] at h
      obtain ⟨ha_eq, hb_eq⟩ := h
      constructor
      · intro hn hT
        cases hn with
        | neutral hne => cases hne
        | pair ha hb =>
          obtain ⟨hA, hB⟩ := ModuleType.prod.inj hT
          subst hA hB
          have ha' := eq_of_heq ((iha a' ha_eq).1 ha rfl)
          have hb' := eq_of_heq ((ihb b' hb_eq).1 hb rfl)
          subst ha' hb'
          exact HEq.rfl
      · intro hne
        cases hne
    | _ => simp [ModuleExpression.erasedEqual] at h

theorem ModuleExpression.erasedEqual_normal_eq {Γ : ModuleContext} {T : ModuleType}
    {n1 n2 : ModuleExpression Γ T} (hn1 : Normal n1)
    (h : ModuleExpression.erasedEqual n1 n2) : n1 = n2 :=
  eq_of_heq ((ModuleExpression.erasedEqual_normal_neutral_eq n1 n2 h).1 hn1 rfl)

theorem ModuleExpression.erasedEqual_neutral_eq {Γ : ModuleContext} {T1 T2 : ModuleType}
    {e1 : ModuleExpression Γ T1} {e2 : ModuleExpression Γ T2}
    (hne1 : Neutral e1)
    (h : ModuleExpression.erasedEqual e1 e2) : T1 = T2 ∧ HEq e1 e2 :=
  (ModuleExpression.erasedEqual_normal_neutral_eq e1 e2 h).2 hne1

theorem moduleExpressionToSTLC_injective_normal {Γ : ModuleContext} {T : ModuleType}
    {n1 n2 : ModuleExpression Γ T} (hn1 : Normal n1)
    (h : moduleExpressionToSTLC n1 = moduleExpressionToSTLC n2) : n1 = n2 :=
  ModuleExpression.erasedEqual_normal_eq hn1 (moduleExpressionToSTLC_injective n1 n2 h)

theorem reduce_normal (m : ModuleExpression Δ t) : Normal (reduce m) := by
  apply WellFoundedRelation.wf.induction (C := fun m => Normal (reduce m)) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact h
  · exact ih _ (cbvReductionStep_stlc_compat n h)

theorem confluence {m m1 m2 : ModuleExpression Γ T}
   (h1 : MultiStepReduction m m1) (h2 : MultiStepReduction m m2) :
   reduce m1 = reduce m2 := by
  have star1 : Rewriting.Star Metatheory.STLCext.Step (moduleExpressionToSTLC m)
                                                      (moduleExpressionToSTLC (reduce m1)) :=
    Rewriting.Star.trans (multiStepReduction_to_stlc_star h1)
                         (multiStepReduction_to_stlc_star multiStepReduction_reduce)
  have star2 : Rewriting.Star Metatheory.STLCext.Step (moduleExpressionToSTLC m)
                                                      (moduleExpressionToSTLC (reduce m2)) :=
    Rewriting.Star.trans
      (multiStepReduction_to_stlc_star h2)
      (multiStepReduction_to_stlc_star multiStepReduction_reduce)
  have nf1 : Rewriting.IsNormalForm Metatheory.STLCext.Step (moduleExpressionToSTLC (reduce m1)) :=
    moduleExpressionToSTLC_Normal_iff.mp (reduce_normal m1)
  have nf2 : Rewriting.IsNormalForm Metatheory.STLCext.Step (moduleExpressionToSTLC (reduce m2)) :=
    moduleExpressionToSTLC_Normal_iff.mp (reduce_normal m2)
  exact moduleExpressionToSTLC_injective_normal (reduce_normal m1)
    (Rewriting.normalForm_unique Metatheory.STLCext.step_confluent star1 star2 nf1 nf2)

theorem reduce_normalClosed (m : ModuleExpression .empty t) : NormalClosed (reduce m) :=
  (reduce_normal m).normalClosed

structure Module (T : ModuleType) where
  expression : ModuleExpression .empty T
  normal : NormalClosed expression

def _root_.Language.Modules.ModuleExpression.toProcModule {T : ModuleType}
  (m : ModuleExpression .empty T) : Module T :=
  ⟨reduce m, reduce_normalClosed m⟩

instance : CoeFun (Module (.arr T U)) (fun _ ↦ Module T → Module U) where
  coe f x := ModuleExpression.toProcModule (ModuleExpression.app f.expression x.expression)

@[simp]
theorem reduce_fst (m : ModuleExpression Γ T) (m' : ModuleExpression Γ T') :
  reduce (ModuleExpression.fst (ModuleExpression.pair m m')) = reduce m := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | fst ne' => exact nomatch ne'
  · rfl

@[simp]
theorem reduce_snd (m : ModuleExpression Γ T) (m' : ModuleExpression Γ T') :
  reduce (ModuleExpression.snd (ModuleExpression.pair m m')) = reduce m' := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | snd ne' => exact nomatch ne'
  · rfl

@[simp]
theorem reduce_idempotent (m : ModuleExpression Γ T) :
  reduce (reduce m) = reduce m := by
  conv_lhs => unfold reduce
  simp [reduce_normal m]

theorem multiStepReduction_app
    {m1 m1' : ModuleExpression Γ (.arr T U)} {m2 m2' : ModuleExpression Γ T}
    (h1 : MultiStepReduction m1 m1') (h2 : MultiStepReduction m2 m2') :
    MultiStepReduction (ModuleExpression.app m1 m2) (ModuleExpression.app m1' m2') := by
  have left : MultiStepReduction (ModuleExpression.app m1 m2) (ModuleExpression.app m1' m2) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appL hbc)
  have right : MultiStepReduction (ModuleExpression.app m1' m2) (ModuleExpression.app m1' m2') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appR hbc)
  exact Rewriting.Star.trans left right

theorem reduce_app (m : ModuleExpression Γ (.arr T U)) (m' : ModuleExpression Γ T) :
  reduce (ModuleExpression.app m m') = reduce (ModuleExpression.app (reduce m) (reduce m')) :=
  (reduce_idempotent _).symm.trans
    (confluence multiStepReduction_reduce
      (multiStepReduction_app multiStepReduction_reduce multiStepReduction_reduce))

@[simp]
theorem reduce_beta
  (body : ModuleExpression (Γ.append T) U) (arg : ModuleExpression Γ T) :
  reduce (ModuleExpression.app (ModuleExpression.abs body) arg) = reduce (substitute body arg) := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with
      | app ne' _ => exact nomatch ne'
      | appProcHoles hph _ _ => exact absurd hph (by simp [IsProcHoles])
  · rfl

private theorem multiStepReduction_fst
    {e e' : ModuleExpression Γ (.prod A B)} (h : MultiStepReduction e e') :
    MultiStepReduction (ModuleExpression.fst e) (ModuleExpression.fst e') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (.fst hbc)

-- TODO: How to tell the simplifier to use these theorems?
-- Maybe need to mark them as congruence rule?
-- => Investigate @[gcongr]
-- @[congr]
theorem reduce_fst_cong (m m' : ModuleExpression Γ (.prod T U)) :
    reduce m = reduce m' → reduce (ModuleExpression.fst m) = reduce (ModuleExpression.fst m') := by
  intro h
  have eq1 : reduce (ModuleExpression.fst m) = reduce (ModuleExpression.fst (reduce m)) :=
    (reduce_idempotent _).symm.trans
      (confluence multiStepReduction_reduce (multiStepReduction_fst multiStepReduction_reduce))
  have eq2 : reduce (ModuleExpression.fst m') = reduce (ModuleExpression.fst (reduce m')) :=
    (reduce_idempotent _).symm.trans
      (confluence multiStepReduction_reduce (multiStepReduction_fst multiStepReduction_reduce))
  rw [eq1, eq2, h]

def Module.fst {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toProcModule

def Module.snd {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toProcModule

def Module.pair {T U} (m1 : Module T) (m2 : Module U) : Module (.prod T U) :=
  (m1.expression.pair m2.expression).toProcModule

@[ext]
theorem Module.ext {T} {m1 m2 : Module T} (h : m1.expression = m2.expression) :
  m1 = m2 := by
  obtain ⟨e1, n1⟩ := m1; obtain ⟨e2, n2⟩ := m2
  simp only at h; subst h; rfl

@[simp]
theorem Module.expression_fst {T U} (m : Module (.prod T U)) :
    m.fst.expression = reduce m.expression.fst := rfl

@[simp]
theorem Module.toProcModule_expression {T} (m : ModuleExpression .empty T) :
    (ModuleExpression.toProcModule m).expression = reduce m := rfl

@[simp]
theorem reduce_fst_pair {T U} (m1 : ModuleExpression Γ T) (m2 : ModuleExpression Γ U) :
    reduce (.fst (.pair m1 m2)) = reduce m1 := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | fst ne' => exact nomatch ne'
  · rfl

private theorem multiStepReduction_pair
    {a a' : ModuleExpression Γ A} {b b' : ModuleExpression Γ B}
    (h1 : MultiStepReduction a a') (h2 : MultiStepReduction b b') :
    MultiStepReduction (ModuleExpression.pair a b) (ModuleExpression.pair a' b') := by
  have left : MultiStepReduction (ModuleExpression.pair a b) (ModuleExpression.pair a' b) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairL hbc)
  have right : MultiStepReduction (ModuleExpression.pair a' b) (ModuleExpression.pair a' b') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairR hbc)
  exact Rewriting.Star.trans left right

@[simp]
theorem reduce_pair {T U} (m1 : ModuleExpression Γ T) (m2 : ModuleExpression Γ U) :
    reduce (ModuleExpression.pair m1 m2) = ModuleExpression.pair (reduce m1) (reduce m2) := by
  have h2 : MultiStepReduction (ModuleExpression.pair m1 m2)
            (ModuleExpression.pair (reduce m1) (reduce m2)) :=
    multiStepReduction_pair multiStepReduction_reduce multiStepReduction_reduce
  have key : reduce (ModuleExpression.pair m1 m2) =
             reduce (ModuleExpression.pair (reduce m1) (reduce m2)) :=
    (reduce_idempotent _).symm.trans (confluence multiStepReduction_reduce h2)
  rw [key]; conv_lhs => unfold reduce
  rw [dif_pos (Normal.pair (reduce_normal m1) (reduce_normal m2))]

@[simp]
theorem Module.reduce_expression {T} (m : Module T) : reduce m.expression = m.expression := by
  obtain ⟨expression, normal⟩ := m; simp only
  have hn : Normal expression := by
    induction normal with
    | const => exact .const
    | constHoles => exact .constHoles
    | abs h => exact .abs h
    | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  conv_lhs => unfold reduce
  rw [dif_pos hn]

@[simp]
theorem Module.fst_pair {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair m2).fst = m1 := by
  ext
  simp [Module.fst, Module.pair]


opaque FV : Type
-- Placeholder
axiom fv_proc {sig holes} (proc : ProcedureWithHoles holes sig) : Set FV
axiom fv_proc_instantiate {sig holes} (proc : ProcedureWithHoles holes sig) (args) :
  fv_proc (proc.instantiate args) = fv_proc proc ∪ ⋃ i : HoleIndex holes sig, fv_proc (args i)

def fv' {mctx : ModuleContext} {mty : ModuleType} (mex : ModuleExpression mctx mty) : Set FV :=
  match mex with
    | .proc p => fv_proc p
    | .procHoles n p => fv_proc p
    | .var .zero => {}
    | .var (.succ n) => {}
    | .app a b => fv' a ∪ fv' b
    | .fst a => fv' a
    | .snd a => fv' a
    | .abs body => fv' body
    | .pair a b => fv' a ∪ fv' b

-- Trivially true but not what we want.
-- Unintuitive that modules don't reduce when applying
-- Do we need the operational semantics of the simply typled λ-calculus?
-- I think so, below's the attempt
theorem fv'_app (a : ModuleExpression Γ (ModuleType.arr A B)) (b : ModuleExpression Γ A) :
  fv' (ModuleExpression.app a b) = fv' a ∪ fv' b := rfl

def fv (m : ModuleExpression c t) : Set FV := fv' (reduce m)

private lemma fv'_var_eq {Γ T} (r : ModuleContextIdx Γ T) : fv' (.var r) = {} := by
  cases r <;> rfl

private lemma fv'_rename_eq {Δ U} (m : ModuleExpression Δ U) :
    ∀ {Γ : ModuleContext} (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T),
    fv' (m.rename ρ) = fv' m := by
  induction m with
  | proc | procHoles | var _ => intros; simp [ModuleExpression.rename, fv', fv'_var_eq]
  | app f a ihf iha => intros Γ ρ; simp [ModuleExpression.rename, fv', ihf ρ, iha ρ]
  | fst e ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih ρ]
  | snd e ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih ρ]
  | abs body ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih (liftRenaming ρ)]
  | pair a b iha ihb => intros Γ ρ; simp [ModuleExpression.rename, fv', iha ρ, ihb ρ]

private lemma fv'_substAll_le {S : Set FV} {Δ U} (m : ModuleExpression Δ U) :
    ∀ {Γ : ModuleContext} (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T),
    (∀ {T} (r : ModuleContextIdx Δ T), fv' (σ r) ⊆ S) →
    fv' (substituteSimultaneously σ m) ⊆ fv' m ∪ S := by
  induction m with
  | proc | procHoles => intros; simp [substituteSimultaneously, fv']
  | var r =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv'_var_eq, Set.empty_union]
      exact hσ r
  | app f a ihf iha =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      rintro x (h | h)
      · rcases ihf σ hσ h with h' | h'
        · exact .inl (.inl h')
        · exact .inr h'
      · rcases iha σ hσ h with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'
  | fst e ih => intros Γ σ hσ; simp only [substituteSimultaneously, fv']; exact ih σ hσ
  | snd e ih => intros Γ σ hσ; simp only [substituteSimultaneously, fv']; exact ih σ hσ
  | abs body ih =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      apply ih (liftSubstitution σ)
      intro T r
      cases r with
      | zero => simp [liftSubstitution, fv']
      | succ r' => simp only [liftSubstitution]; rw [fv'_rename_eq]; exact hσ r'
  | pair a b iha ihb =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      rintro x (h | h)
      · rcases iha σ hσ h with h' | h'
        · exact .inl (.inl h')
        · exact .inr h'
      · rcases ihb σ hσ h with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'

private lemma fv'_subst_le
    (body : ModuleExpression (Δ.append u) t) (arg : ModuleExpression Δ u) :
    fv' (substitute body arg) ⊆ fv' body ∪ fv' arg := by
  simp only [substitute]
  apply fv'_substAll_le body (S := fv' arg)
  intro T r
  cases r with
  | zero => simp [variableSubstitution]
  | succ r' => simp only [variableSubstitution, fv'_var_eq]; exact Set.empty_subset _

/-- The union of `fv_proc` over the entries of a procedure tuple. -/
def fvArgs : (sigs : List ProcedureSignature) →
    typeListToProdGeneric Prod PUnit (sigs.map Procedure) → Set FV
  | [],           _          => {}
  | [_],          p          => fv_proc p
  | _ :: s :: ss, (p, rest)  => fv_proc p ∪ fvArgs (s :: ss) rest

lemma fv'_procTupleOfArgs_eq_fvArgs {Δ : ModuleContext} :
    (sigs : List ProcedureSignature) → (hne : sigs ≠ []) →
    (args : typeListToProdGeneric Prod PUnit (sigs.map Procedure)) →
    fv' (procTupleOfArgs (Δ := Δ) sigs hne args) = fvArgs sigs args
  | [], hne, _ => absurd rfl hne
  | [_], _, p => by simp [procTupleOfArgs, fv', fvArgs]
  | _ :: s :: ss, _, (p, rest) => by
      simp only [procTupleOfArgs, fv', fvArgs]
      rw [fv'_procTupleOfArgs_eq_fvArgs (s :: ss) (by simp) rest]

/-- Every procedure looked up from a tuple `args` has its free variables inside the free
    variables of the proc-tuple built from `args`. -/
private lemma fv_proc_holeLookup_subset {Δ : ModuleContext} :
    (holes : HoleSigs) → (hne : holes.toList ≠ []) →
    (args : typeListToProdGeneric Prod PUnit (holes.toList.map Procedure)) →
    ∀ {sig : ProcedureSignature} (i : HoleIndex holes sig),
      fv_proc (holeLookup holes args i)
        ⊆ fv' (procTupleOfArgs (Δ := Δ) holes.toList hne args)
  | .empty, _, _, _, i => nomatch i
  | .append Γ a, hne, args, sig, i => by
      -- `cases i` (zero/succ) + `fv'_procTupleOfArgs_eq_fvArgs` reduces this to a snoc split of
      -- `fvArgs (Γ.toList ++ [a]) args` matching `tupleSnocSplit`.  Remaining obstacle: the
      -- `heq ▸ args` cast (`(l++[a]).map Procedure = l.map Procedure ++ [Procedure a]`) must be
      -- distributed over the tuple in the `_ :: _ :: _` case — the HoleSigs-snoc / List-cons
      -- impedance.
      sorry

theorem fv_reduction_step (m : ModuleExpression c t) (nn : ¬ Normal m) :
  fv' (cbvReductionStep m nn) ⊆ fv' m := by
  apply cbvReductionStep_preservation (R := fun x y => fv' y ⊆ fv' x)
  case pair_left =>
    refine fun m1 m1' m2 h => ?_; simp only [fv']; exact Set.union_subset_union_left _ h
  case pair_right =>
    refine fun m1 m2 m2' h => ?_; simp only [fv']; exact Set.union_subset_union_right _ h
  case app_left =>
    refine fun f f' a h => ?_; simp only [fv']; exact Set.union_subset_union_left _ h
  case app_right =>
    refine fun f a a' h => ?_; simp only [fv']; exact Set.union_subset_union_right _ h
  case app_beta =>
    refine fun body arg => ?_; simp only [fv']; exact fv'_subst_le body arg
  case app_delta =>
    refine fun ne proc args => ?_
    simp only [fv', substituteProcedure, fv_proc_instantiate]
    exact Set.union_subset_union_right _
      (Set.iUnion_subset fun i => fv_proc_holeLookup_subset _ (HoleSigs.toList_ne_nil ne) args i)
  case abs =>
    refine fun m m' h => ?_; simp only [fv']; exact h
  case fst =>
    refine fun e e' h => ?_; simp only [fv']; exact h
  case fst_beta =>
    refine fun a b => ?_; simp only [fv']; exact Set.subset_union_left
  case snd =>
    refine fun e e' h => ?_; simp only [fv']; exact h
  case snd_beta =>
    refine fun a b => ?_; simp only [fv']; exact Set.subset_union_right



theorem fv_reduce (m : ModuleExpression c t) : fv m ⊆ fv' m := by
  unfold fv
  -- Having some packaged induction principle for reduce would be nice.
  apply WellFoundedRelation.wf.induction (C := fun m => fv' (reduce m) ⊆ fv' m) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact Set.Subset.refl _
  · exact (ih _ (cbvReductionStep_stlc_compat n h)).trans (fv_reduction_step n h)

theorem fv_app (a : ModuleExpression Γ (ModuleType.arr A B)) (b : ModuleExpression Γ A) :
    fv (ModuleExpression.app a b) ⊆ fv a ∪ fv b := by
  simp only [fv, ← fv'_app]
  rw [reduce_app]
  exact fv_reduce _



section Demo

axiom sig : ProcedureSignature
def TestModuleType := Module (ModuleType.prod (ModuleType.proc sig) (ModuleType.proc sig))

noncomputable
def TestModuleType.main (m : TestModuleType) : Module (ModuleType.proc sig) := m.fst
noncomputable
def TestModuleType.aux (m : TestModuleType) : Module (ModuleType.proc sig) := m.snd

structure TestModuleTypeStruct where
  main : Module (ModuleType.proc sig)
  aux : Module (ModuleType.proc sig)

noncomputable
def TestModuleTypeStruct.destruct (str : TestModuleTypeStruct) : TestModuleType :=
  str.main.pair str.aux

noncomputable
def TestModuleType.mk (str : TestModuleTypeStruct) : TestModuleType := str.main.pair str.aux

axiom testMain : Module (ModuleType.proc sig)
axiom testAux : Module (ModuleType.proc sig)

noncomputable
def myMod := TestModuleType.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModuleType.main, myMod, TestModuleType.mk]

end Demo

end Language.Modules
