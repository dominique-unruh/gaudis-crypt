import Mathlib.Data.List.AList
import Mathlib.Logic.Equiv.Defs
import PlonkLean.Language.Programs
import Metatheory.STLCext.Normalization
import Metatheory.STLCext.Confluence

namespace Language.Modules

open Language.Programs

variable [ProgramSpec]

/- # Definition of the module calculus -/

/-- Possible types of modules -/
inductive ModuleType where
  | proc : ProcedureSignature → ModuleType
  | prod : ModuleType → ModuleType → ModuleType
  | arr  : ModuleType → ModuleType → ModuleType
  | unit : ModuleType

/-- Module context typing:
    Types of a given module contexts; just a list of module types -/
inductive ModuleContext where
  | empty  : ModuleContext
  | append : ModuleContext → ModuleType → ModuleContext

/-- Pointer into a module context; type safe for a given module context typing -/
inductive ModuleContextIdx : ModuleContext → ModuleType → Type _ where
  | zero {a} {Γ : ModuleContext} : ModuleContextIdx (Γ.append a) a
  | succ {a b} : ModuleContextIdx Γ a → ModuleContextIdx (Γ.append b) a

def ModuleContextIdx.toNat : ModuleContextIdx Γ T → Nat
| .zero => 0
| .succ n => Nat.succ (n.toNat)

def procedureHolesToArgumentType (holes : HoleSigs) : ModuleType :=
  typeListToProdGeneric ModuleType.prod ModuleType.unit
     (holes.toList.map fun sig => ModuleType.proc sig)

/-- `ModuleExpression Γ T` is the type of all module expressions that are well-typed in
    module contexts of type `Γ` and have type `T`. -/
inductive ModuleExpression : ModuleContext → ModuleType → Type _ where
  | proc {sig} : Procedure sig → ModuleExpression Δ (.proc sig)
  | procHoles {holes} {sig} : holes.NonEmpty → ProcedureWithHoles holes sig →
        ModuleExpression Δ (.arr (procedureHolesToArgumentType holes) (.proc sig))
  | var  : ModuleContextIdx Δ M → ModuleExpression Δ M
  | app  : ModuleExpression Δ (.arr A B) → ModuleExpression Δ A → ModuleExpression Δ B
  | fst : ModuleExpression Δ (.prod A B) → ModuleExpression Δ A
  | snd : ModuleExpression Δ (.prod A B) → ModuleExpression Δ B
  | abs : ModuleExpression (Δ.append A) B → ModuleExpression Δ (ModuleType.arr A B)
  | pair : ModuleExpression Δ A → ModuleExpression Δ B → ModuleExpression Δ (ModuleType.prod A B)

/- # Helper functions -/

def IsProcHoles : ModuleExpression Δ T → Prop
| .procHoles _ _ => True
| _ => False

instance : Decidable (IsProcHoles m) :=
  match m with
  | .procHoles _ _ => isTrue trivial
  | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .proc _ => isFalse not_false

/-- `IsProcTuple m` holds when `m` is a right-nested tuple of hole-free procedures:
    either `.proc _`, or `.pair (.proc _) rest` with `IsProcTuple rest`.  These are exactly
    the ground arguments a procedure-with-holes can be instantiated with (the module-level
    analogue of STLC `BasicTerm`s). -/
def IsProcTuple : ModuleExpression Δ T → Prop
  | .proc _ => True
  | .pair (.proc _) rest => IsProcTuple rest
  | _ => False

instance instModuleExpressionDecidable (m : ModuleExpression Δ T) : Decidable (IsProcTuple m) :=
  match m with
  | .proc _ => isTrue trivial
  | .pair a rest =>
      match a with
      | .proc _ =>
          match instModuleExpressionDecidable rest with
          | isTrue h  => isTrue h
          | isFalse h => isFalse h
      | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .procHoles _ _ =>
          isFalse (by simp [IsProcTuple])
  | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .procHoles _ _ => isFalse not_false


/-- A type that can be the argument type of a procedure-with-holes: a right-nested tuple of
    procedure types. -/
def IsProcArgType : ModuleType → Prop
  | .unit => True
  | .proc _ => True
  | .prod (.proc _) rest => IsProcArgType rest
  | _ => False

-- TODO inline?
omit [ProgramSpec] in
lemma isProcArgType_tlpg : (sigs : List ProcedureSignature) →
    IsProcArgType (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc))
  | [] => trivial
  | [_] => trivial
  | _ :: s :: ss => isProcArgType_tlpg (s :: ss)

-- TODO inline?
omit [ProgramSpec] in
lemma isProcArgType_procHolesArgType (holes : HoleSigs) :
    IsProcArgType (procedureHolesToArgumentType holes) :=
  isProcArgType_tlpg holes.toList

lemma IsProcHoles.isProcArgType {Δ : ModuleContext} {A B : ModuleType}
    {f : ModuleExpression Δ (.arr A B)} (h : IsProcHoles f) : IsProcArgType A := by
  cases f with
  | procHoles _ _ => exact isProcArgType_procHolesArgType _
  | abs _ => exact absurd h (by simp [IsProcHoles])
  | var _ | app _ _ | fst _ | snd _ => exact absurd h (by simp [IsProcHoles])

def IsProcHoles.destruct {m : ModuleExpression Γ T} (h : IsProcHoles m) :
    Σ holes : HoleSigs, Σ sig : ProcedureSignature,
    { proc : ProcedureWithHoles holes sig //
      T = (.arr (procedureHolesToArgumentType holes) (.proc sig))}
:= match m with
| @ModuleExpression.procHoles _ _ holes sigs _ p => ⟨holes, sigs, p, rfl⟩

/-- Extract the underlying tuple of hole-free procedures from a `IsProcTuple` argument,
    in the shape expected by `substituteProcedure`.  Total: the `IsProcTuple` proof rules
    out every non-`.proc`/`.pair` shape. -/
-- TODO get rid of this or change type
def IsProcTuple.toArgs
  {sigs : List ProcedureSignature}
  {m : ModuleExpression Δ (typeListToProdGeneric ModuleType.prod ModuleType.unit
                                                 (sigs.map ModuleType.proc))}
  (ipt : IsProcTuple m)
     : typeListToProdGeneric Prod PUnit (sigs.map Procedure) := match sigs, m, ipt with
  | [],           _, _ => PUnit.unit
  | [_],          m, h =>
      match m, h with
      | .proc p,  _ => p
      | .var _,   h => absurd h (by simp [IsProcTuple])
      | .app _ _, h => absurd h (by simp [IsProcTuple])
      | .fst _,   h => absurd h (by simp [IsProcTuple])
      | .snd _,   h => absurd h (by simp [IsProcTuple])
  | _ :: s :: ss, m, h =>
      match m, h with
      | .pair (.proc p) rest, hpt => (p, IsProcTuple.toArgs hpt)
      | .pair (.var _) _,        h => absurd h (by simp [IsProcTuple])
      | .pair (.app _ _) _,      h => absurd h (by simp [IsProcTuple])
      | .pair (.fst _) _,        h => absurd h (by simp [IsProcTuple])
      | .pair (.snd _) _,        h => absurd h (by simp [IsProcTuple])
      | .var _,   h => absurd h (by simp [IsProcTuple])
      | .app _ _, h => absurd h (by simp [IsProcTuple])
      | .fst _,   h => absurd h (by simp [IsProcTuple])
      | .snd _,   h => absurd h (by simp [IsProcTuple])

/- # Normal forms -/

mutual

  /-- Beta-normal form: no beta-redex anywhere in the term. -/
  inductive Normal : ModuleExpression Δ T → Prop where
    | neutral : Neutral e → Normal e
    | abs {body : ModuleExpression (ModuleContext.append Δ A) B} : Normal body → Normal (.abs body)
    | pair {a : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
             Normal a → Normal b → Normal (.pair a b)
    -- TODO rename const -> proc, constHoles -> procHoles
    | const : Normal (.proc p)
    | constHoles {holes sig} {ne : holes.NonEmpty} {p : ProcedureWithHoles holes sig} :
        Normal (.procHoles ne p)

  /-- Neutral form: no outermost redex.  Either the head is a variable, or it is a
      procedure-with-holes applied to a normal argument that is not a proc-tuple (so the
      δ-rule cannot fire) — both are stuck.
      `Neutral f` in `app` rules out `app (abs ..) ..`.
      `Neutral e` in `fst`/`snd` rules out `fst (pair ..)` / `snd (pair ..)`. -/
  inductive Neutral : ModuleExpression Δ T → Prop where
    | var : Neutral (.var r)
    | app {f : ModuleExpression Δ (.arr A B)} {arg : ModuleExpression Δ A} :
        Neutral f → Normal arg → Neutral (.app f arg)
    | appProcHoles {f : ModuleExpression Δ (.arr A B)} {arg : ModuleExpression Δ A} :
        IsProcHoles f → Normal arg → ¬ IsProcTuple arg → Neutral (.app f arg)
    | fst : Neutral e → Neutral (.fst e)
    | snd : Neutral e → Neutral (.snd e)
end

private def decidableNormalNeutral (m : ModuleExpression Δ t) :
    Decidable (Normal m) × Decidable (Neutral m) :=
  match m with
  | .var _  => ⟨.isTrue (.neutral .var), .isTrue .var⟩
  | .proc _ => ⟨.isTrue .const, .isFalse fun h => nomatch h⟩
  | .procHoles _ _ => ⟨.isTrue .constHoles, .isFalse fun h => nomatch h⟩
  | .abs body =>
      match (decidableNormalNeutral body).1 with
      | .isTrue hn   => ⟨.isTrue (.abs hn), .isFalse fun h => nomatch h⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .abs hb => hb | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .pair a b =>
      match (decidableNormalNeutral a).1, (decidableNormalNeutral b).1 with
      | .isTrue ha, .isTrue hb =>
          ⟨.isTrue (.pair ha hb), .isFalse fun h => nomatch h⟩
      | .isFalse ha, _ =>
          ⟨.isFalse fun h => ha (match h with | .pair hp _ => hp | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
      | .isTrue _, .isFalse hb =>
          ⟨.isFalse fun h => hb (match h with | .pair _ hq => hq | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .app f arg => by
      -- An application is Normal iff it is Neutral (applications are never canonical values).
      -- It is Neutral either via `.app` (neutral head) or `.appProcHoles`
      -- (procedure-with-holes applied to a normal, non-proc-tuple argument).
      have df := decidableNormalNeutral f
      have da := decidableNormalNeutral arg
      have dN : Decidable (Neutral (.app f arg)) := by
        match df.2, da.1 with
        | .isTrue nf, .isTrue na => exact .isTrue (.app nf na)
        | _, .isFalse na =>
            exact .isFalse fun h => by
              cases h with
              | app _ na' => exact na na'
              | appProcHoles _ na' _ => exact na na'
        | .isFalse nf, .isTrue na =>
            if hph : IsProcHoles f then
              match instModuleExpressionDecidable arg with
              | .isFalse hpt => exact .isTrue (.appProcHoles hph na hpt)
              | .isTrue hpt =>
                  exact .isFalse fun h => by
                    cases h with
                    | app nf' _ => exact nf nf'
                    | appProcHoles _ _ hpt' => exact hpt' hpt
            else
              exact .isFalse fun h => by
                cases h with
                | app nf' _ => exact nf nf'
                | appProcHoles hph' _ _ => exact hph hph'
      exact ⟨(match dN with
              | .isTrue h => .isTrue (.neutral h)
              | .isFalse h => .isFalse fun hn => by cases hn with | neutral hne => exact h hne), dN⟩
  | .fst e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.fst hn)), .isTrue (.fst hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.fst he) => he),
           .isFalse fun h => hnn (match h with | .fst he => he)⟩
  | .snd e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.snd hn)), .isTrue (.snd hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.snd he) => he),
           .isFalse fun h => hnn (match h with | .snd he => he)⟩

instance (m : ModuleExpression Γ A) : Decidable (Normal m) := (decidableNormalNeutral m).1
instance (m : ModuleExpression Γ A) : Decidable (Neutral m) := (decidableNormalNeutral m).2

/-- Beta-normal form for closed terms (empty context).
    Neutral terms cannot occur (they would require a variable in the empty context),
    so this has fewer cases than `Normal`. The `abs` body is in a one-variable context
    and therefore still uses the general `Normal`. -/
inductive NormalClosed : ModuleExpression .empty T → Prop where
  | const : NormalClosed (.proc p)
  | constHoles : NormalClosed (.procHoles n p)
  | abs {body : ModuleExpression (ModuleContext.append .empty A) B} :
                Normal body → NormalClosed (.abs body)
  | pair {a : ModuleExpression .empty A} {b : ModuleExpression .empty B} :
      NormalClosed a → NormalClosed b → NormalClosed (.pair a b)

/-- Progress for the closed fragment, packaged so the two facts share one structural
    recursion on the term: a closed term is never neutral, and a closed `Normal` term of a
    procedure-argument type is a proc-tuple. -/
private lemma closed_progress : {T : ModuleType} → (m : ModuleExpression .empty T) →
    (¬ Neutral m) ∧ (IsProcArgType T → Normal m → IsProcTuple m)
  | _, .proc _ => ⟨fun hne => (nomatch hne), fun _ _ => trivial⟩
  | _, .procHoles _ _ => ⟨fun hne => (nomatch hne), fun ht _ => ht.elim⟩
  | _, .var r => nomatch r
  | _, .app f arg =>
      have ihf := closed_progress f
      have iharg := closed_progress arg
      have h1 : ¬ Neutral (.app f arg) := by
        intro hne
        cases hne with
        | app nf _ => exact ihf.1 nf
        | appProcHoles hph ha hpt => exact hpt (iharg.2 hph.isProcArgType ha)
      ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | _, .fst e =>
      have ih := closed_progress e
      have h1 : ¬ Neutral (.fst e) := by intro hne; cases hne with | fst ne => exact ih.1 ne
      ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | _, .snd e =>
      have ih := closed_progress e
      have h1 : ¬ Neutral (.snd e) := by intro hne; cases hne with | snd ne => exact ih.1 ne
      ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | _, .abs _ => ⟨fun hne => (nomatch hne), fun ht _ => ht.elim⟩
  | _, .pair a b =>
      have iha := closed_progress a
      have ihb := closed_progress b
      ⟨fun hne => (nomatch hne), fun ht hn => by
        cases hn with
        | neutral hne => exact nomatch hne
        | pair ha hb =>
            cases a with
            | proc p => exact ihb.2 ht hb
            | var r => exact nomatch r
            | app _ _ => cases ha with | neutral hne => exact absurd hne iha.1
            | fst _ => cases ha with | neutral hne => exact absurd hne iha.1
            | snd _ => cases ha with | neutral hne => exact absurd hne iha.1
            | abs _ => exact ht.elim
            | procHoles _ _ => exact ht.elim
            | pair _ _ => exact ht.elim⟩

lemma empty_context_not_neutral {T : ModuleType} {m : ModuleExpression .empty T} : ¬ Neutral m :=
  (closed_progress m).1

lemma Normal.normalClosed {T : ModuleType} {m : ModuleExpression .empty T} :
    Normal m → NormalClosed m
  | .neutral h  => absurd h empty_context_not_neutral
  | .const      => .const
  | .constHoles => .constHoles
  | .abs hb     => .abs hb
  | .pair ha hb => .pair ha.normalClosed hb.normalClosed

/- # Reduction step -/


/-- Extends a renaming `ρ : ModuleContextIdx Δ → ModuleContextIdx Γ` to work under one
    binder of type `A`.
    The bound variable `.zero` maps to itself; outer variables `.succ r` are renamed by `ρ`
    and re-wrapped with `.succ`.  This is the typed analogue of incrementing the cutoff `c`
    in Pierce's shift operation. -/
def liftRenaming {Δ Γ : ModuleContext} {A : ModuleType}
    (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T) {T} :
    ModuleContextIdx (ModuleContext.append Δ A) T → ModuleContextIdx (ModuleContext.append Γ A) T
  | .zero   => .zero
  | .succ r => .succ (ρ r)

/-- Applies a renaming `ρ : ModuleContextIdx Δ → ModuleContextIdx Γ` to every variable in a term,
    producing a term over context `Γ`.
    Goes under binders by lifting `ρ` with `liftRename`.
    This is the typed analogue of Pierce's shift `↑_c^d`, where `ρ` encodes both the
    cutoff `c` and the displacement `d`. -/
def ModuleExpression.rename
    (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T) :
  ModuleExpression Δ T → ModuleExpression Γ T
| .proc p  => .proc p
| .procHoles ne p => .procHoles ne p
| .var r    => .var (ρ r)
| .app f a  => .app (f.rename ρ) (a.rename ρ)
| .fst e    => .fst (e.rename ρ)
| .snd e    => .snd (e.rename ρ)
| .abs body => .abs (body.rename (liftRenaming ρ))
| .pair a b => .pair (a.rename ρ) (b.rename ρ)

/-- Extends a simultaneous substitution `σ : ModuleContextIdx Δ → ModuleExpression Γ`
    to work under one binder of type `A`,
    yielding a substitution `ModuleContextIdx (Δ,A) → ModuleExpression (Γ,A)`.
    The bound variable `.zero` maps to the fresh variable `.var .zero`;
    outer variables `.succ r` are substituted by `σ r` and then weakened into the
    extended context `Γ,A` by renaming with `.succ`. -/
def liftSubstitution {Δ Γ : ModuleContext} {A : ModuleType}
    (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T) {T} :
    ModuleContextIdx (ModuleContext.append Δ A) T → ModuleExpression (ModuleContext.append Γ A) T
  | .zero   => .var .zero
  | .succ r => (σ r).rename (fun {_} r => .succ r)

/-- Applies a simultaneous substitution `σ : ModuleContextIdx Δ → ModuleExpression Γ`
    to every variable in a term, producing a term over context `Γ`.
    Goes under binders by lifting `σ` with `liftSubst`. -/
def substituteSimultaneously (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T) :
   ModuleExpression Δ T → ModuleExpression Γ T
  | .proc p  => .proc p
  | .procHoles ne p => .procHoles ne p
  | .var r    => σ r
  | .app f a  => .app (substituteSimultaneously σ f) (substituteSimultaneously σ a)
  | .fst e    => .fst (substituteSimultaneously σ e)
  | .snd e    => .snd (substituteSimultaneously σ e)
  | .abs body => .abs (substituteSimultaneously (liftSubstitution σ) body)
  | .pair a b => .pair (substituteSimultaneously σ a) (substituteSimultaneously σ b)

/-- The single-variable substitution map used as the `σ` argument to `substSimultaneous`:
    de Bruijn index 0 (the outermost bound variable) maps to `arg`;
    any other index `k+1` maps back to the variable at index `k`. -/
def variableSubstitution {Δ : ModuleContext} {u : ModuleType} (arg : ModuleExpression Δ u) {T} :
    ModuleContextIdx (ModuleContext.append Δ u) T → ModuleExpression Δ T
  | .zero   => arg
  | .succ r => .var r

/-- Single-variable de Bruijn substitution: replaces de Bruijn index 0 in `body` with `arg`.
    Implemented via `substSimultaneous` with the point substitution `substVar arg`. -/
def substitute (body : ModuleExpression (Δ.append u) t) (arg : ModuleExpression Δ u) :
  ModuleExpression Δ t :=
  substituteSimultaneously (variableSubstitution arg) body

/- # Mapping to Metatheory.STLCext -/

scoped instance instModuleExpressionSTLCspec : Metatheory.STLCext.STLCspec where
  baseTypes := ProcedureSignature
  baseTypeValue := Procedure
  funcData := Σ holes : HoleSigs, Σ sig : ProcedureSignature, ProcedureWithHoles holes sig

def moduleTypeToSTLC : ModuleType → Metatheory.STLCext.Ty
| .prod A B => .prod (moduleTypeToSTLC A) (moduleTypeToSTLC B)
| .arr A B => .arr (moduleTypeToSTLC A) (moduleTypeToSTLC B)
| .proc sig => .base sig
| .unit => .unit

/- # Strong normalization -/

/- # Confluence -/

/- # Full reduction -/
