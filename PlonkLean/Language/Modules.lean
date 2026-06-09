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

def _root_.Language.Programs.HoleSigs.toModuleTypeTuple : HoleSigs → ModuleType
| .empty => .unit
| .append holes sig => .prod (.proc sig) holes.toModuleTypeTuple

/-- `ModuleExpression Γ T` is the type of all module expressions that are well-typed in
    module contexts of type `Γ` and have type `T`. -/
inductive ModuleExpression : ModuleContext → ModuleType → Type _ where
  | proc {sig} : Procedure sig → ModuleExpression Δ (.proc sig)
  | procHoles {holes} {sig} : holes.NonEmpty → ProcedureWithHoles holes sig →
        ModuleExpression Δ (.arr holes.toModuleTypeTuple (.proc sig))
  | var  : ModuleContextIdx Δ M → ModuleExpression Δ M
  | app  : ModuleExpression Δ (.arr A B) → ModuleExpression Δ A → ModuleExpression Δ B
  | fst : ModuleExpression Δ (.prod A B) → ModuleExpression Δ A
  | snd : ModuleExpression Δ (.prod A B) → ModuleExpression Δ B
  | abs : ModuleExpression (Δ.append A) B → ModuleExpression Δ (ModuleType.arr A B)
  | pair : ModuleExpression Δ A → ModuleExpression Δ B → ModuleExpression Δ (ModuleType.prod A B)
  | unit : ModuleExpression Δ .unit

/- # Helper functions -/

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
  | .unit | .var _ | .pair _ _ | .fst _ | .snd _ | .app _ _ | .proc _ | .procHoles _ _ =>
       isFalse Bool.false_ne_true

def IsAbs.body {m : ModuleExpression Δ (.arr T U)} (_ : IsAbs m) :
    ModuleExpression (Δ.append T) U :=
  match m with
   | .abs body => body
   | .fst _ | .snd _ | .var _ | .app _ _ => False.elim (by simp [IsAbs] at *)


def IsProcHoles : ModuleExpression Δ T → Prop
| .procHoles _ _ => True
| _ => False

instance : Decidable (IsProcHoles m) :=
  match m with
  | .procHoles _ _ => isTrue trivial
  | .unit | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .proc _ => isFalse not_false

/-- `IsProcTuple m` holds when `m` is a right-nested tuple of hole-free procedures:
    either `.proc _`, or `.pair (.proc _) rest` with `IsProcTuple rest`.  These are exactly
    the ground arguments a procedure-with-holes can be instantiated with (the module-level
    analogue of STLC `BasicTerm`s). -/
def IsProcTuple : ModuleExpression Δ T → Prop
  | .unit => True
  | .pair (.proc _) rest => IsProcTuple rest
  | _ => False

instance instDecidableIsProcTuple (m : ModuleExpression Δ T) : Decidable (IsProcTuple m) :=
  match m with
  | .unit => isTrue trivial
  | .pair a rest =>
      match a with
      | .proc _ =>
          match instDecidableIsProcTuple rest with
          | isTrue h  => isTrue h
          | isFalse h => isFalse h
      | .unit | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .procHoles _ _ =>
          isFalse (by simp [IsProcTuple])
  | .proc _ | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .procHoles _ _ => isFalse not_false


/-- A type that can be the argument type of a procedure-with-holes: a right-nested tuple of
    procedure types. -/
def IsProcArgType : ModuleType → Prop
  | .unit => True
  | .prod (.proc _) rest => IsProcArgType rest
  | _ => False

-- TODO inline?
omit [ProgramSpec] in
lemma isProcArgType_procHolesArgType (holes : HoleSigs) :
    IsProcArgType (holes.toModuleTypeTuple) :=
  holes.rec trivial (fun _ _ ih => ih)

lemma IsProcHoles.isProcArgType {Δ : ModuleContext} {A B : ModuleType}
    {f : ModuleExpression Δ (.arr A B)} (h : IsProcHoles f) : IsProcArgType A := by
  cases f with
  | procHoles _ _ => exact isProcArgType_procHolesArgType _
  | abs _ => exact absurd h (by simp [IsProcHoles])
  | var _ | app _ _ | fst _ | snd _ => exact absurd h (by simp [IsProcHoles])

def IsProcHoles.destruct {m : ModuleExpression Γ T} (h : IsProcHoles m) :
    Σ holes : HoleSigs, Σ sig : ProcedureSignature,
    { proc : ProcedureWithHoles holes sig //
      T = (.arr holes.toModuleTypeTuple (.proc sig))}
:= match m with
| @ModuleExpression.procHoles _ _ holes sigs _ p => ⟨holes, sigs, p, rfl⟩


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
    | unit : Normal .unit

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
  | .unit => ⟨.isTrue .unit, .isFalse fun h => nomatch h⟩
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
              match instDecidableIsProcTuple arg with
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
  | unit : NormalClosed .unit

/-- Progress for the closed fragment, packaged so the two facts share one structural
    recursion on the term: a closed term is never neutral, and a closed `Normal` term of a
    procedure-argument type is a proc-tuple. -/
private lemma closed_progress : {T : ModuleType} → (m : ModuleExpression .empty T) →
    (¬ Neutral m) ∧ (IsProcArgType T → Normal m → IsProcTuple m)
  | _, .unit => ⟨fun hne => (nomatch hne), fun _ _ => trivial⟩
  | _, .proc _ => ⟨fun hne => (nomatch hne), fun ht _ => absurd ht (by simp [IsProcArgType])⟩
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
            | unit => exact absurd ht (by simp [IsProcArgType])
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
  | .unit       => .unit

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
| .unit => .unit
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
  | .unit => .unit
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

/-- Convert a `HoleSigs.Instantiation` into the corresponding module-expression tuple. -/
def _root_.Language.Programs.HoleSigs.Instantiation.toModuleTuple {Δ : ModuleContext} :
    {holes : HoleSigs} → holes.Instantiation → ModuleExpression Δ holes.toModuleTypeTuple
  | .empty,       _    => .unit
  | .append _ _, inst =>
      .pair (.proc (inst .zero))
            (Language.Programs.HoleSigs.Instantiation.toModuleTuple (fun idx => inst (.succ idx)))

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
            (instantiation : holes.Instantiation) :
      ReductionStep
        (.app (.procHoles ne proc) instantiation.toModuleTuple)
        (.proc (proc.instantiate instantiation))

def MultiStepReduction : ModuleExpression Γ T → ModuleExpression Γ T → Prop :=
  Rewriting.Star ReductionStep



/- # Call-by-value reduction step -/

/-- Inverse of `HoleSigs.Instantiation.toModuleTuple`: extract a `Procedure` for each hole index
    from a `ModuleExpression` that is a right-nested tuple of procedures (`IsProcTuple`). -/
-- TODO make non-private + rename
private def procTupleLookup {Δ : ModuleContext} :
    {holes : HoleSigs} → (m : ModuleExpression Δ holes.toModuleTypeTuple) → IsProcTuple m →
    holes.Instantiation
  | .empty, _, _ => fun n => nomatch n
  | .append _ _, m, h => fun n => by
      cases m with
      | pair a rest =>
          cases a with
          | proc p =>
              cases n with
              | zero => exact p
              | succ n' => exact procTupleLookup rest h n'
          | var _ | app _ _ | fst _ | snd _ => simp [IsProcTuple] at h
      | var _ | app _ _ | fst _ | snd _ => simp [IsProcTuple] at h

def cbvReductionStep (m : ModuleExpression Δ t) (nn : ¬ Normal m) :
    ModuleExpression Δ t :=
  match m with
  | @ModuleExpression.app _ _  A B hd arg =>
      if abs : IsAbs hd then
        substitute abs.body arg
      else if h : IsProcHoles hd ∧ IsProcTuple arg then
        let ⟨holes, sigs, proc, tconv⟩ := h.1.destruct
        have a : A = holes.toModuleTypeTuple := by grind
        have b : B = ModuleType.proc sigs := by grind
        let ipt : IsProcTuple (a ▸ arg) := by grind
        let instantiation : holes.Instantiation := procTupleLookup (a ▸ arg) ipt
        let result := ModuleExpression.proc (proc.instantiate instantiation)
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
  | .unit => absurd .unit nn



/- # Mapping to Metatheory.STLCext -/

-- TODO Make basically everything private here

scoped instance instModuleExpressionSTLCspec : Metatheory.STLCext.STLCspec where
  baseTypes := ProcedureSignature
  baseTypeValue := Procedure
  funcData := Σ holes : HoleSigs, Σ sig : ProcedureSignature, ProcedureWithHoles holes sig

def ModuleType.toSTLC : ModuleType → Metatheory.STLCext.Ty
| .prod A B => .prod A.toSTLC B.toSTLC
| .arr A B => .arr A.toSTLC B.toSTLC
| .proc sig => .base sig
| .unit => .unit

private lemma toModuleTypeTuple_isArrowFree (holes : HoleSigs) :
    holes.toModuleTypeTuple.toSTLC.isArrowFree := by
  induction holes with
  | empty => simp [HoleSigs.toModuleTypeTuple, ModuleType.toSTLC, Metatheory.STLCext.Ty.isArrowFree]
  | append _ _ ih =>
      simp [HoleSigs.toModuleTypeTuple, ModuleType.toSTLC, Metatheory.STLCext.Ty.isArrowFree, ih]

open Metatheory.STLCext in
def basicTermHoleLookup : (holes : HoleSigs) →
    BasicTerm (holes.toModuleTypeTuple.toSTLC) →
    holes.Instantiation
  | .empty, _ => fun n => nomatch n
  | .append Γ _, .pair (.value v) rest => fun n =>
      match n with
      | .zero   => v
      | .succ m => basicTermHoleLookup Γ rest m

open Metatheory.STLCext in
noncomputable def _root_.Language.Programs.ProcedureWithHoles.toSTLC {holes sig}
  (proc : ProcedureWithHoles holes sig) : Term :=
    let inputType := holes.toModuleTypeTuple.toSTLC
    let outputType := (ModuleType.proc sig).toSTLC
    let inputArrowFree : inputType.isArrowFree := toModuleTypeTuple_isArrowFree holes
    let outputArrowFree : outputType.isArrowFree := by
      simp [outputType, ModuleType.toSTLC, Metatheory.STLCext.Ty.isArrowFree]
    let substitution : BasicTerm inputType → BasicTerm outputType :=
      fun basicTerm =>
        .value (proc.instantiate (basicTermHoleLookup holes basicTerm))
    .func (t := inputType) (u := outputType)
      (ht := inputArrowFree) (hu := outputArrowFree) ⟨holes, sig, proc⟩ substitution


noncomputable def ModuleExpression.toSTLC :
    ModuleExpression Γ T → Metatheory.STLCext.Term
  | .unit => .unit
  | .proc p => .value p
  | .procHoles _ p => p.toSTLC
  | .var n => .var n.toNat
  | .app M N => .app M.toSTLC N.toSTLC
  | .fst M => .fst M.toSTLC
  | .snd M => .snd M.toSTLC
  | .abs M => .lam M.toSTLC
  | .pair M N => .pair M.toSTLC N.toSTLC

def ModuleContext.toSTLC : ModuleContext → Metatheory.STLCext.Context
| .empty => []
| .append Γ T => T.toSTLC :: Γ.toSTLC

private lemma ModuleExpression.toSTLC_rename_shift (d : Nat)
    {Δ : ModuleContext} {T : ModuleType} (m : ModuleExpression Δ T) :
    ∀ (c : Nat) {Γ : ModuleContext}
      (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T)
      (_ : ∀ {T} (r : ModuleContextIdx Δ T), r.toNat < c → (ρ r).toNat = r.toNat)
      (_ : ∀ {T} (r : ModuleContextIdx Δ T), r.toNat ≥ c → (ρ r).toNat = r.toNat + d),
      ModuleExpression.toSTLC (m.rename ρ) =
      Metatheory.STLCext.Term.shift d c (ModuleExpression.toSTLC m) := by
  induction m with
  | unit => intros; simp [ModuleExpression.rename, ModuleExpression.toSTLC,
                          Metatheory.STLCext.Term.shift]
  | proc p => intros; simp [ModuleExpression.rename, ModuleExpression.toSTLC,
                            Metatheory.STLCext.Term.shift]
  | procHoles ne p =>
    intros
    simp [ModuleExpression.rename, ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC,
          Metatheory.STLCext.Term.shift]
  | var r =>
    intro c Γ ρ hlo hhi
    simp only [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift]
    by_cases h : r.toNat < c
    · simp only [h, ite_true]; congr 1; exact hlo _ h
    · simp only [h, ite_false]; congr 1
      have h' : r.toNat ≥ c := Nat.le_of_not_lt h
      have heq := hhi _ h'; omega
  | app f a ihf iha =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift,
          ihf c ρ hlo hhi, iha c ρ hlo hhi]
  | fst e ih =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC,
          Metatheory.STLCext.Term.shift, ih c ρ hlo hhi]
  | snd e ih =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC,
          Metatheory.STLCext.Term.shift, ih c ρ hlo hhi]
  | pair a b iha ihb =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift,
          iha c ρ hlo hhi, ihb c ρ hlo hhi]
  | abs body ih =>
    intro c Γ ρ hlo hhi
    simp only [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift]
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

lemma ModuleExpression.toSTLC_substAll_level
    (N_stlc : Metatheory.STLCext.Term)
    {Δ' : ModuleContext} {T : ModuleType} (m : ModuleExpression Δ' T) :
    ∀ (k : Nat) {Γ : ModuleContext}
      (σ : ∀ {T}, ModuleContextIdx Δ' T → ModuleExpression Γ T)
      (_ : ∀ {T} (r : ModuleContextIdx Δ' T),
        ModuleExpression.toSTLC (σ r) =
        Metatheory.STLCext.Term.subst k
          (Metatheory.STLCext.Term.shift k 0 N_stlc)
          (Metatheory.STLCext.Term.var r.toNat)),
      ModuleExpression.toSTLC (substituteSimultaneously σ m) =
      Metatheory.STLCext.Term.subst k
        (Metatheory.STLCext.Term.shift k 0 N_stlc)
        (ModuleExpression.toSTLC m) := by
  induction m with
  | unit => intros; simp [substituteSimultaneously, ModuleExpression.toSTLC,
                          Metatheory.STLCext.Term.subst]
  | proc p => intros
              simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst]
  | procHoles ne p =>
    intros
    simp [substituteSimultaneously, ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC,
          Metatheory.STLCext.Term.subst]
  | var r =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, hσ]
  | app f a ihf iha =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst,
          ihf k σ hσ, iha k σ hσ]
  | fst e ih =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | snd e ih =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | pair a b iha ihb =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst,
          iha k σ hσ, ihb k σ hσ]
  | abs body ih =>
    intro k Γ σ hσ
    simp only [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst]
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
      simp only [liftSubstitution, ModuleExpression.toSTLC, ModuleContextIdx.toNat,
                 Metatheory.STLCext.Term.subst]
      simp [show ¬ (0 : Nat) > k + 1 from Nat.not_lt.mpr (Nat.zero_le _)]
    | succ r' =>
      simp only [liftSubstitution, ModuleContextIdx.toNat]
      rw [ModuleExpression.toSTLC_rename_shift 1 (σ r') 0 (fun {_} r => .succ r)
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

lemma ModuleExpression.toSTLC_subst
    {Δ : ModuleContext} {u T : ModuleType}
    (body : ModuleExpression (Δ.append u) T) (arg : ModuleExpression Δ u) :
    ModuleExpression.toSTLC (substitute body arg) =
    Metatheory.STLCext.Term.subst0 (ModuleExpression.toSTLC arg) (ModuleExpression.toSTLC body) := by
  simp only [substitute]
  rw [ModuleExpression.toSTLC_substAll_level (ModuleExpression.toSTLC arg) body 0 (variableSubstitution arg)]
  · simp [Metatheory.STLCext.Term.shift_zero]
  · intro T r
    cases r with
    | zero =>
      simp only [variableSubstitution, ModuleContextIdx.toNat, Metatheory.STLCext.Term.subst]
      simp [Metatheory.STLCext.Term.shift_zero]
    | succ r' =>
      simp only [variableSubstitution, ModuleExpression.toSTLC,
                 ModuleContextIdx.toNat, Metatheory.STLCext.Term.subst]
      simp [show r'.toNat + 1 > 0 from Nat.succ_pos _]

/-- `toModuleTuple inst` erases to a basic STLC term. Defined in term mode so it is
    definitionally transparent (enabling `rfl` in the roundtrip below).
    Note: use `HoleSigs.Instantiation.toModuleTuple inst` explicitly; dot notation fails because
    `HoleSigs.Instantiation` is an `abbrev` that unfolds to a plain function type. -/
private def isBasicType_toModuleTuple {Δ : ModuleContext} :
    {holes : HoleSigs} → (inst : holes.Instantiation) →
    Metatheory.STLCext.Term.isBasicType holes.toModuleTypeTuple.toSTLC
        (HoleSigs.Instantiation.toModuleTuple (Δ := Δ) inst).toSTLC
  | .empty,    _    => trivial
  | .append _ _, inst =>
      -- isBasicType (.base sig) (.value (inst .zero)) reduces to (sig = sig) = rfl, not True
      ⟨rfl, isBasicType_toModuleTuple (fun idx => inst (.succ idx))⟩

/-- Reading the procedures back from the STLC encoding of `toModuleTuple inst` recovers `inst`.
    Term-mode so `isBasicType_toModuleTuple` unfolds and `rfl`/direct recursion closes goals. -/
private def basicTermHoleLookup_toModuleTuple {Δ : ModuleContext} :
    {holes : HoleSigs} → (inst : holes.Instantiation) →
    {sig : ProcedureSignature} → (n : HoleIndex holes sig) →
    basicTermHoleLookup holes
      (Metatheory.STLCext.Term.toBasicTerm _ _ (isBasicType_toModuleTuple (Δ := Δ) inst)) n = inst n
  | .empty,    _,    _, n => nomatch n
  | .append _ _, _, _, .zero   => rfl
  | .append _ _, inst, _, .succ m =>
      basicTermHoleLookup_toModuleTuple (fun idx => inst (.succ idx)) m


-- `funext` cannot introduce the implicit `{sig}` binder in `holes.Instantiation`.
-- Instead prove the needed instantiate equality by induction on the procedure body.
private lemma instantiate_congr {Δ : ModuleContext} {holes : HoleSigs} (args : holes.Instantiation)
    {sig : ProcedureSignature} (proc : ProcedureWithHoles holes sig) :
    proc.instantiate (basicTermHoleLookup holes
      (Metatheory.STLCext.Term.toBasicTerm _ _ (isBasicType_toModuleTuple (Δ := Δ) args)))
    = proc.instantiate args := by
  obtain ⟨body, _⟩ := proc
  simp only [ProcedureWithHoles.instantiate]
  congr 1
  induction body with
  | skip | assign | sample | call' => rfl
  | hole n _ _ =>
      simp only [StmtWithHoles.instantiate, StmtWithHoles.call]
      rw [basicTermHoleLookup_toModuleTuple (Δ := Δ) args n]
  | seq _ _ ih1 ih2 => simp only [StmtWithHoles.instantiate]; rw [ih1, ih2]
  | ifThenElse _ _ _ iht ihe => simp only [StmtWithHoles.instantiate]; rw [iht, ihe]
  | «while» _ _ ihb => simp only [StmtWithHoles.instantiate]; rw [ihb]

theorem reductionStep_stlc_compat (m m' : ModuleExpression Γ T) :
    ReductionStep m m' →
    Metatheory.STLCext.Step (ModuleExpression.toSTLC m) (ModuleExpression.toSTLC m') := by
  intro h
  induction h with
  | beta =>
      simp only [ModuleExpression.toSTLC]
      rw [ModuleExpression.toSTLC_subst]
      exact .beta _ _
  | appL _ ih => simp only [ModuleExpression.toSTLC]; exact .appL ih
  | appR _ ih => simp only [ModuleExpression.toSTLC]; exact .appR ih
  | lam _ ih  => simp only [ModuleExpression.toSTLC]; exact .lam ih
  | pairL _ ih => simp only [ModuleExpression.toSTLC]; exact .pairL ih
  | pairR _ ih => simp only [ModuleExpression.toSTLC]; exact .pairR ih
  | fstPair => simp only [ModuleExpression.toSTLC]; exact .fstPair _ _
  | fst _ ih  => simp only [ModuleExpression.toSTLC]; exact .fst ih
  | sndPair => simp only [ModuleExpression.toSTLC]; exact .sndPair _ _
  | snd _ ih  => simp only [ModuleExpression.toSTLC]; exact .snd ih
  | delta args =>
      rename_i Δ holes sigs ne proc
      simp only [ModuleExpression.toSTLC]
      rw [show Metatheory.STLCext.Term.value (proc.instantiate args)
            = Metatheory.STLCext.BasicTerm.toTerm
                ((fun bt => Metatheory.STLCext.BasicTerm.value
                    (proc.instantiate (basicTermHoleLookup holes bt)))
                  (Metatheory.STLCext.Term.toBasicTerm _
                    (ModuleExpression.toSTLC (HoleSigs.Instantiation.toModuleTuple (Δ := Δ) args))
                    (isBasicType_toModuleTuple (Δ := Δ) args)))
            from by
              simp only [Metatheory.STLCext.BasicTerm.toTerm]
              exact congrArg Metatheory.STLCext.Term.value (instantiate_congr (Δ := Δ) args proc).symm]
      exact Metatheory.STLCext.Step.funcApp _ _ _ _

theorem ModuleExpression.toSTLC_hasType (m : ModuleExpression Γ T) :
  Metatheory.STLCext.HasType (ModuleContext.toSTLC Γ) m.toSTLC T.toSTLC
   := by induction m with
  | proc c =>
    simp only [ModuleExpression.toSTLC, ModuleType.toSTLC]
    exact Metatheory.STLCext.HasType.value c
  | procHoles _ _ =>
    exact Metatheory.STLCext.HasType.func _ _
  | abs M ihM =>
    simp only [ModuleExpression.toSTLC, ModuleType.toSTLC, ModuleContext.toSTLC] at *
    exact Metatheory.STLCext.HasType.lam ihM
  | pair M N ihM ihN =>
    simp only [ModuleExpression.toSTLC, ModuleType.toSTLC]
    exact Metatheory.STLCext.HasType.pair ihM ihN
  | app M N ihM ihN =>
    simp only [ModuleExpression.toSTLC, ModuleType.toSTLC]
    exact Metatheory.STLCext.HasType.app ihM ihN
  | fst M ihM =>
    simp only [ModuleExpression.toSTLC, ModuleType.toSTLC]
    exact Metatheory.STLCext.HasType.fst ihM
  | snd M ihM =>
    simp only [ModuleExpression.toSTLC, ModuleType.toSTLC]
    exact Metatheory.STLCext.HasType.snd ihM
  | unit => exact Metatheory.STLCext.HasType.unit
  | var n =>
    simp only [ModuleExpression.toSTLC, ModuleType.toSTLC]
    apply Metatheory.STLCext.HasType.var
    induction n with
    | zero =>
      simp [ModuleContextIdx.toNat, ModuleContext.toSTLC]
    | succ n ih =>
      simp [ModuleContextIdx.toNat, ModuleContext.toSTLC, ih]



/- # Strong normalization -/

private theorem reduce_acc {Γ : ModuleContext} {T : ModuleType} (m : ModuleExpression Γ T) :
    Acc (fun p q : ModuleExpression Γ T =>
      Metatheory.STLCext.Step (ModuleExpression.toSTLC q) (ModuleExpression.toSTLC p)) m := by
  suffices h : ∀ M : Metatheory.STLCext.Term, Metatheory.STLCext.SN M →
      ∀ (n : ModuleExpression Γ T), ModuleExpression.toSTLC n = M → Acc (fun p q =>
          Metatheory.STLCext.Step (ModuleExpression.toSTLC q) (ModuleExpression.toSTLC p)) n from
    h _ (Metatheory.STLCext.strong_normalization (ModuleExpression.toSTLC_hasType m)) m rfl
  intro M sn
  induction sn with
  | intro _ h_acc ih =>
    intro n heq
    apply Acc.intro
    intro q step
    rw [heq] at step
    exact ih _ step q rfl

scoped instance instWellFoundedRelationModuleExpressionReduction (priority := 1001) {Γ : ModuleContext} {T : ModuleType} :
    WellFoundedRelation (ModuleExpression Γ T) :=
  ⟨fun p q => ReductionStep q p,
   ⟨fun m => by
     have lift : ∀ (n : ModuleExpression Γ T),
         Acc (fun p q =>
               Metatheory.STLCext.Step q.toSTLC p.toSTLC) n →
         Acc (fun p q => ReductionStep q p) n := by
       intro n h
       induction h with
       | intro x _ ih => exact Acc.intro x (fun y step => ih y (reductionStep_stlc_compat x y step))
     exact lift m (reduce_acc m)⟩⟩

/- # Confluence -/

/- # Full reduction -/
