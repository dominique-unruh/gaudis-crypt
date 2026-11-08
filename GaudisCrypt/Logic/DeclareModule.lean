import GaudisCrypt.Logic.Representation
import GaudisCrypt.Logic.FootprintSolver
import GaudisCrypt.Logic.GlobMono
import GaudisCrypt.Syntax.CloneRegistry

/-!
# EasyCrypt's `declare module`

    declare module A <: AdvPreimage «from» «to» {-RO, -Preimage}

declares an abstract module `A` of a module type for the rest of the section, with EasyCrypt's
restriction: `A` touches none of the globals of `RO` and `Preimage`.  It is

    variable (A : AdvPreimage «from» «to») [Module.Declared A S]

with `S` the join of those globals' footprints.  `Module.Declared A S` bundles the two facts EC
takes for granted about a declared module: finitely many globals, and none of them in `S`.  As
an instance-implicit section variable it is part of exactly the lemmas that mention `A` — EC's
generalization over `A` when the section is closed — and `fp_disjoint` reads it like the
restriction hypothesis `FVP.fvP A ≤ Sᶜ` it states.

**The restriction.**  Each `-X` names a module or a global variable:
* a concrete module (a definition): its globals are the `global_var`s its code mentions, through
  the modules it uses (EC's `glob X` of a concrete module is read off its code the same way);
* a global variable: itself;
* a declared module (a section variable): `glob X`, EC's restriction against an abstract module.

**Representability** (exception E2 of the SHA-3 port) is not a hypothesis: over a first-order
module type it is a theorem (`Module.representable_of_firstOrder`), and
`Module.Declared.ecModule A ext` gives `Module.ECModule A ext` with its side conditions
discharged by default (`ext` the module type's canonical one, as `Oracle.ext` is).
-/

namespace GaudisCrypt

open Lean

/-- `A` is an EasyCrypt declared module restricted against `S`: finitely many globals (EC's
`glob A` is a set of variables), none of them in `S`. -/
class Module.Declared {M : Type 1} [IsModule M] (A : M)
    (S : Footprint VariableAssignment) :
    Prop where
  finite : (FVP.fvP A).FinitelySupported
  restr : FVP.fvP A ≤ Sᶜ

/-- `S` is a sub-join of `S₀`: every joinand of `S` is one of `S₀` (or `⊥`), found by instance
search on the two joins.  What lets a module declared against `S₀` be used where a lemma
declares it against less (`Module.Declared.weaken`): a lemma of a theory, used in a clone whose
declaration restricts more (EC's `exact (RO_is_collision_resistant A &m)`). -/
class Footprint.JoinLe (S S₀ : Footprint VariableAssignment) : Prop where
  le : S ≤ S₀

instance (priority := high) Footprint.JoinLe.refl (S : Footprint VariableAssignment) :
    Footprint.JoinLe S S := ⟨le_rfl⟩

instance Footprint.JoinLe.bot (S : Footprint VariableAssignment) : Footprint.JoinLe ⊥ S :=
  ⟨bot_le⟩

instance Footprint.JoinLe.sup {a b S : Footprint VariableAssignment} [ha : Footprint.JoinLe a S]
    [hb : Footprint.JoinLe b S] : Footprint.JoinLe (a ⊔ b) S := ⟨sup_le ha.le hb.le⟩

instance (priority := low) Footprint.JoinLe.left {x l r : Footprint VariableAssignment}
    [h : Footprint.JoinLe x l] : Footprint.JoinLe x (l ⊔ r) := ⟨h.le.trans le_sup_left⟩

instance (priority := low) Footprint.JoinLe.right {x l r : Footprint VariableAssignment}
    [h : Footprint.JoinLe x r] : Footprint.JoinLe x (l ⊔ r) := ⟨h.le.trans le_sup_right⟩

set_option synthInstance.checkSynthOrder false in
/-- A module declared against `S₀` is declared against any sub-join `S` of it.  The declaration
is found first, its `S₀` unknown (a local hypothesis: `declare module`'s, an introduced binder's),
then `S` checked against it: the synthesis order the check would not accept. -/
instance (priority := low) Module.Declared.weaken {M : Type 1} [IsModule M] {A : M}
    {S₀ S : Footprint VariableAssignment} [h : Module.Declared A S₀] [hS : Footprint.JoinLe S S₀] :
    Module.Declared A S :=
  ⟨h.finite, h.restr.trans (Footprint.compl_antimono hS.le)⟩

/-! ### Concrete modules: their `glob` read off their code

EC checks a restriction against a concrete module from its code (`glob Perm` is `Perm.m`,
`Perm.mi`).  Here a concrete module carries `Module.GlobBound A B`: its footprint within a join
`B` of `global_var`s (proven once, by `fp_module`, next to the module).  Instance search then
derives `Module.Declared` for it, and for a declared module against the `glob` of a concrete
one, as EC does:

* `Footprint.Outside B S` — `B ≤ Sᶜ` over the joins: `global_var`s by their `Lens.Disjoint`
  instances, the `glob` of a declared module (its restriction), of a concrete one (its bound);
* `Module.Declared.ofGlobBound` — a concrete module is declared against what its bound stays
  outside;
* `Footprint.Covers S₀ S` — what stays outside `S₀` (finitely supported) stays outside `S`: the
  joinands of `S₀`, and the `glob` of a concrete module whose bound is within `S₀`
  (`Module.Declared.weakenCovers`, `weaken` extended). -/

/-- A concrete module's footprint lies within `B`, a join of `global_var`s (`fp_module`): what
EC reads off the module's code.  Not an EC notion. -/
class Module.GlobBound {M : Type 1} [IsModule M] (A : M)
    (B : outParam (Footprint VariableAssignment)) : Prop where
  le : FVP.fvP A ≤ B
  finite : (FVP.fvP A).FinitelySupported

/-- `B` is a join of `global_var`s: finitely supported, and outside a finitely supported `F`,
outside `glob F`. -/
class Footprint.GlobalJoin (B : Footprint VariableAssignment) : Prop where
  finite : B.FinitelySupported
  le_compl_glob : ∀ F : Footprint VariableAssignment, F.FinitelySupported → F ≤ Bᶜ →
    B ≤ F.globᶜ

instance Footprint.GlobalJoin.var {T : Type} (x : Lens T VariableAssignment) {v : VariableName}
    [Lens.IsGlobalVar x v] : Footprint.GlobalJoin x.footprint :=
  ⟨Footprint.FinitelySupported.globalVar x, fun _ hF h => Footprint.globalVar_le_compl_glob hF x h⟩

instance Footprint.GlobalJoin.sup {a b : Footprint VariableAssignment} [ha : Footprint.GlobalJoin a]
    [hb : Footprint.GlobalJoin b] : Footprint.GlobalJoin (a ⊔ b) :=
  ⟨ha.finite.sup hb.finite, fun F hF h => sup_le
    (ha.le_compl_glob F hF (h.trans (Footprint.compl_antimono le_sup_left)))
    (hb.le_compl_glob F hF (h.trans (Footprint.compl_antimono le_sup_right)))⟩

/-- `B ≤ Sᶜ`, by instance search over the two joins. -/
class Footprint.Outside (B S : Footprint VariableAssignment) : Prop where
  le : B ≤ Sᶜ

instance Footprint.Outside.sup_left {a b S : Footprint VariableAssignment}
    [ha : Footprint.Outside a S] [hb : Footprint.Outside b S] : Footprint.Outside (a ⊔ b) S :=
  ⟨sup_le ha.le hb.le⟩

instance Footprint.Outside.sup_right {B a b : Footprint VariableAssignment}
    [ha : Footprint.Outside B a] [hb : Footprint.Outside B b] : Footprint.Outside B (a ⊔ b) :=
  ⟨(Footprint.le_compl_comm _ _).mpr (sup_le ((Footprint.le_compl_comm _ _).mp ha.le)
    ((Footprint.le_compl_comm _ _).mp hb.le))⟩

/-- Two `global_var`s: their `Lens.Disjoint` instance. -/
instance Footprint.Outside.var {T U : Type} (x : Lens T VariableAssignment)
    (y : Lens U VariableAssignment) [Lens.Disjoint x y] :
    Footprint.Outside x.footprint y.footprint :=
  ⟨Lens.footprint_le_compl_of_disjoint x y⟩

set_option synthInstance.checkSynthOrder false in
/-- The `glob` of a declared module `N`: its restriction keeps it outside `B`. -/
instance (priority := low) Footprint.Outside.glob_declared {M : Type 1} [IsModule M] {N : M}
    {B S₀ : Footprint VariableAssignment} [h : Module.Declared N S₀] [hB : Footprint.GlobalJoin B]
    [hS : Footprint.JoinLe B S₀] : Footprint.Outside B (FVP.fvP N).glob :=
  ⟨hB.le_compl_glob _ h.finite (h.restr.trans (Footprint.compl_antimono hS.le))⟩

set_option synthInstance.checkSynthOrder false in
/-- The `glob` of a declared module `N` on the left: its restriction keeps the `global_var`s `S`
outside it. -/
instance (priority := low) Footprint.Outside.glob_declared_left {M : Type 1} [IsModule M] {N : M}
    {S S₀ : Footprint VariableAssignment} [h : Module.Declared N S₀] [hS : Footprint.GlobalJoin S]
    [hJ : Footprint.JoinLe S S₀] : Footprint.Outside (FVP.fvP N).glob S :=
  ⟨(Footprint.le_compl_comm _ _).mp
    (hS.le_compl_glob _ h.finite (h.restr.trans (Footprint.compl_antimono hJ.le)))⟩

/-- The `glob` of a concrete module `N`, its bound `B'` outside `B`. -/
instance Footprint.Outside.glob_concrete {M : Type 1} [IsModule M] {N : M}
    {B B' : Footprint VariableAssignment} [h : Module.GlobBound N B'] [hB : Footprint.GlobalJoin B]
    [hO : Footprint.Outside B' B] : Footprint.Outside B (FVP.fvP N).glob :=
  ⟨hB.le_compl_glob _ h.finite (h.le.trans hO.le)⟩

/-- **A concrete module is declared** against what its bound stays outside (EC's check of a
restriction from the module's code). -/
instance Module.Declared.ofGlobBound {M : Type 1} [IsModule M] {A : M}
    {B S : Footprint VariableAssignment} [h : Module.GlobBound A B] [hO : Footprint.Outside B S] :
    Module.Declared A S :=
  ⟨h.finite, h.le.trans hO.le⟩

/-- **A concrete functor applied to a declared module** is declared where both stay outside
(EC's restriction of `F(A)` from `F`'s code and `A`'s declaration). -/
instance Module.Declared.app {A B : Type 1} [IsModule A] [IsModule B] {F : Module.Arr A B} {X : A}
    {BF S : Footprint VariableAssignment} [hF : Module.GlobBound F BF] [hX : Module.Declared X S]
    [hO : Footprint.Outside BF S] : Module.Declared (Module.app F X) S :=
  ⟨(hF.finite.sup hX.finite).mono (FVP.fvP_app F X),
    (FVP.fvP_app F X).trans (sup_le (hF.le.trans hO.le) hX.restr)⟩

/-- **EC's syntactic `glob A`**: `R`, a region containing `A`'s footprint, within the `glob` of a
finitely supported footprint (a declared module's `glob`, joined with `global_var`s).  Given once
for a local module built from declared ones (EC's `glob D'` is `glob D` and the variables of
`D'`'s code), where `glob (fvP A)` would not do: `fvP` of an application is only bounded
above. -/
class Module.ECGlob {M : Type 1} [IsModule M] (A : M)
    (R : outParam (Footprint VariableAssignment)) : Prop where
  finite : (FVP.fvP A).FinitelySupported
  le : FVP.fvP A ≤ R
  base : ∃ GF : Footprint VariableAssignment, GF.FinitelySupported ∧ R ≤ GF.glob

set_option synthInstance.checkSynthOrder false in
/-- A declared module's EC `glob` is its `glob`. -/
instance (priority := low) Module.ECGlob.declared {M : Type 1} [IsModule M] {A : M}
    {S : Footprint VariableAssignment} [h : Module.Declared A S] :
    Module.ECGlob A (FVP.fvP A).glob :=
  ⟨h.finite, Footprint.le_glob _, ⟨_, h.finite, le_rfl⟩⟩

/-- A module is declared against what its EC `glob` stays outside (EC's restriction of a local
module, `{-PRPi}` on `D'`). -/
instance (priority := low) Module.Declared.ofECGlob {M : Type 1} [IsModule M] {A : M}
    {R S : Footprint VariableAssignment} [h : Module.ECGlob A R] [hO : Footprint.Outside R S] :
    Module.Declared A S :=
  ⟨h.finite, h.le.trans hO.le⟩

/-- What stays outside `S₀` (a finitely supported footprint) stays outside `S`. -/
class Footprint.Covers (S₀ S : Footprint VariableAssignment) : Prop where
  le : ∀ F : Footprint VariableAssignment, F.FinitelySupported → F ≤ S₀ᶜ → F ≤ Sᶜ

instance (priority := low) Footprint.Covers.of_joinLe {S₀ S : Footprint VariableAssignment}
    [h : Footprint.JoinLe S S₀] : Footprint.Covers S₀ S :=
  ⟨fun _ _ hF => hF.trans (Footprint.compl_antimono h.le)⟩

instance Footprint.Covers.sup {S₀ a b : Footprint VariableAssignment} [ha : Footprint.Covers S₀ a]
    [hb : Footprint.Covers S₀ b] : Footprint.Covers S₀ (a ⊔ b) :=
  ⟨fun F hfs hF => (Footprint.le_compl_comm _ _).mpr (sup_le
    ((Footprint.le_compl_comm _ _).mp (ha.le F hfs hF))
    ((Footprint.le_compl_comm _ _).mp (hb.le F hfs hF)))⟩

/-- The `glob` of a concrete module whose bound lies within `S₀` (EC: a module restricted
against `Perm.m`, `Perm.mi` is restricted against `glob Perm`). -/
instance Footprint.Covers.glob_concrete {M : Type 1} [IsModule M] {N : M}
    {S₀ B : Footprint VariableAssignment} [h : Module.GlobBound N B] [hB : Footprint.GlobalJoin B]
    [hS : Footprint.JoinLe B S₀] : Footprint.Covers S₀ (FVP.fvP N).glob :=
  ⟨fun F hfs hF => Footprint.le_compl_glob_symm h.finite
    (h.le.trans (hB.le_compl_glob F hfs (hF.trans (Footprint.compl_antimono hS.le))))⟩

set_option synthInstance.checkSynthOrder false in
/-- `Module.Declared.weaken`, to what a declaration's set `Covers`: also the `glob` of the
concrete modules within it. -/
instance (priority := low) Module.Declared.weakenCovers {M : Type 1} [IsModule M] {A : M}
    {S₀ S : Footprint VariableAssignment} [h : Module.Declared A S₀] [hS : Footprint.Covers S₀ S] :
    Module.Declared A S :=
  ⟨h.finite, hS.le _ h.finite h.restr⟩

/-- Every procedure signature of `holes` has nonempty parameter and result types. -/
def HoleSigs.AllNonempty : HoleSigs → Prop
  | .empty => True
  | .cons s h => ((∀ U ∈ s.params, Nonempty U) ∧ Nonempty s.ret) ∧ h.AllNonempty

theorem HoleSigs.AllNonempty.index {holes : HoleSigs} (h : holes.AllNonempty) :
    ∀ {sig : ProcedureSignature}, HoleIndex holes sig →
      (∀ U ∈ sig.params, Nonempty U) ∧ Nonempty sig.ret
  | _, .zero => h.1
  | _, .succ n => HoleSigs.AllNonempty.index h.2 n

theorem ModuleTypeRep.FirstOrder.proc' (s : ProcedureSignature) :
    (ModuleTypeRep.proc s).FirstOrder := trivial

theorem ModuleTypeRep.FirstOrder.unit' : ModuleTypeRep.unit.FirstOrder := trivial

theorem ModuleTypeRep.FirstOrder.prod' {a b : ModuleTypeRep} (ha : a.FirstOrder)
    (hb : b.FirstOrder) : (ModuleTypeRep.prod a b).FirstOrder := ⟨ha, hb⟩

theorem HoleSigs.AllNonempty.nil : HoleSigs.empty.AllNonempty := trivial

theorem HoleSigs.AllNonempty.cons {s : ProcedureSignature} {h : HoleSigs}
    (hp : ∀ U ∈ s.params, Nonempty U) (hr : Nonempty s.ret) (hh : h.AllNonempty) :
    (HoleSigs.cons s h).AllNonempty := ⟨⟨hp, hr⟩, hh⟩

/-- Discharge `(Module.moduleTypeRep T).FirstOrder` for a literal module type: the constructor
lemmas, unification unfolding the type down to its representation. -/
macro "module_first_order" : tactic =>
  `(tactic| repeat' (first
    | exact ModuleTypeRep.FirstOrder.proc' _
    | exact ModuleTypeRep.FirstOrder.unit'
    | refine ModuleTypeRep.FirstOrder.prod' ?_ ?_))

/-- Discharge `HoleSigs.AllNonempty holes` for literal signatures: one goal per parameter and
result type, by instance search. -/
macro "holes_nonempty" : tactic =>
  `(tactic| (repeat' (first
      | exact HoleSigs.AllNonempty.nil
      | refine HoleSigs.AllNonempty.cons ?_ ?_ ?_)) <;>
    (try simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff,
      forall_const, and_true]) <;>
    (try and_intros) <;> infer_instance)

/-- **A declared module is EasyCrypt-like** (`Module.ECModule`): its finite support is part of
the declaration, and over a first-order module type its representability is a theorem
(`Module.representable_of_firstOrder`).  The side conditions are discharged by default for a
module type declared by `moduletype` and its canonical `ext` (each procedure in order). -/
theorem Module.Declared.ecModule {T : Type 1} [IsModule T] {sig : ProcedureSignature}
    (A : Module.Arr T (Module.Proc sig)) [h : Module.Declared A ⊥]
    (ext : T → ((Module.moduleTypeRep T).holesApp .empty).Instantiation)
    (hT : (Module.moduleTypeRep T).FirstOrder := by module_first_order)
    (hne : ((Module.moduleTypeRep T).holesApp .empty).AllNonempty := by holes_nonempty)
    (hext : ∀ O, ext O = (Module.moduleTypeRep T).extOf (Module.cast T O) := by
      intro _; rfl) :
    Module.ECModule A ext :=
  ⟨Module.representable_of_firstOrder hT (fun n => hne.index n) ext hext A, h.finite⟩

/-- The restriction as a hypothesis. -/
theorem Module.Declared.le_compl {M : Type 1} [IsModule M] (A : M)
    {S : Footprint VariableAssignment} [h : Module.Declared A S] : FVP.fvP A ≤ Sᶜ :=
  h.restr

/-- A global variable's footprint is finitely supported (one variable): what `Module.Declared`'s
finite support combines with for the modules built from declared ones and the theory's variables. -/
theorem Lens.IsGlobalVar.footprint_finitelySupported {T : Type} (x : Lens T VariableAssignment)
    {v : VariableName} [h : Lens.IsGlobalVar x v] : x.footprint.FinitelySupported := by
  obtain ⟨hT, hx⟩ := h
  cases v
  subst hT
  cases eq_of_heq hx
  exact Footprint.FinitelySupported.varLens _

namespace DeclareModule

open Meta

/-- `c` is a `global_var` or a `module_var`: its value is `varLens …` under the binders of its
implicit arguments (and `module_var`'s `have`s). -/
def isGlobalVar (env : Environment) (c : Name) : Bool := Id.run do
  let some ci := env.find? c | return false
  let some v := ci.value? | return false
  -- under the binders of the implicit arguments and the `have`s of `module_var`
  let rec body : Lean.Expr → Lean.Expr
    | .lam _ _ b _ => body b
    | .letE _ _ _ b _ => body b
    | e@(.app (.app (.app (.app (.const ``letFun _) _) _) _) f) =>
      match f with
      | .lam _ _ b _ => body b
      | _ => e
    | e => e
  return (body v).isAppOf ``varLens

/-- Whether to look into the definition `c` for globals: ours (this file, the examples, the
libraries), not the framework's or mathlib's. -/
def inScope (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`GaudisCrypt.Examples).isPrefixOf m || (`GaudisCrypt.Lib).isPrefixOf m

/-- The `global_var`s the code of the definitions `roots` mentions, through the definitions it
uses (EC's `glob` of a concrete module), in the order first met.  Under an alias of a clone
(`Syntax/Clone.lean`), a variable of the clone's theory is the clone's (`SRO.RO.m` for
`SecureRO.RO.m`), nested clones innermost first: the name that elaborates where the clone is used
(the theory's own would need the theory's instance, which a clone does not register). -/
def globalVarsOf (env : Environment) (roots : Array Name) (cap : Nat := 20000) : Array Name :=
  Id.run do
    let mut out : Array Name := #[]
    let mut seen : Std.HashSet (Name × List (Name × Name)) := {}
    let mut todo : List (Name × List (Name × Name)) := roots.toList.map (·, [])
    let mut n := 0
    while n < cap do
      match todo with
      | [] => break
      | (c, ctx) :: rest =>
        todo := rest
        n := n + 1
        if seen.contains (c, ctx) then continue
        seen := seen.insert (c, ctx)
        if isGlobalVar env c then
          let v := ctx.foldl (fun v (C, T) => (cloneRename? env C T v).getD v) c
          unless out.contains v do out := out.push v
          continue
        unless inScope env c do continue
        let some ci := env.find? c | continue
        unless ci matches .defnInfo _ do continue
        let ctx' := match cloneOf? env c with
          | some ct => ct :: ctx
          | none => ctx
        todo := (ci.value!.getUsedConstants.toList.map (·, ctx')) ++ todo
    return out

open Elab Term in
/-- The restriction `{-X₁, …, -Xₖ}` as a footprint term, resolved in the current context, as
`declare module` resolves it: a declared module (a local) is `glob X`; a global variable itself;
a concrete module (a definition) the globals its code mentions. -/
def restrictionTerm (xs : Array Ident) : Elab.Term.TermElabM (TSyntax `term) := do
  let mut out : Array (TSyntax `term) := #[]
  let mut seen : NameSet := {}
  for x in xs do
    if (← getLCtx).findFromUserName? x.getId |>.isSome then
      out := out.push (← `((FVP.fvP $x).glob))
      continue
    let c ← Elab.realizeGlobalConstNoOverloadWithInfo x
    let env ← getEnv
    let vars := if isGlobalVar env c then #[c] else globalVarsOf env #[c]
    if vars.isEmpty then
      logWarningAt x m!"`{c}` mentions no global variable: the restriction `-{x}` is empty"
    for v in vars do
      unless seen.contains v do
        seen := seen.insert v
        out := out.push (← `(Lens.footprint $(mkCIdent v)))
  match out.toList with
  | [] => `((⊥ : Footprint VariableAssignment))
  | j :: js => js.foldlM (fun acc t => `($acc ⊔ $t)) j

end DeclareModule

/-- An argument of the module type in `declare module`: a name or a parenthesized term (so that
the restriction `{-…}` that follows is not read as one more argument). -/
declare_syntax_cat declare_module_arg
syntax ident : declare_module_arg
syntax "(" term ")" : declare_module_arg

/-- `declare module A <: T a₁ … aₙ {-X₁, …, -Xₖ}`: see the module docstring. -/
syntax (name := declareModule) "declare " "module " ident " <: " ident (ppSpace declare_module_arg)*
  (" {" ("-" ident),* "}")? : command

open Elab Command Term Meta DeclareModule in
elab_rules : command
  | `(declare module $A:ident <: $T:ident $args:declare_module_arg* $[{ $[- $xs:ident],* }]?) => do
    let argTs : Array Term ← args.mapM fun
      | `(declare_module_arg| $x:ident) => pure (x : Term)
      | `(declare_module_arg| ($t:term)) => `(($t))
      | _ => throwUnsupportedSyntax
    let ty ← `($T $argTs*)
    let xs := (xs.getD #[])
    -- the restriction, each `-X` resolved in the section's context
    let S ← runTermElabM fun _ => restrictionTerm xs
    elabCommand (← `(variable ($A : $ty) [Module.Declared $A $S]))
    -- EC generalizes every lemma of the section that mentions `A` over the declaration, the
    -- restriction included whether the proof needs it or not
    elabCommand (← `(set_option linter.unusedSectionVars false))

end GaudisCrypt
