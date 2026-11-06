import GaudisCrypt.Logic.Representation
import GaudisCrypt.Logic.FootprintSolver

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
    (S : outParam (Footprint VariableAssignment)) :
    Prop where
  finite : (FVP.fvP A).FinitelySupported
  restr : FVP.fvP A ≤ Sᶜ

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
    (A : Module.Arr T (Module.Proc sig)) {S : Footprint VariableAssignment}
    [h : Module.Declared A S]
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
uses (EC's `glob` of a concrete module), in the order first met. -/
def globalVarsOf (env : Environment) (roots : Array Name) (cap : Nat := 20000) : Array Name :=
  Id.run do
    let mut out : Array Name := #[]
    let mut seen : NameSet := {}
    let mut todo := roots.toList
    let mut n := 0
    while n < cap do
      match todo with
      | [] => break
      | c :: rest =>
        todo := rest
        n := n + 1
        if seen.contains c then continue
        seen := seen.insert c
        if isGlobalVar env c then
          out := out.push c
          continue
        unless inScope env c do continue
        let some ci := env.find? c | continue
        unless ci matches .defnInfo _ do continue
        todo := ci.value!.getUsedConstants.toList ++ todo
    return out

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
    -- the joinands of the restriction: each `-X` resolved in the section's context
    let joinands ← runTermElabM fun _ => do
      let mut out : Array Term := #[]
      let mut seen : NameSet := {}
      for x in xs do
        if (← getLCtx).findFromUserName? x.getId |>.isSome then
          -- a declared module: `glob X`
          out := out.push (← `((FVP.fvP $x).glob))
          continue
        let c ← realizeGlobalConstNoOverloadWithInfo x
        let env ← getEnv
        let vars := if isGlobalVar env c then #[c] else globalVarsOf env #[c]
        if vars.isEmpty then
          logWarningAt x m!"`{c}` mentions no global variable: the restriction `-{x}` is empty"
        for v in vars do
          unless seen.contains v do
            seen := seen.insert v
            out := out.push (← `(Lens.footprint $(mkCIdent v)))
      return out
    let S ← match joinands.toList with
      | [] => `((⊥ : Footprint VariableAssignment))
      | j :: js => js.foldlM (fun acc t => `($acc ⊔ $t)) j
    elabCommand (← `(variable ($A : $ty) [Module.Declared $A $S]))
    -- EC generalizes every lemma of the section that mentions `A` over the declaration, the
    -- restriction included whether the proof needs it or not
    elabCommand (← `(set_option linter.unusedSectionVars false))

end GaudisCrypt
