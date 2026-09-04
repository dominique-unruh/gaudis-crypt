import GaudisCrypt.Language.ModuleExpressions

/-! # Modules

A `Module T` is a closed, well-typed, normal `ModuleExpression` of type `T`, together with the
operations on such (application, projections, pairing) and the `IsModule` bridge from Lean types
to `ModuleTypeRep`s.  The underlying expression calculus lives in `ModuleExpressions.lean`. -/

namespace GaudisCrypt

variable [ProgramSpec]

/- # Modules -/

structure Module (T : ModuleTypeRep) where
  expression : ModuleExpression
  typed : expression.HasType [] T
  normal : expression.NormalClosed

/-- Build a `Module` from a well-typed closed expression by normalising it. -/
noncomputable def ModuleExpression.toModule {T : ModuleTypeRep}
    (m : ModuleExpression) (h : m.HasType [] T := by moduletyping!) : Module T :=
  ⟨m.reduce, m.reduce_hasType h, m.reduce_normalClosed h⟩

noncomputable instance : CoeFun (Module (.arr T U)) (fun _ ↦ Module T → Module U) where
  coe f x := (f.expression.app x.expression).toModule (.app f.typed x.typed)

noncomputable def Module.fst' {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toModule (.fst m.typed)

noncomputable def Module.snd' {T U} (m : Module (.prod T U)) : Module U :=
  m.expression.snd.toModule (.snd m.typed)

noncomputable def Module.pair' {T U} (m1 : Module T) (m2 : Module U) : Module (.prod T U) :=
  (m1.expression.pair m2.expression).toModule (.pair m1.typed m2.typed)

@[ext]
theorem Module.ext {T} {m1 m2 : Module T} (h : m1.expression = m2.expression) :
  m1 = m2 := by
  obtain ⟨e1, t1, n1⟩ := m1; obtain ⟨e2, t2, n2⟩ := m2
  simp only at h; subst h; rfl

@[simp]
theorem Module.expression_fst' {T U} (m : Module (.prod T U)) :
    m.fst'.expression = m.expression.fst.reduce := rfl

@[simp]
theorem Module.expression_snd' {T U} (m : Module (.prod T U)) :
    m.snd'.expression = m.expression.snd.reduce := rfl


@[simp]
theorem Module.toModule_expression {T} (m : ModuleExpression) (h : m.HasType [] T) :
    (m.toModule h).expression = m.reduce := rfl

@[simp]
theorem Module.reduce_expression {T} (m : Module T) :
  m.expression.reduce = m.expression :=
  ModuleExpression.reduce_of_stuck m.normal.normal.stuck

/-- A module's expression is closed, so a substitution leaves it alone. -/
@[simp]
theorem Module.substituteSimultaneously_expression {T} (m : Module T)
    (σ : Nat → ModuleExpression) :
    m.expression.substituteSimultaneously σ = m.expression :=
  m.typed.substituteSimultaneously_eq_self (by simp)

/-- A module's expression is closed, so a renaming leaves it alone.  (This is what a substitution
going under a binder does to it — `liftSubst` renames by `Nat.succ` — so normalising an application
of a *curried* module needs this as well as `Module.substituteSimultaneously_expression`.) -/
@[simp]
theorem Module.rename_expression {T} (m : Module T) (ρ : Nat → Nat) :
    m.expression.rename ρ = m.expression :=
  m.typed.rename_eq_self (by simp)

/-- Pairing two modules pairs their expressions — no `reduce` left over, both being normal. -/
theorem Module.expression_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).expression = .pair m1.expression m2.expression :=
  ModuleExpression.reduce_of_normal (.pair m1.normal.normal m2.normal.normal)

/-- Reducing a pair componentwise: if the components reduce to the expressions of the modules
    `m1`/`m2`, the pair reduces to the expression of their `Module.pair'`.  Turns a `reduce` of a
    whole record into the record of the reduced components, with no detour through termination —
    normality of the *result* comes from the modules `m1`/`m2`.  (Currently unused: `module_apply`
    used to peel `X.apply_simp`'s record with it, but now normalises both sides with
    `reduce_simp` instead.) -/
theorem Module.reduce_pair_expression {T U} {a b : ModuleExpression}
    (m1 : Module T) (m2 : Module U)
    (ha : a.reduce = m1.expression) (hb : b.reduce = m2.expression) :
    (ModuleExpression.pair a b).reduce = (m1.pair' m2).expression := by
  rw [ModuleExpression.reduce_pair_cong ha hb, Module.expression_pair',
    ModuleExpression.reduce_of_normal (.pair m1.normal.normal m2.normal.normal)]

@[simp]
theorem Module.fst_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).fst' = m1 := by
  ext
  change ((m1.expression.pair m2.expression).reduce.fst).reduce = m1.expression
  rw [ModuleExpression.reduce_of_stuck
        (ModuleExpression.NormalClosed.pair m1.normal m2.normal).normal.stuck,
      ModuleExpression.reduce_fst, m1.reduce_expression]

@[simp]
theorem Module.snd_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).snd' = m2 := by
  ext
  change ((m1.expression.pair m2.expression).reduce.snd).reduce = m2.expression
  rw [ModuleExpression.reduce_of_stuck
        (ModuleExpression.NormalClosed.pair m1.normal m2.normal).normal.stuck,
      ModuleExpression.reduce_snd, m2.reduce_expression]


theorem Module.pair_fst_snd' : (Module.fst' m).pair' (Module.snd' m) = m := by
  obtain ⟨a, b, he⟩ := ModuleExpression.pair_type_is_pair m.typed m.normal
  have hn : (ModuleExpression.pair a b).NormalClosed := he ▸ m.normal
  obtain ⟨hna, hnb⟩ : a.NormalClosed ∧ b.NormalClosed := by
    cases hn with | pair x y => exact ⟨x, y⟩
  ext
  change ((m.expression.fst.reduce).pair (m.expression.snd.reduce)).reduce = m.expression
  rw [he, ModuleExpression.reduce_fst, ModuleExpression.reduce_snd,
      ModuleExpression.reduce_of_stuck hna.normal.stuck,
      ModuleExpression.reduce_of_stuck hnb.normal.stuck,
      ModuleExpression.reduce_of_stuck hn.normal.stuck]


abbrev Module.Unit := Module .unit
noncomputable def Module.unit : Module .unit := ModuleExpression.unit.toModule .unit

class IsModule (T : Type _) where
  moduleTypeRep : ModuleTypeRep
  isModule : T = Module moduleTypeRep := by rfl

@[reducible]
instance : IsModule (Module t) where
  moduleTypeRep := t
  isModule := rfl

def Module.moduleTypeRep (T : Type _) [inst : IsModule T] := inst.moduleTypeRep

def Module.cast (T : Type _) [inst : IsModule T] (m : T) : Module (Module.moduleTypeRep T) :=
  inst.isModule ▸ m

def Module.cast' (T : Type _) [inst : IsModule T] (m : Module (Module.moduleTypeRep T)) : T :=
  inst.isModule.symm ▸ m

def Module.Arr (M : Type _) (N : Type _) [IsModule M] [IsModule N] : Type _ :=
  Module (ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N))

instance (M : Type _) (N : Type _) [IsModule M] [IsModule N] : IsModule (Module.Arr M N) where
  moduleTypeRep := ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N)
  isModule := rfl

def Module.Proc (sig : ProcedureSignature) : Type _ :=
  Module (ModuleTypeRep.proc sig)

instance {sig} : IsModule (Module.Proc sig) where
  moduleTypeRep := ModuleTypeRep.proc sig

noncomputable def Module.app' (m : Module (.arr A B)) (m' : Module A) : Module B :=
  (m.expression.app m'.expression).toModule (.app m.typed m'.typed)

noncomputable def Module.app {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m : Module.Arr M N) (m' : M) : N :=
  have hMN : Module.Arr M N =
      Module (ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Arr]
  iN.isModule.symm ▸ Module.app' (hMN ▸ m) (iM.isModule ▸ m')

theorem Module.cast_app [IsModule M] [IsModule N] (a : Module.Arr M N) (b : M) :
    Module.cast _ (Module.app a b)
      = Module.app' (Module.cast (Module.Arr M N) a) (Module.cast M b) := by
  unfold Module.cast Module.app
  simp only [eqRec_eq_cast, cast_cast, cast_eq]
  rfl

/-- Simp set collecting the field accessors `moduletype` emits (`X.f : X → Tᵢ`, a chain of
`Module.fst'`/`Module.snd'`).

A goal about a field of an *abstract* module — `S : CommitmentScheme` a parameter, not a literal
record — can only make progress by unfolding the accessor, and a tactic cannot know the accessor's
name.  This set is how `proc_apply` reaches them. -/
register_simp_attr module_accessor

/-- What is derivable about a field accessor `acc : M → T` of a module type, bundled into one
declaration.

The `moduletype` command emits one of these per field, as `X.f.utilities`, rather than a separate
declaration per fact — the facts are reached as `X.f.utilities.accessorModule` and so on.  It is a
structure and not a class: there is nothing to synthesise, the command hands the value over by
name. -/
structure ModuleTypeUtilities (M T : Type _) [IsModule M] [IsModule T] (acc : M → T) where
  /-- The projection `acc` implements, as it acts on `ModuleExpression`s
  (`fun e => e.snd.fst`, …). -/
  proj : ModuleExpression → ModuleExpression
  /-- The accessor as a module of its own: a projection is a module morphism. -/
  accessorModule : Module.Arr M T
  /-- …and applying that module is the accessor. -/
  apply_simp : ∀ m : M, Module.app accessorModule m = acc m
  /-- The accessor at the level of expressions: it is `proj`, reduced.  The `.reduce` is not
  removable — `Module.expression` is always a reduct, and `proj m.expression` need not be normal. -/
  expression_eq : ∀ m : M,
    (Module.cast T (acc m)).expression = (proj (Module.cast M m).expression).reduce

def Module.Prod (M : Type _) (N : Type _) [IsModule M] [IsModule N] : Type _ :=
  Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N))

instance (M : Type _) (N : Type _) [IsModule M] [IsModule N] : IsModule (Module.Prod M N) where
  moduleTypeRep := ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)
  isModule := rfl

noncomputable def Module.fst {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m : Module.Prod M N) : M :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  iM.isModule.symm ▸ Module.fst' (hMN ▸ m)

noncomputable def Module.snd {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m : Module.Prod M N) : N :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  iN.isModule.symm ▸ Module.snd' (hMN ▸ m)

noncomputable def Module.pair {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N]
    (m1 : M) (m2 : N) : Module.Prod M N :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  hMN ▸ Module.pair' (iM.isModule ▸ m1) (iN.isModule ▸ m2)

@[simp]
theorem Module.fst_pair {M N : Type max 1 u} [IsModule M] [IsModule N] (m1 : M) (m2 : N) :
    Module.fst (Module.pair m1 m2) = m1 := by
  simp only [Module.fst, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast, cast_eq,
    Module.fst_pair']

@[simp]
theorem Module.snd_pair {M N : Type max 1 u} [IsModule M] [IsModule N] (m1 : M) (m2 : N) :
    Module.snd (Module.pair m1 m2) = m2 := by
  simp only [Module.snd, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast, cast_eq,
    Module.snd_pair']

theorem Module.pair_fst_snd {M N : Type max 1 u} [IsModule M] [IsModule N] (m : Module.Prod M N) :
    Module.pair (Module.fst m) (Module.snd m) = m := by
  simp only [Module.fst, Module.snd, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast,
    cast_eq, Module.pair_fst_snd']

noncomputable def Module.proc {sig} (p : Procedure sig) : Module.Proc sig :=
  (ModuleExpression.proc p).toModule (.proc p)

/-- Canonical forms at procedure type: a *closed normal* expression of type `.proc sig` is
    literally a `.proc p` node. -/
theorem proc_type_is_proc {sig : ProcedureSignature}
    {m : ModuleExpression} (ht : m.HasType [] (.proc sig)) (h : m.NormalClosed) :
    ∃ p : Procedure sig, m = .proc p := by
  cases h with
  | «proc» =>
      rename_i p
      injection ht.proc_inv with hs
      subst hs
      exact ⟨p, rfl⟩
  | procHoles => cases ht
  | abs _ => cases ht
  | pair _ _ => cases ht
  | unit => cases ht

/-- The procedure of a proc-typed module — the inverse of `Module.proc`.  (`Classical.choose`
    only escapes the Prop-to-data restriction; the witness is unique — see
    `Module.procedure_spec` and `Module.procedure_proc`.) -/
noncomputable def Module.Proc.procedure
    {sig : ProcedureSignature} (m : Module.Proc sig) : Procedure sig :=
    match he : m.expression with
    | @ModuleExpression.proc _ sig' p =>
        -- The signature the `.proc` node carries is the module's own: its typing says so.
        have hsig : sig' = sig := by
          injection (he ▸ m.typed).proc_inv with hs
          exact hs.symm
        hsig ▸ p
    | .procHoles _ _ | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .unit =>
        -- Impossible: `.var`/`.app`/`.fst`/`.snd` are not normal, and the remaining nodes cannot
        -- have a procedure type.
        (show False by cases he ▸ m.normal <;> cases he ▸ m.typed).elim

/-- `Module.procedure` is characterized by its defining equation (the witness of
    `proc_type_is_proc` is unique by constructor injectivity). -/
theorem Module.procedure_spec
    {sig : ProcedureSignature} (m : Module.Proc sig) :
    m.expression = .proc m.procedure := by
  have key : ∀ {a b : ProcedureSignature} (h : a = b) (q : Procedure a),
      ModuleExpression.proc q = ModuleExpression.proc (h ▸ q) := by
    rintro a b rfl q; rfl
  unfold Module.Proc.procedure
  split
  case _ sig' p he => exact he.trans (key _ p)
  all_goals
    rename_i he
    exact (show False by cases he ▸ m.normal <;> cases he ▸ m.typed).elim

/-- Round-trip: wrapping a procedure as a module and extracting recovers it. -/
@[simp] theorem Module.procedure_proc
    {sig : ProcedureSignature} (p : Procedure sig) :
    Module.Proc.procedure ((ModuleExpression.proc p).toModule (.proc p)) = p := by
  have h1 : ((ModuleExpression.proc p).toModule (.proc p)).expression = .proc p :=
    Module.reduce_expression ⟨.proc p, .proc p, .proc⟩
  have h2 := Module.procedure_spec ((ModuleExpression.proc p).toModule (.proc p))
  rw [h1] at h2
  injection h2 with hsig h
  exact h.symm

/-- Renaming by a function that's pointwise the identity is the identity, regardless of `ρ`'s
    behavior elsewhere (needed below since `IsRenaming [] Δ ρ` holds vacuously for *any* `ρ`,
    but we specifically want the renamed term to be syntactically unchanged). -/
private theorem ModuleExpression.rename_id :
    ∀ (m : ModuleExpression) (ρ : Nat → Nat), (∀ n, ρ n = n) → m.rename ρ = m := by
  intro m
  induction m with
  | unit => intro ρ _; rfl
  | proc p => intro ρ _; rfl
  | procHoles ne p => intro ρ _; rfl
  | var n => intro ρ hρ; simp [ModuleExpression.rename, hρ]
  | app f a ihf iha => intro ρ hρ; simp [ModuleExpression.rename, ihf ρ hρ, iha ρ hρ]
  | fst e ih => intro ρ hρ; simp [ModuleExpression.rename, ih ρ hρ]
  | snd e ih => intro ρ hρ; simp [ModuleExpression.rename, ih ρ hρ]
  | pair a b iha ihb => intro ρ hρ; simp [ModuleExpression.rename, iha ρ hρ, ihb ρ hρ]
  | abs body ih =>
      intro ρ hρ
      simp only [ModuleExpression.rename]
      congr 1
      apply ih
      intro n
      cases n with
      | zero => rfl
      | succ n' => simp [ModuleExpression.liftRen, hρ]

/-- A closed term (well-typed in the empty context) is well-typed in *any* context: `Δ = []`
    makes `IsRenaming [] Δ' ρ` hold vacuously for any `ρ`, so picking `ρ := id` and cancelling
    the resulting `rename id` via `rename_id` gives back `m` itself, unchanged, in the wider
    context `Δ'`. -/
private theorem ModuleExpression.HasType.weaken_of_empty {m : ModuleExpression} {T : ModuleTypeRep}
    (h : m.HasType [] T) (Δ : ModuleContext) : m.HasType Δ T := by
  have hIsRen : ModuleExpression.HasType.IsRenaming [] Δ id :=
    fun {n} hn => absurd hn (Nat.not_lt_zero n)
  have hren := h.rename hIsRen
  rwa [ModuleExpression.rename_id m id (fun _ => rfl)] at hren

/-- A module's expression is well-typed in *any* context, not just the empty one — it is closed.
This is what lets `moduletyping` type an expression built from already-formed modules (whose
leaves are `m.expression` rather than a `HasType` constructor). -/
theorem Module.typed_weaken {T : ModuleTypeRep} (m : Module T) (Δ : ModuleContext) :
    m.expression.HasType Δ T := m.typed.weaken_of_empty Δ

noncomputable def Module.const {T U} [IsModule T] [iu : IsModule U] (m : U) : Module.Arr T U :=
  let expr : ModuleExpression := (iu.isModule ▸ m).expression
  have h : expr.HasType [] (Module.moduleTypeRep U) := by
    exact (iu.isModule ▸ m).typed
  let abs : ModuleExpression := .abs expr
  have habs :
      abs.HasType [] (ModuleTypeRep.arr (Module.moduleTypeRep T) (Module.moduleTypeRep U)) := by
    exact .abs (h.weaken_of_empty _)
  abs.toModule habs

noncomputable def Module.procWithHoles {holes : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles holes sig) :
    Module.Arr (Module holes.toModuleTypeRepTuple) (Module.Proc sig) :=
  match h : holes with
  | .empty =>
    Module.const (Module.proc p)
  | .append x y =>
    show Module (.arr (HoleSigs.append x y).toModuleTypeRepTuple (.proc sig))
    from (ModuleExpression.procHoles (by trivial) p).toModule

/-! ## Applying a procedure-with-holes to its callees

The δ-rule `ReductionStep.delta` fires only on a *literal* tuple of `.proc` nodes
(`HoleSigs.Instantiation.toModuleExpr`).  What one has in practice is a tuple of arbitrary module
expressions — the callees, as they were written — which merely *reduce* to such a tuple, each of
them to the `.proc` of a `Module.procedure`.  These lemmas bridge the two: `reduce_tuple_nil`/
`reduce_tuple_cons` build the reduction of the tuple component by component, and
`reduce_app_procWithHoles` then takes the δ-step.  Together they are what the `proc_apply` tactic
(`GaudisCrypt/Language/Syntax2.lean`) runs on the `X.<f>.apply_simp` goals the `module` command
emits. -/

@[simp] theorem HoleSigs.Instantiation.toModuleExpr_nil :
    HoleSigs.Instantiation.toModuleExpr HoleSigs.Instantiation.nil = .unit := rfl

@[simp] theorem HoleSigs.Instantiation.toModuleExpr_push {holes : HoleSigs}
    {sig : ProcedureSignature} (inst : holes.Instantiation) (p : Procedure sig) :
    HoleSigs.Instantiation.toModuleExpr (HoleSigs.Instantiation.push inst p)
      = .pair (.proc p) (HoleSigs.Instantiation.toModuleExpr inst) := rfl

/-- A tuple of procedures is normal: it is built from `.proc` nodes and `.unit` alone. -/
theorem HoleSigs.Instantiation.toModuleExpr_normal {holes : HoleSigs}
    (inst : holes.Instantiation) : (HoleSigs.Instantiation.toModuleExpr inst).Normal := by
  induction holes with
  | empty => exact .unit
  | append holeTail sig ih => exact .pair .proc (ih _)

/-- The empty tuple: `.unit` is already the instantiation of no holes. -/
theorem Module.reduce_tuple_nil :
    (ModuleExpression.unit).reduce
      = HoleSigs.Instantiation.toModuleExpr HoleSigs.Instantiation.nil :=
  ModuleExpression.reduce_of_normal .unit

/-- One component of the tuple: if `c` reduces to the expression of a proc-typed module `m` — which
by canonicity *is* a `.proc` node, namely `.proc m.procedure` — and the rest of the tuple reduces to
`inst`'s, then the whole pair reduces to that of `inst` extended by `m.procedure`. -/
theorem Module.reduce_tuple_cons {holes : HoleSigs} {sig : ProcedureSignature}
    (inst : holes.Instantiation) (m : Module (.proc sig)) (c rest : ModuleExpression)
    (hc : c.reduce = m.expression)
    (hrest : rest.reduce = HoleSigs.Instantiation.toModuleExpr inst) :
    (ModuleExpression.pair c rest).reduce
      = HoleSigs.Instantiation.toModuleExpr
          (HoleSigs.Instantiation.push inst (Module.Proc.procedure m)) := by
  rw [HoleSigs.Instantiation.toModuleExpr_push, ← Module.procedure_spec m,
    ModuleExpression.reduce_pair_cong hc hrest,
    ModuleExpression.reduce_of_normal
      (.pair m.normal.normal (HoleSigs.Instantiation.toModuleExpr_normal inst))]

/-- The δ-step, on an argument that only *reduces* to a tuple of procedures: applying
`Module.procWithHoles p` to it is the procedure `p` with its holes instantiated.  With no holes at
all `Module.procWithHoles p` is the constant function `Module.proc p`, and instantiating changes
nothing (`ProcedureWithHoles.instantiate_empty`) — so the statement covers that case too. -/
theorem Module.reduce_app_procWithHoles {holes : HoleSigs} {sig : ProcedureSignature}
    (p : ProcedureWithHoles holes sig) (T : ModuleExpression) (inst : holes.Instantiation)
    (h : T.reduce = HoleSigs.Instantiation.toModuleExpr inst) :
    (ModuleExpression.app (Module.procWithHoles p).expression T).reduce
      = .proc (p.instantiate inst) := by
  rw [← ModuleExpression.reduce_app_right, h]
  cases holes with
  | empty =>
      rw [ProcedureWithHoles.instantiate_empty]
      have hexpr : (Module.procWithHoles p).expression
          = ModuleExpression.abs (ModuleExpression.proc p) := by
        simp only [Module.procWithHoles, Module.const, Module.proc,
          Module.toModule_expression, ModuleExpression.reduce_proc]
        exact ModuleExpression.reduce_of_normal (.abs .proc)
      rw [hexpr]
      reduce_simp
      trivial
  | append holeTail s =>
      have hexpr : (Module.procWithHoles p).expression
          = ModuleExpression.procHoles (holes := holeTail.append s) trivial p :=
        ModuleExpression.reduce_of_normal .procHoles
      rw [hexpr, ModuleExpression.reduce_step
          (.delta (holes := holeTail.append s) trivial p inst),
        ModuleExpression.reduce_proc]


end GaudisCrypt
