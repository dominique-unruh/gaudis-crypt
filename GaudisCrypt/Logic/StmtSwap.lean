import GaudisCrypt.Logic.HoareWp
import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Logic.PRHL.Prhl

/-!
# Swapping statements (EC's `swap`)

Two adjacent statements can be exchanged when neither sees the other's effect.  Two cases cover
what game hops need:

* a **deterministic** statement `d` (`Stmt.Det d u`: it runs as the update `u`) and a statement
  `s` that **commutes with `u`** (`Stmt.CommutesWith s u`): `d; s ≡ s; d` (`Stmt.swap_det`);
* a **sampling** `x <$ e` from a distribution that does not depend on the state, and a statement
  that commutes with every write to `x`: `x <$ e; s ≡ s; x <$ e` (`Stmt.swap_sample`, by Fubini
  for the two independent draws).

`Stmt.CommutesWith s u` — running `s` from `u σ` is running it from `σ` and applying `u` after —
is stated on expectations, and proved syntax-directed (assignments, samplings, calls,
conditionals, sequences) from **state equations** that `simp` settles for distinct variables:
the update leaves what `s` reads alone, and commutes with what `s` writes.  A call commutes with
an update of the caller's locals that does not touch the result variable or the arguments: the
callee runs on its own locals.

Like `split` and `inline`, a swap is an equivalence of statements, so it works on every
registered judgment (`stmt_swap`).  Also here: splitting a tuple assignment into one assignment
per component (`Stmt.split_pair`), which is how a swap reaches one parameter of an inlined call.
-/

namespace GaudisCrypt

/-- `s` commutes with the state update `u`: from `u σ` it does what it does from `σ`, followed by
`u`. -/
def Stmt.CommutesWith (s : Stmt) (u : ProgramState → ProgramState) : Prop :=
  ∀ (g : ProgramState → ENNReal) (σ : ProgramState), s.ewp g (u σ) = s.ewp (fun τ => g (u τ)) σ

namespace Stmt.CommutesWith

variable {u : ProgramState → ProgramState}

theorem «skip» : Stmt.CommutesWith StmtWithHoles.skip u := fun g σ => by
  simp only [Stmt.ewp_skip]

theorem seq {s₁ s₂ : Stmt} (h₁ : s₁.CommutesWith u) (h₂ : s₂.CommutesWith u) :
    Stmt.CommutesWith (.seq s₁ s₂) u := fun g σ => by
  rw [Stmt.ewp_seq, Stmt.ewp_seq, h₁]
  congr 1
  funext τ
  exact h₂ g τ

theorem sample {α : Type} {y : Setter α ProgramState} {e : Getter (SubProbability α) ProgramState}
    (he : ∀ σ, e.get (u σ) = e.get σ) (hy : ∀ v σ, y.set v (u σ) = u (y.set v σ)) :
    Stmt.CommutesWith (.sample y e) u := fun g σ => by
  simp only [Stmt.ewp_sample, he, hy]

theorem assign {α : Type} {y : Setter α ProgramState} {e : Getter α ProgramState}
    (h : ∀ σ, y.set (e.get (u σ)) (u σ) = u (y.set (e.get σ) σ)) :
    Stmt.CommutesWith (StmtWithHoles.assign y e) u := fun g σ => by
  simp only [Stmt.ewp_assign, h]

theorem ite {c : Getter Bool ProgramState} {t e : Stmt} (hc : ∀ σ, c.get (u σ) = c.get σ)
    (ht : t.CommutesWith u) (he : e.CommutesWith u) :
    Stmt.CommutesWith (.ifThenElse c t e) u := fun g σ => by
  simp only [Stmt.ewp_ifThenElse, hc]
  split
  · exact ht g σ
  · exact he g σ

theorem «call» {sig : ProcedureSignature} {y : Setter sig.ret ProgramState} {p : Procedure sig}
    {args : Getter sig.ParamType ProgramState} (ha : ∀ σ, args.get (u σ) = args.get σ)
    (hg : ∀ σ, (u σ).globals = σ.globals)
    (hy : ∀ v gl σ, y.set v (ProgramState.globalL.set gl (u σ))
      = u (y.set v (ProgramState.globalL.set gl σ))) :
    Stmt.CommutesWith (Stmt.call y p args) u := fun g σ => by
  simp only [Stmt.ewp_call, ha, hg, hy]

end Stmt.CommutesWith

/-! ## Equivalences -/

/-- Fubini for two independent expectations (discrete measures). -/
theorem SubProbability.expected_comm {A : Type*} {B : Type*} (μ : SubProbability A)
    (ν : SubProbability B) (G : A → B → ENNReal) :
    μ.expected (fun a => ν.expected (G a)) = ν.expected (fun b => μ.expected fun a => G a b) := by
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace B := ⊤
  exact (lintegral_lintegral_swap_discrete μ.2.2 ν.2.2 G).symm

/-- Statements with the same expectations are equivalent. -/
theorem Stmt.equiv_of_ewp {a b : Stmt} (h : ∀ g σ, a.ewp g σ = b.ewp g σ) :
    StmtWithHoles.Equiv a b := by
  have hden : programDenotation a = programDenotation b := funext fun σ =>
    SubProbability.ext_of_expected fun F => h (fun τ => F ((), τ)) σ
  intro inst sa sb hab
  rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty, hden]
  subst hab
  exact SubProbability.bind_pure _

/-- **Swap a deterministic statement** with one that commutes with its update. -/
theorem Stmt.swap_det {d s : Stmt} {u : ProgramState → ProgramState} (hd : Stmt.Det d u)
    (hs : s.CommutesWith u) : StmtWithHoles.Equiv (.seq d s : Stmt) (.seq s d) :=
  Stmt.equiv_of_ewp fun g σ => by
    have hd' : ∀ g, d.ewp g = fun σ => g (u σ) := fun g => funext fun σ => hd _ σ
    rw [Stmt.ewp_seq, Stmt.ewp_seq, hd', hd']
    exact hs g σ

/-- **Swap a sampling** from a distribution that does not depend on the state with a statement
that commutes with every write to the sampled variable. -/
theorem Stmt.swap_sample {α : Type} {x : Setter α ProgramState}
    {e : Getter (SubProbability α) ProgramState} {s : Stmt} (he : ∀ σ τ, e.get σ = e.get τ)
    (hs : ∀ a, s.CommutesWith (x.set a)) :
    StmtWithHoles.Equiv (.seq (.sample x e) s : Stmt) (.seq s (.sample x e)) :=
  Stmt.equiv_of_ewp fun g σ => by
    rw [Stmt.ewp_seq, Stmt.ewp_seq, Stmt.ewp_sample, Stmt.ewp_sample]
    simp only [hs _ g]
    have : (fun τ => (e.get τ).expected fun a => g (x.set a τ))
        = fun τ => (e.get σ).expected fun a => g (x.set a τ) := funext fun τ => by rw [he τ σ]
    rw [this]
    simp only [Stmt.ewp, ProgramDenotation.wp]
    exact (SubProbability.expected_comm _ _ _).symm

/-- **Split a pair assignment** `(x, y) <- e` into `x <- e.1; y <- e.2`, when the second
component does not read `x`. -/
theorem Stmt.split_pair {α β : Type} {x : Lens α ProgramState} {y : Lens β ProgramState}
    [hxy : Lens.Disjoint x y] {e : Getter (α × β) ProgramState}
    (h2 : ∀ v σ, (e.get (x.set v σ)).2 = (e.get σ).2) :
    StmtWithHoles.Equiv (StmtWithHoles.assign (Lens.pair x y).toSetter e : Stmt)
      (.seq (StmtWithHoles.assign x.toSetter ⟨fun σ => (e.get σ).1⟩)
        (StmtWithHoles.assign y.toSetter ⟨fun σ => (e.get σ).2⟩)) :=
  Stmt.equiv_of_ewp fun g σ => by
    rw [Stmt.ewp_seq, Stmt.ewp_assign, Stmt.ewp_assign, Stmt.ewp_assign]
    simp only [h2]
    change g (x.set _ (y.set _ σ)) = _
    rw [hxy.commute]

/-! ## State equations

What the side conditions of `Stmt.CommutesWith` reduce to, after the reads through writes are
simplified: equations between states written in different orders.  `Lens.set_outward X` moves
the writes through `X` outwards past writes through lenses disjoint from it, which normalizes
both sides; resets of other names are passed the same way (`resetSetter_set_intoLocal`). -/

/-- A write through `X` moves out past a write through a disjoint lens. -/
theorem Lens.set_outward {α m : Type*} (X : Lens α m) {β : Type*} (Y : Lens β m)
    [hd : Lens.Disjoint Y X] (w : β) (v : α) (s : m) :
    Y.set w (X.set v s) = X.set v (Y.set w s) :=
  hd.commute s w v

/-- A write to a local variable moves out past a reset of other names. -/
theorem resetSetter_set_intoLocal (S : Set String) (v : VariableName) (hv : v.name ∉ S)
    (u : Unit) (a : v.type) (σ : ProgramState) :
    (resetSetter S).set u ((varLens v).intoLocal.set a σ)
      = (varLens v).intoLocal.set a ((resetSetter S).set u σ) := by
  classical
  obtain ⟨g, l⟩ := σ
  simp only [resetSetter, Lens.intoLocal, Lens.chain, ProgramState.localL, varLens]
  congr 1
  funext w
  by_cases hw : w = v
  · subst hw; simp [hv]
  · simp [Function.update_of_ne hw]

/-- `resetSetter_set_intoLocal` at the spelling a program's local variables carry. -/
theorem resetSetter_set_localVarLens (S : Set String) (n : String) (T : Type) [Nonempty T]
    {key : Nat} (kc : key = VariableName.encode n) (hn : n ∉ S) (u : Unit) (a : T)
    (σ : ProgramState) :
    (resetSetter S).set u ((localVarLens n T kc).set a σ)
      = (localVarLens n T kc).set a ((resetSetter S).set u σ) :=
  resetSetter_set_intoLocal S (@VariableName.mk n T _ key kc) hn u a σ

/-- `resetSetter_set_intoLocal` with the variable name spelled out (as the inliner writes the
variables it makes up): stated for `v`, the slot's type would be the projection `v.type`, which
`simp` cannot match against a concrete type before `v` is known. -/
theorem resetSetter_set_varLens (S : Set String) (n : String) (T : Type) (i : Nonempty T)
    (key : Nat) (kc : key = VariableName.encode n) (hn : n ∉ S) (u : Unit) (a : T)
    (σ : ProgramState) :
    (resetSetter S).set u ((@Lens.intoLocal T (varLens (@VariableName.mk n T i key kc))).set a σ)
      = (@Lens.intoLocal T (varLens (@VariableName.mk n T i key kc))).set a
          ((resetSetter S).set u σ) :=
  resetSetter_set_intoLocal S (@VariableName.mk n T i key kc) hn u a σ

/-- A pair of variables is disjoint from what both components are disjoint from. -/
instance Lens.Disjoint.pair_left {a b c m : Type*} {x : Lens a m} {y : Lens b m}
    {z : Lens c m} [Lens.Disjoint x y] [hxz : Lens.Disjoint x z] [hyz : Lens.Disjoint y z] :
    Lens.Disjoint (Lens.pair x y) z where
  commute s v w := by
    change x.set v.1 (y.set v.2 (z.set w s)) = z.set w (x.set v.1 (y.set v.2 s))
    rw [hyz.commute, hxz.commute]

instance Lens.Disjoint.pair_right {a b c m : Type*} {x : Lens a m} {y : Lens b m}
    {z : Lens c m} [Lens.Disjoint x y] [hzx : Lens.Disjoint z x] [hzy : Lens.Disjoint z y] :
    Lens.Disjoint z (Lens.pair x y) where
  commute s v w := by
    change z.set v (x.set w.1 (y.set w.2 s)) = x.set w.1 (y.set w.2 (z.set v s))
    rw [hzx.commute, hzy.commute]

namespace StmtSwap

open Lean Meta Elab Tactic TacticMisc

/-- The lens (into the program state) behind a setter: `Lens.toSetter X`, or an l-value
`liftLens X` (`X` itself for a lens into the program state, `X.intoGlobal` for a global). -/
def lensOfSetter? (x : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let x ← instantiateMVars x
  if x.isAppOfArity ``Lens.toSetter 3 then return some x.appArg!
  if x.isAppOfArity `GaudisCrypt.liftLens 4 then
    let X := x.appArg!
    let .app (.app (.const ``Lens _) _) M ← whnfR (← inferType X) | return none
    if ← isDefEq M (mkConst ``ProgramState) then return some X
    if ← isDefEq M (mkConst ``VariableAssignment) then
      return some (← mkAppM ``Lens.intoGlobal #[X])
  return none

/-- Prove the side condition `ty` (a state equation, or a getter's independence of a write) by
`simp`: reads through writes (`HoareWp.simpReadsDecls`), writes through `X?` pushed outward,
writes to locals pushed out past resets. -/
def discharge (ty : Lean.Expr) (X? : Option Lean.Expr) : MetaM Lean.Expr := do
  let m ← mkFreshExprMVar ty
  let (_, g) ← m.mvarId!.intros
  let mut thms : SimpTheorems := {}
  for n in HoareWp.simpReadsDecls ++
      [``resetSetter_set_varLens, ``resetSetter_set_localVarLens, ``Lens.Disjoint.pair_left,
        ``Lens.Disjoint.pair_right] do
    if (← getConstInfo n) matches .thmInfo _ then thms ← thms.addConst n
    else thms ← thms.addDeclToUnfold n
  if let some X := X? then
    -- `Lens.set_outward X`, the other lens's universe left as a parameter for `simp`
    let .app (.app (.const ``Lens _) α) m ← whnfR (← inferType X)
      | throwError "stmt_swap: not a lens:{indentExpr X}"
    let lα ← getLevel α
    let lm ← getLevel m
    let lvl (l : Level) : MetaM Level := do
      match (← instantiateLevelMVars l).dec with
      | some l' => return l'
      | none => throwError "stmt_swap: unexpected universe {l}"
    let pf := mkAppN (mkConst ``Lens.set_outward [← lvl lα, ← lvl lm, .param `u])
      #[α, m, X]
    thms ← thms.add (.stx (← mkFreshId) .missing) #[`u] pf
  let ctx ← Simp.mkContext (config := { decide := true, failIfUnchanged := false })
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simpGoal g ctx #[← Simp.getSimprocs]
  if let some (_, g') := r then
    try g'.refl
    catch _ =>
      -- the default simp set as well
      let ctx' ← Simp.mkContext (config := { decide := true, failIfUnchanged := false })
        (simpTheorems := #[thms, ← getSimpTheorems]) (congrTheorems := ← getSimpCongrTheorems)
      let (r', _) ← simpGoal g' ctx' #[← Simp.getSimprocs]
      if let some (_, g'') := r' then
        try g''.refl
        catch _ =>
          throwError "stmt_swap: cannot show that the statements commute; left to prove:\
            {indentExpr (← g''.getType)}"
  instantiateMVars m

/-- A proof of `ty` by the rule `lem`: its conclusion unified with `ty`; its premises about
sub-statements (`Stmt.CommutesWith t u`) by `sub`, the others by `discharge`. -/
def applyRule (lem : Name) (ty : Lean.Expr) (X? : Option Lean.Expr)
    (sub : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr := do
  let c ← mkConstWithFreshMVarLevels lem
  let (ms, _, concl) ← forallMetaTelescope (← inferType c)
  unless ← isDefEq concl ty do throwError "stmt_swap: `{lem}` does not apply to{indentExpr ty}"
  for m in ms do
    if ← m.mvarId!.isAssigned then continue
    let t ← instantiateMVars (← inferType m)
    let pf ← if t.isAppOfArity ``Stmt.CommutesWith 2 then sub (t.getArg! 0) (t.getArg! 1)
      else discharge t X?
    unless ← isDefEq m pf do throwError "stmt_swap: cannot use the proof of{indentExpr t}"
  instantiateMVars (mkAppN c ms)

/-- A proof that the statement `s` commutes with the update `u` (`Stmt.CommutesWith s u`), built
from its syntax; `X?` is the lens `u` writes through, if any. -/
partial def commutesOf (s u : Lean.Expr) (X? : Option Lean.Expr) : MetaM Lean.Expr := do
  let s ← openStmt (stripLets (← instantiateMVars s))
  let ty ← mkAppM ``Stmt.CommutesWith #[s, u]
  let some h := s.getAppFn.constName? | throwError "stmt_swap: not a statement:{indentExpr s}"
  let lem ← match h with
    | ``StmtWithHoles.skip => pure ``Stmt.CommutesWith.«skip»
    | ``StmtWithHoles.seq => pure ``Stmt.CommutesWith.seq
    | ``StmtWithHoles.sample => pure ``Stmt.CommutesWith.sample
    | ``StmtWithHoles.assign => pure ``Stmt.CommutesWith.assign
    | ``StmtWithHoles.ifThenElse => pure ``Stmt.CommutesWith.ite
    | ``StmtWithHoles.call | ``Stmt.call | ``StmtWithHoles.call' =>
        pure ``Stmt.CommutesWith.«call»
    | _ => throwError "stmt_swap: no commutation rule for{indentExpr s}"
  applyRule lem ty X? fun t u' => commutesOf t u' X?

/-- The sampling `x <$ e` in `s`, if `s` is one. -/
def sample? (s : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let s ← openStmt (stripLets (← instantiateMVars s))
  unless s.isAppOf ``StmtWithHoles.sample do return none
  return some (s.getArg! (s.getAppNumArgs - 2), s.appArg!)

/-- A proof of `(a; b).Equiv (b; a)`: one of them deterministic and the other commuting with its
update, or one of them a sampling from a constant distribution and the other commuting with
writes to its variable. -/
def swapPair (a b : Lean.Expr) : MetaM Lean.Expr := do
  let detSwap (d s : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let some (u, hd) ← detOf? d | return none
    let d' ← openStmt (stripLets d)
    let X? ← if d'.isAppOf ``StmtWithHoles.assign then lensOfSetter? (d'.getArg! 2)
      else pure none
    some <$> mkAppM ``Stmt.swap_det #[hd, ← commutesOf s u X?]
  let sampleSwap (smp s : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let some (x, e) ← sample? smp | return none
    let X? ← lensOfSetter? x
    let heTy ← withLocalDeclD `σ (mkConst ``ProgramState) fun σ =>
      withLocalDeclD `τ (mkConst ``ProgramState) fun τ => do
        mkForallFVars #[σ, τ]
          (← mkEq (← mkAppM ``Getter.get #[e, σ]) (← mkAppM ``Getter.get #[e, τ]))
    let he ← try discharge heTy none
      catch _ => throwError "stmt_swap: the distribution of{indentExpr smp}\ndepends on the state"
    let .forallE _ α _ _ ← whnf (← inferType (← mkAppM ``Setter.set #[x])) | failure
    let hs ← withLocalDeclD `a α fun av => do
      mkLambdaFVars #[av] (← commutesOf s (← mkAppM ``Setter.set #[x, av]) X?)
    some <$> mkAppM ``Stmt.swap_sample #[he, hs]
  let symm (p : Lean.Expr) : MetaM Lean.Expr := mkAppM ``StmtWithHoles.Equiv.symm #[p]
  let attempts : List (MetaM (Option Lean.Expr)) :=
    [detSwap a b, (do return (← (← detSwap b a).mapM symm)),
     sampleSwap a b, (do return (← (← sampleSwap b a).mapM symm))]
  let mut err : Option MessageData := none
  for t in attempts do
    let st ← saveState
    try
      if let some p ← t then return p
    catch e =>
      st.restore
      if err.isNone then err := some e.toMessageData
  throwError "stmt_swap: cannot swap{indentExpr a}\nwith{indentExpr b}\n{err.getD m!"(neither \
    is deterministic or a sampling)"}"

/-- Swap the statements at positions `p` and `p + 1` (from 0) of the right-nested sequence `s`;
the result and the proof of `s.Equiv result`. -/
partial def swapAt (p : Nat) (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => do
      let (r, pr) ← swapAt p (body.instantiate1 fv)
      return (← mkLetFVars #[fv] r (usedLetOnly := false),
              ← mkLetFVars #[fv] pr (usedLetOnly := false))
  unless s.isAppOfArity ``StmtWithHoles.seq 3 do
    throwError "stmt_swap: no statement at position {p + 1}"
  let a := s.getArg! 1
  let rest ← openStmt (s.getArg! 2)
  if p > 0 then
    let (rest', pr) ← swapAt (p - 1) rest
    return (← mkAppM ``StmtWithHoles.seq #[a, rest'],
            ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl a, pr])
  if rest.isAppOfArity ``StmtWithHoles.seq 3 then
    let b := rest.getArg! 1
    let r := rest.getArg! 2
    let hab ← swapPair a b
    let p1 ← mkAppM ``StmtWithHoles.Equiv.symm
      #[← mkAppM ``StmtWithHoles.Equiv.seq_assoc #[a, b, r]]
    let p2 ← mkAppM ``StmtWithHoles.EquivInLens.seq #[hab, ← mkEquivRefl r]
    let p3 ← mkAppM ``StmtWithHoles.Equiv.seq_assoc #[b, a, r]
    let pr ← mkAppM ``StmtWithHoles.Equiv.trans
      #[p1, ← mkAppM ``StmtWithHoles.Equiv.trans #[p2, p3]]
    return (← mkAppM ``StmtWithHoles.seq #[b, ← mkAppM ``StmtWithHoles.seq #[a, r]], pr)
  return (← mkAppM ``StmtWithHoles.seq #[rest, a], ← swapPair a rest)

/-- Move the statement at position `p` by `k` positions (later for `k > 0`), one swap at a time. -/
def moveStmt (p : Nat) (k : Int) (s : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let mut cur := s
  let mut pr ← mkEquivRefl s
  let mut pos := p
  for _ in [0:k.natAbs] do
    let at_ := if k > 0 then pos else pos - 1
    if k < 0 && pos == 0 then throwError "stmt_swap: cannot move the first statement earlier"
    let (s', p') ← swapAt at_ cur
    pr ← mkAppM ``StmtWithHoles.Equiv.trans #[pr, p']
    cur := s'
    pos := if k > 0 then pos + 1 else pos - 1
  return (cur, pr)

/-- `stmt_swap n k`: move the statement at position `n` (from 0) by `k` positions — later for
`k > 0`, earlier for `-k` (EC's `swap`).  Each step exchanges two neighbours, one deterministic
and the other commuting with its update, or one a sampling from a constant distribution and the
other commuting with the writes to its variable; the commutation is shown by `simp`.  Any
registered judgment; on a relational one, `stmt_swap{i} n k` on side `i`. -/
syntax "stmt_swap" (Judgment.judgmentSide)? ppSpace num ppSpace ("-")? num : tactic

elab_rules : tactic
  | `(tactic| stmt_swap $[$s]? $n:num $[-%$neg]? $k:num) => do
    let k : Int := if neg.isSome then -(k.getNat : Int) else k.getNat
    liftMetaTactic1 fun g => some <$>
      Judgment.onStmt (moveStmt n.getNat k) g (Judgment.sideOf? s)

/-- Split the pair assignment at position `p` into one assignment per component, recursively
for nested pairs (`Stmt.split_pair`). -/
partial def splitPairAt (p : Nat) (s₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let s ← openStmt s₀
  if let .letE n ty val body _ := s then
    return ← withLetDecl n ty val fun fv => do
      let (r, pr) ← splitPairAt p (body.instantiate1 fv)
      return (← mkLetFVars #[fv] r (usedLetOnly := false),
              ← mkLetFVars #[fv] pr (usedLetOnly := false))
  let (a, rest?) := if s.isAppOfArity ``StmtWithHoles.seq 3 then
      (s.getArg! 1, some (s.getArg! 2))
    else (s, none)
  if p > 0 then
    let some rest := rest? | throwError "stmt_split_pair: no statement at position {p}"
    let (rest', pr) ← splitPairAt (p - 1) rest
    return (← mkAppM ``StmtWithHoles.seq #[a, rest'],
            ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl a, pr])
  let (a', pa) ← splitPair a
  match rest? with
  | none => return (a', pa)
  | some rest =>
    return (← mkAppM ``StmtWithHoles.seq #[a', rest],
            ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, ← mkEquivRefl rest])
where
  /-- `(x, y) <- e` ↦ `x <- e.1; y <- e.2`, the second split further if it is a pair. -/
  splitPair (a₀ : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
    let a ← openStmt (stripLets (← instantiateMVars a₀))
    unless a.isAppOf ``StmtWithHoles.assign do
      throwError "stmt_split_pair: not an assignment:{indentExpr a}"
    let some L ← lensOfSetter? (a.getArg! 2)
      | throwError "stmt_split_pair: not an assignment to variables:{indentExpr a}"
    unless L.isAppOfArity ``Lens.pair 6 do
      throwError "stmt_split_pair: not a tuple assignment:{indentExpr a}"
    let c ← mkConstWithFreshMVarLevels ``Stmt.split_pair
    let (ms, _, concl) ← forallMetaTelescope (← inferType c)
    -- `concl` is `(assign (pair x y) e).Equiv …`: unify its left side with `a`
    unless concl.isAppOfArity ``StmtWithHoles.Equiv 3 do
      throwError "stmt_split_pair: unexpected lemma"
    unless ← isDefEq (concl.getArg! 1) a do
      throwError "stmt_split_pair: cannot match{indentExpr a}"
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let t ← instantiateMVars (← inferType m)
      if (← isClass? t).isSome then
        unless ← isDefEq m (← synthInstance t) do throwError "stmt_split_pair: instance"
      else
        unless ← isDefEq m (← discharge t (some (L.getArg! 3))) do
          throwError "stmt_split_pair: the second component reads the first:{indentExpr t}"
    let pf ← instantiateMVars (mkAppN c ms)
    let rhs := (← instantiateMVars concl).getArg! 2
    -- the components' getters, reduced (`(⟨fun σ => (f σ, g σ)⟩.get σ).1` is `f σ`)
    let rhs ← Meta.transform rhs (post := fun e => do
      if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
        let e' ← whnfR e
        if e' != e then return .visit e'
      if e.isAppOfArity ``Getter.get 4 then
        let e' ← whnfR e
        if e' != e then return .visit e'
      return .continue)
    let pf ← mkExpectedTypeHint pf (← mkAppM ``StmtWithHoles.Equiv #[a, rhs])
    -- split the second component further
    let second := rhs.getArg! 2
    let (second', p2) ← try splitPair second catch _ => pure (second, ← mkEquivRefl second)
    let rhs' ← mkAppM ``StmtWithHoles.seq #[rhs.getArg! 1, second']
    let p2' ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl (rhs.getArg! 1), p2]
    return (rhs', ← mkAppM ``StmtWithHoles.Equiv.trans #[pf, p2'])

/-- `stmt_split_pair n`: split the tuple assignment at position `n` (from 0) into one assignment
per component (`Stmt.split_pair`; each component must not read the ones before it).  Any
registered judgment; `stmt_split_pair{i} n` on side `i` of a relational one. -/
elab "stmt_split_pair" s:(Judgment.judgmentSide)? ppSpace n:num : tactic =>
  liftMetaTactic1 fun g => some <$>
    Judgment.onStmt (fun st => do
      let (s₁, p₁) ← splitPairAt n.getNat st
      let (s₂, p₂) ← flattenSeq s₁
      return (s₂, ← mkAppM ``StmtWithHoles.Equiv.trans #[p₁, p₂])) g (Judgment.sideOf? s)

end StmtSwap

end GaudisCrypt
