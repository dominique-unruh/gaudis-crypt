import GaudisCrypt.Examples.Pedersen.Commitment
import GaudisCrypt.WeakestPreconditions

/-!
# The Pedersen commitment scheme

A transliteration of EasyCrypt's `examples/Pedersen.ec`:

* EC's `clone DLog` (cyclic group `group` with generator `g`, prime exponent field `exp`)
  becomes the structure `PedersenGroup`: the operations the programs mention, plus the laws the
  proofs turned out to need (`f_commring`, `gpow_add`, `gpow_mul` — the last two are EC's
  `expD`/`expM`).  It is a section `variable (group : PedersenGroup)`, and hence a Lean parameter
  of everything below that mentions it.
* EC's `PedersenTypes` + the `Commitment` clone become the `CommitmentTypes` record
  `group.types` (value/commitment = group, message/openingkey = exponent), which every
  `CommitmentScheme`-shaped name here is applied to.
* `module Pedersen : CommitmentScheme` becomes a
  `module Pedersen : (CommitmentScheme group.types) { … }` declaration — EC's own syntax, near
  enough, now that the `module` command exists.
* Correctness is stated as EC states it (`hoare[Correctness(Pedersen).main : true ==> res]`):
  the output distribution puts no mass on `res = false`.  Proven (`pedersen_correctness`), on
  standard axioms only, entirely on the `module` command's generated lemmas — this file declares
  nothing of its own for it beyond the per-procedure `wp_*` lemmas.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt

-- the scheme is deliberately named like the enclosing example namespace (EC: `module Pedersen`)
set_option linter.dupNamespace false

/-! ## The group setup (EC's `DLog` clone) -/

/-- A cyclic group `G` with generator `g` and exponent type `F` (EC's `group`/`exp`).
    Multiplication and exponentiation, what the programs genuinely need of the types — a default
    element (`Inhabited`, so local variables can be declared) and `Fintype F` (real content:
    `SubProbability.uniform` samples it, and the wp lemmas sum over it) — and the algebraic laws
    the proofs need, which are the three fields documented individually below.  Correctness needs
    none of the laws; they are all for `Hiding.lean`.

    Decidable equality is *not* a field.  `verify` does compare (`$c == $c'`), and `==` is `BEq`
    derived from `DecidableEq` — but these programs are never executed: every `proc` is
    `noncomputable` and the semantics is a measure, so the comparison only ever has to *denote* a
    `Bool`, not compute one.  `Classical.decEq` supplies that for free, which is why the instances
    below are classical and the class is two fields shorter.  Nothing in the proofs cares: they
    reason about `=`, and `beq_self_eq_true` and friends hold for any `DecidableEq` witness. -/
structure PedersenGroup where
  G : Type
  F : Type
  g : G
  -- TODO: Change to `[Mul G]`
  gmul : G → G → G
  -- TODO: Change to `[Pow G F]`
  gpow : G → F → G
  [g_inhabited : Inhabited G]
  -- TODO: Remove. Implied by CommRing F.
  [f_inhabited : Inhabited F]
  [f_fintype : Fintype F]
  /-- EC's exponent type is the prime field `DL.GP.ZModE`; the hiding proof forms `d + x * m`
      and its inverse `d - x * m`, so the additive group and the multiplication are both needed.
      (Only the ring structure is required — nothing here uses inverses.) -/
  [f_commring : CommRing F]
  /-- EC's `expD`: exponentiation turns addition into multiplication. -/
  gpow_add : ∀ (h : G) (a b : F), gpow h (a + b) = gmul (gpow h a) (gpow h b)
  /-- EC's `expM`: iterated exponentiation multiplies the exponents. -/
  gpow_mul : ∀ (h : G) (a b : F), gpow (gpow h a) b = gpow h (a * b)

-- namespace PedersenGroup

variable (group : PedersenGroup)

@[reducible] instance : Inhabited group.G := group.g_inhabited
@[reducible] noncomputable instance : DecidableEq group.G := Classical.decEq _
@[reducible] instance : Inhabited group.F := group.f_inhabited
@[reducible] instance : CommRing group.F := group.f_commring
@[reducible] noncomputable instance : DecidableEq group.F := Classical.decEq _
@[reducible] instance : Fintype group.F := group.f_fintype
@[reducible] instance : Mul group.G := ⟨group.gmul⟩
@[reducible] instance : Pow group.G group.F := ⟨group.gpow⟩

/-- `gpow_add` at the `^`/`*` notation.  The class fields have to be stated with the raw
    `gmul`/`gpow` (the instances below them do not exist yet), but every use site sees the
    notation, and `rw` matches on the notation's head — not the raw field. -/
theorem pow_add (h : group.G) (a b : group.F) : h ^ (a + b) = h ^ a * h ^ b := group.gpow_add h a b

/-- `gpow_mul` at the `^` notation. -/
theorem pow_mul (h : group.G) (a b : group.F) : (h ^ a) ^ b = h ^ (a * b) := group.gpow_mul h a b

-- end PedersenGroup

-- open PedersenGroup (G F g)


/-- EC's `PedersenTypes` + `clone Commitment with …`: value/commitment are group elements,
    message/openingkey are exponents. -/
/- Reducible on purpose.  It used to be an `instance`, which carries `@[reducible]` implicitly, and
the `wp_*` proofs below rely on it: they are stated at `group.types.Commitment` and worked on at
`group.G`, and every `simp` that has to see through that spelling needs the record to unfold at
`reducible` transparency.  A plain `def` leaves `programDenotation` stuck on the `.seq` of the
procedure's body. -/
@[reducible] def PedersenGroup.types : CommitmentTypes where
  Value := group.G
  Message := group.F
  Commitment := group.G
  OpeningKey := group.F
  value_inhabited := inferInstance
  message_inhabited := inferInstance
  commitment_inhabited := inferInstance
  openingKey_inhabited := inferInstance

variable [ProgramSpec]

/-! ## The scheme

EC's
```
module Pedersen : CommitmentScheme = {
  proc gen() : value                = { x <$ dt; h <- g ^ x; return h; }
  proc commit(h, m)                 = { d <$ dt; c <- (g ^ d) * (h ^ m); return (c, d); }
  proc verify(h, m, c, d)           = { c' <- (g ^ d) * (h ^ m); return (c = c'); }
}.
```
transcribes directly with the `module` command.  It declares, per procedure `f`, both the body
`Pedersen.f.procedure` and the module `Pedersen.f : Module.Proc …`, and assembles them into
`Pedersen : CommitmentScheme` with `CommitmentScheme.mk` (the field names match the moduletype's,
so the record constructor is used rather than a nest of `Module.pair`s).  `Pedersen` has no
module parameters, so it *is* the scheme — there is nothing to apply it to, and hence no
`Pedersen.apply_simp`. -/

module Pedersen : (CommitmentScheme group.types) {
  /- Sample a secret exponent, publish `h = g ^ x`. -/
  proc gen() : group.G {
    var x : group.F;
    var h : group.G;
    x <$ SubProbability.uniform;
    h <- group.g ^ $x;
    return $h
  };
  /- Commit to `m` under `h`: sample the opening key `d`, output `g ^ d * h ^ m`. -/
  proc commit(h : group.G, m : group.F) : (group.G × group.F) {
    var c : group.G;
    var d : group.F;
    d <$ SubProbability.uniform;
    c <- group.g ^ $d * $h ^ $m;
    return ($c, $d)
  };
  /- Recompute the commitment and compare. -/
  proc verify(h : group.G, m : group.F, c : group.G, d : group.F) : Bool {
    var c' : group.G;
    c' <- group.g ^ $d * $h ^ $m;
    return $c == $c'
  };
}

/-! ## Correctness

To *run* an applied functor module we extract its procedure: a normal closed module
expression of procedure type is a `.proc` node (`proc_type_is_proc` / `Module.procedure`,
now in `Language/Modules.lean`).

`Correctness group.types (Pedersen group)` β/δ-normalizes to `Correctness.main` with Pedersen's
procedures in the holes.  That reduction used to be done by hand here, by a `functorApp_procedure`
bridge lemma, a `functor_procedure` tactic, a `Pedersen_expression` record equation and a
`pedersenInst` naming the hole filling.  None of it is needed any more, and all of it is gone (see
the history of this file if you want it back): the `module`/`moduletype` commands emit `@[simp]`
`apply_simp` lemmas
and tag their accessors `@[module_accessor]`, and those do the whole reduction inline in
`pedersen_correctness`. -/

/-! ### Per-procedure wp lemmas (EC's `inline`+`auto` steps, done once per procedure)

All three are stated at the `group.types`-spelled signature the instantiated game carries,
not at `group.G`/`group.F`.  The two are definitionally equal, but `Eq` carries its type as an
index, so the spelling is what makes them the same proposition as the goal — see the ⚠ below. -/

theorem wp_gen (f : ProgramDenotation.Post State group.types.Value) :
    (procedureDenotation (sig := procsig () -> group.types.Value)
        (Pedersen.gen.procedure group) ()).wp f
      = fun st => ∑ x : group.F, f (group.g ^ x, st) / Fintype.card group.F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.gen.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoLocalVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.scopedL, ProcedureScope.localVarsL]

theorem wp_commit (args : group.G × group.F)
    (f : ProgramDenotation.Post State
      (group.types.Commitment × group.types.OpeningKey)) :
    (procedureDenotation
        (sig := procsig (group.types.Value, group.types.Message) ->
          (group.types.Commitment × group.types.OpeningKey))
        (Pedersen.commit.procedure group) args).wp f
      = fun st => ∑ x : group.F, f ((group.g ^ x * args.1 ^ args.2, x), st)
          / Fintype.card group.F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [PedersenGroup.types,
    Pedersen.commit.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoLocalVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.scopedL,
    ProcedureScope.paramsL, ProcedureScope.localVarsL]

theorem wp_verify (args : group.G × group.F × group.G × group.F)
    (f : ProgramDenotation.Post State Bool) :
    (procedureDenotation
        (sig := procsig (group.types.Value, group.types.Message,
          group.types.Commitment, group.types.OpeningKey) -> Bool)
        (Pedersen.verify.procedure group) args).wp f
      = fun st => f (args.2.2.1 == group.g ^ args.2.2.2 * args.1 ^ args.2.1, st) := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [PedersenGroup.types,
    Pedersen.verify.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoLocalVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.scopedL,
    ProcedureScope.paramsL, ProcedureScope.localVarsL]

/-! ### Reducing the applied functor

`Correctness.main.procedure.apply_simp` fills `Correctness.main`'s holes with the callees they
were made from — which, since `Correctness`'s body calls `S.gen`, are the moduletype *accessors*
`CommitmentScheme.gen Pedersen` and friends.  The `wp_*` lemmas above are stated at
`Pedersen.gen.procedure`, a separate definition the `module` command emits.  Adding
`module_accessor` (the simp set the accessors are tagged with), `Pedersen`, and the
`Module.procedure_proc'` round-trip to the main `simp` call is all it takes to close that gap.  So
the whole reduction is the commands' own lemmas plus one `simp` set: no bridge lemma, no
hand-written hole instantiation, nothing declared for the purpose.

(`Module.procedure_proc'`, with the prime, is the one to name: the unprimed
`Module.procedure_proc` states the round-trip with `Module.proc` already unfolded, as
`(ModuleExpression.proc p).toModule (.proc p)`, and so never fires against the folded `Module.proc`
that `X.<f>.apply_simp` emits — before the primed companion existed, every caller had to unfold
`Module.proc` alongside it.)

⚠ One thing to know before touching this: `CommitmentScheme.gen Pedersen` and `Pedersen.gen`
**both print as `Pedersen.gen`** (dot-notation collision) and are *not* defeq — the accessor is a
chain of `Module.fst'`/`Module.snd'` through `Pedersen`'s expression.  So a lemma or rewrite
aimed at the wrong one of the two fails with the two sides displaying identically, or with "did
not find an occurrence of the pattern" against a goal in which the pattern is apparently right
there.  `set_option pp.explicit true` is what tells them apart.  A second, similar trap: signature
spellings must be `group.types.*`, not `group.G`/`group.F` — those are defeq, but `Eq` carries its
type as an index, so the two are *different propositions* and `exact` rejects the mismatch, again
printing identically (`convert … using 2` exposes that one).  The `wp_*` lemmas above are spelled
`group.types.*` for exactly this reason.

A third, from `PedersenGroup.types` being `@[reducible]`: `simp` files a lemma under the
discrimination key of its *statement*, and indexes the goal with `group.types.Message` already
reduced to `group.F`, so a lemma stated over an abstract `types` — every `apply_simp` the `module`
command emits — used to be looked up under a key the goal no longer had, and silently did not fire
("This simp argument is unused").  The commands now keep those positions out of the key with
`no_index` (see "Keeping the generated `@[simp]` lemmas findable" in `Syntax/ModuleSyntax.lean`), so
the lemmas are found at a reducible instantiation too: `pedersen_correctness2` below reduces the
whole applied functor with a single `simp`.

`pedersen_correctness` still reduces it by `rw`, for a different reason: reaching the goal through
the `suffices` leaves it type-incorrect at the `instances` transparency simp works at (`m :
group.F` where `(procsig (group.F) → Bool).ParamType` is expected), and simp then declines.  `rw`
unifies at default transparency and is unaffected. -/

set_option linter.flexible false in
/-- **Correctness of Pedersen** — EC's
    `hoare[Correctness(Pedersen).main : true ==> res]`: from any initial state, the
    correctness game never returns `false`. -/
theorem pedersen_correctness (m : group.F) (σ : State) :
    (procedureDenotation
        (Module.app (Correctness group.types) (Pedersen group)).main.procedure m σ).ofEvent
      {r : Bool × State | r.1 = false} = 0 := by
  -- reduce `ofEvent` to a `wp` with the indicator postcondition.  Done *before* the module
  -- reduction, so nothing here ever has to name the reduced procedure.
  suffices h : (procedureDenotation
      (Module.app (Correctness group.types) (Pedersen group)).main.procedure m).wp
      (({r : Bool × State | r.1 = false}).indicator fun _ => 1) σ = 0 by
    have hi := expectation_indicator
      (procedureDenotation
        (Module.app (Correctness group.types) (Pedersen group)).main.procedure m σ)
      {r : Bool × State | r.1 = false} 1
    rw [one_mul] at hi
    exact_mod_cast hi.symm.trans h
  -- β/δ-reduce the applied functor down to `Correctness.main`'s body with Pedersen's three
  -- procedures in the holes — the `module`/`moduletype` commands' own `@[simp]` lemmas do all of
  -- it.  `rw` rather than `simp` here: the goal the `suffices` above leaves is not type-correct at
  -- the `instances` transparency simp works at, and simp declines to rewrite in it (see the ⚠
  -- above); `rw` unifies at default transparency instead.
  rw [Correctness.apply_simp]
  -- read `main` back off the record `Correctness.apply_simp` builds — the `moduletype` command's
  -- own `@[simp]` lemma for the accessor
  simp only [CorrectnessT.main.mk_simp]
  rw [Correctness.main.apply_simp, Correctness.main.procedure.apply_simp]
  simp only [Module.procedure_proc']
  -- unfold the game and push `wp` through.  Kept as `rw`, not folded into the `simp only` above:
  -- as simp lemmas these two also fire on the *callees*, and `wp_gen` then no longer matches.
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  simp [module_accessor, Pedersen, Module.procedure_proc', programDenotation,
    StmtWithHoles.call, wp_bind, wp_get_g, wp_set_g, wp_zoom,
    ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoLocalVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.scopedL, ProcedureState.globalL,
    ProcedureScope.paramsL, ProcedureScope.localVarsL,
    Set.indicator, Set.mem_setOf_eq]
  -- descend through the two samplings with `rw` (full-defeq unification), summand by summand
  rw [wp_gen]
  refine Finset.sum_eq_zero fun x _ => ENNReal.div_eq_zero_iff.mpr (Or.inl ?_)
  rw [wp_commit]
  refine Finset.sum_eq_zero fun d _ => ENNReal.div_eq_zero_iff.mpr (Or.inl ?_)
  rw [wp_verify]
  -- `Lens.pair`: the game stores `commit`'s result through the tuple l-value `c, d <- …`, so
  -- the final read has to compute back through that pair lens.
  simp [Lens.pair]

omit [ProgramSpec] in
-- TODO Maybe delete (unused)
/-- An event of null points is null.  No `[Countable α]`: `μ.2.2` is the discreteness invariant
    `μ A = ∑_{x ∈ A} μ {x}`, so the sum over `E` is a `tsum` of zeroes whatever the cardinality. -/
lemma _root_.GaudisCrypt.SubProbability.ofEvent0I {μ : SubProbability α} :
    (∀ x ∈ E, μ x = 0) → μ.ofEvent E = 0 := by
  intro h
  -- `ofEvent` is `toNNReal` of the measure, and the measure is finite (`≤ 1`), so the two
  -- vanish together
  have hzero : ∀ s : Set α, μ.ofEvent s = 0 ↔ μ.1 s = 0 := fun s => by
    rw [SubProbability.ofEvent, ENNReal.toNNReal_eq_zero_iff]
    exact or_iff_left
      (((MeasureTheory.measure_mono (Set.subset_univ s)).trans μ.2.1).trans_lt
        ENNReal.one_lt_top).ne
  rw [hzero, μ.2.2 E, ENNReal.tsum_eq_zero]
  exact fun x => (hzero {(x : α)}).mp (h x x.2)

section UnfinitedExperimentsByDominique

def hoare (A : ProcedureState l → Prop) (p : Stmt l) (B : ProcedureState l → Prop) :=
  ∀ σ, A σ → (programDenotation p σ).ofEvent (fun (_, σ') => ¬ B σ') = 0

#print HoleSigs.Instantiation

/-- A Hoare triple for a whole procedure whose postcondition may mention the procedure's
    *internal* state — its parameters and local variables — and not only the return value and the
    globals.

    Reduced to `hoare` on the body.  The body's state is a `ProcedureState`, so the precondition
    `hoare` gets says: the global half satisfies `A args`, and the local half is exactly the scope
    the call would set up, `sig.localVariableInit p.locals args`.  The postcondition applies `B` to
    the value `p.return_val` reads off the final state and to that final state itself — which is
    where the extra information over an ordinary triple comes from, since the final state still has
    the locals in it (`procedureDenotation` projects them away with `.global`).

    Note the argument order: `p` comes before `B` because `B`'s domain mentions `p.locals`.
    Polarity is inherited from `hoare`: `B` has to hold almost surely, i.e. the event `¬ B` has
    mass `0`. -/
def hoareProc' {sig} (A : sig.ParamType → State → Prop) (p : Procedure sig)
    (B : sig.ret → ProcedureState (sig.ProcedureScope p.locals) → Prop) :=
  ∀ args : sig.ParamType,
    hoare (fun σ => A args σ.global ∧ σ.locals = sig.localVariableInit p.locals args)
      p.body (fun σ => B (p.return_val.get σ) σ)

def hoareProc {sig} (A : sig.ParamType → State → Prop) (p : Procedure sig) (B : sig.ret → State → Prop) :=
  ∀ args σ, A args σ → (procedureDenotation p args σ).ofEvent (fun (ret, σ') => B ret σ') = 0

/-- `hoareProc` is the special case of `hoareProc'` in which the postcondition ignores the locals.

    Two adjustments turn one `B` into the other, and both are forced.  Polarity: `hoareProc`'s `B`
    names the event that must *not* happen, `hoareProc'` inherits `hoare`'s convention that `B` must
    hold almost surely — hence the `¬`.  Domain: `hoareProc'` offers the whole final
    `ProcedureState`, so the globals-only `B` is read off it with `.global`, and the locals are
    dropped — which is what `procedureDenotation` does to them anyway.  That is why this is an
    equivalence and `hoareProc'_imp_hoareProc` below, for a `B` that does look at the locals, is
    only an implication. -/
lemma hoareProc_iff_hoareProc' {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B : sig.ret → State → Prop} :
    hoareProc A p B ↔ hoareProc' A p (fun r σ => ¬ B r σ.global) := by
  -- `ofEvent E = 0` and `expected (indicator E 1) = 0` are the same statement; working with
  -- `expected` lets `wp_procWrap` do the rest.
  have ofEvent_iff : ∀ {α : Type} (μ : SubProbability α) (E : Set α),
      μ.ofEvent E = 0 ↔ μ.expected (E.indicator fun _ => 1) = 0 := fun μ E => by
    rw [expectation_indicator, one_mul, ENNReal.coe_eq_zero]
  -- the procedure's distribution is the body's, pushed along `τ ↦ (return_val.get τ, τ.global)`
  have key : ∀ (args : sig.ParamType) (σ : State) (F : ProgramDenotation.Post State sig.ret),
      (procedureDenotation p args σ).expected F
        = (programDenotation p.body ⟨σ, sig.localVariableInit p.locals args⟩).expected
            (fun q => F (p.return_val.get q.2, q.2.global)) := by
    intro args σ F
    change (procedureDenotation p args).wp F σ = _
    rw [procedureDenotation_eq_procWrap, wp_procWrap]
    rfl
  -- the two events are each other's image/preimage under that push-forward, so the masses agree
  have iff0 : ∀ (args : sig.ParamType) (σ : State),
      (procedureDenotation p args σ).ofEvent (fun (ret, σ') => B ret σ') = 0
        ↔ (programDenotation p.body ⟨σ, sig.localVariableInit p.locals args⟩).ofEvent
            (fun (_, τ) => ¬ ¬ B (p.return_val.get τ) τ.global) = 0 := by
    intro args σ
    have hfun : (fun q : Unit × ProcedureState (sig.ProcedureScope p.locals) =>
        Set.indicator (fun (ret, σ') => B ret σ') (fun _ => (1 : ENNReal))
          (p.return_val.get q.2, q.2.global))
        = Set.indicator (fun (_, τ) => ¬ ¬ B (p.return_val.get τ) τ.global)
            (fun _ => (1 : ENNReal)) := by
      -- drop the double negation, after which the two events are the same event, one written on
      -- the body's states and one on the pushed-forward pairs — `rfl` up to `Set.indicator`
      have hnn : ((fun (_, τ) => ¬ ¬ B (p.return_val.get τ) τ.global) :
            Set (Unit × ProcedureState (sig.ProcedureScope p.locals)))
          = fun q => B (p.return_val.get q.2) q.2.global := by
        funext q
        simp
      rw [hnn]
      rfl
    rw [ofEvent_iff, ofEvent_iff, key, hfun]
  constructor
  · intro h args σ hσ
    obtain ⟨hA, hloc⟩ := hσ
    -- the precondition pins the local half, and `⟨σ.global, σ.locals⟩` is `σ` by structure eta
    have hσ' : σ = ⟨σ.global, sig.localVariableInit p.locals args⟩ := by rw [← hloc]
    rw [hσ']
    exact (iff0 args σ.global).mp (h args σ.global hA)
  · intro h args σ hA
    exact (iff0 args σ).mpr (h args ⟨σ, sig.localVariableInit p.locals args⟩ ⟨hA, rfl⟩)

omit [ProgramSpec] in
/-- A subset of a null event is null.  (`ofEvent` is `toNNReal` of the measure, and the measure is
    finite — bounded by `1` — so the two vanish together, which is what lets
    `measure_mono_null` be used through the `toNNReal`.) -/
lemma _root_.GaudisCrypt.SubProbability.ofEvent_eq_zero_of_subset {α : Type u}
    {μ : SubProbability α} {E₁ E₂ : Set α} (hsub : E₁ ⊆ E₂) (h : μ.ofEvent E₂ = 0) :
    μ.ofEvent E₁ = 0 := by
  have hzero : ∀ s : Set α, μ.ofEvent s = 0 ↔ μ.1 s = 0 := fun s => by
    rw [SubProbability.ofEvent, ENNReal.toNNReal_eq_zero_iff]
    exact or_iff_left
      (((MeasureTheory.measure_mono (Set.subset_univ s)).trans μ.2.1).trans_lt
        ENNReal.one_lt_top).ne
  rw [hzero] at h ⊢
  exact MeasureTheory.measure_mono_null hsub h

/-- `hoare` is monotone in its postcondition: a weaker `B` is a weaker triple, because the null
    event `¬ B` only shrinks. -/
lemma hoare_mono {l} {A : ProcedureState l → Prop} {p : Stmt l}
    {B₁ B₂ : ProcedureState l → Prop} (hB : ∀ σ, B₁ σ → B₂ σ) (h : hoare A p B₁) :
    hoare A p B₂ := by
  intro σ hA
  refine SubProbability.ofEvent_eq_zero_of_subset ?_ (h σ hA)
  intro q hq hb
  exact hq (hB _ hb)

/-- `hoareProc'` inherits that monotonicity, postcondition by postcondition. -/
lemma hoareProc'_mono {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B₁ B₂ : sig.ret → ProcedureState (sig.ProcedureScope p.locals) → Prop}
    (hB : ∀ r σ, B₁ r σ → B₂ r σ) (h : hoareProc' A p B₁) : hoareProc' A p B₂ :=
  fun args => hoare_mono (fun _ hb => hB _ _ hb) (h args)

/-- The observable content of a `hoareProc'` triple, in `hoareProc` form: what survives the call is
    that the *bad* event — the outcomes for which `B` fails whatever the final scope was — is null.

    An implication, and not an equivalence like `hoareProc_iff_hoareProc'`, which is not a
    shortcoming of the proof.  `procedureDenotation` hands back `(return value, globals)`; the final
    scope is projected away with `.global`, so the locals `B` may talk about are not observable in a
    `hoareProc` at all.  The `∀ l` is the strongest observable consequence, and the converse fails:
    take a body that samples a local `x : Bool` and `B r σ := σ.locals.x = true`.  The bad event is
    then empty — no `σ'` has *every* scope satisfying `B` — so the `hoareProc` holds, while the
    `hoareProc'` is false, the body putting mass `1/2` on `¬ B`.  Replacing `∀ l` by `∃ l` turns the
    implication around and is equally not an equivalence.

    For an actual equivalence, either restrict to a `B` that only reads the globals — that is
    `hoareProc_iff_hoareProc'` — or have the procedure return its own scope, so that the locals
    become observable.

    Proof: `hoareProc_iff_hoareProc'` turns the goal into a `hoareProc'` triple with postcondition
    `¬ ∀ l, ¬ B r ⟨σ.global, l⟩`, which is weaker than `B` — instantiate the `∀ l` at the scope in
    hand, `σ.locals` — so `hoareProc'_mono` closes it. -/
lemma hoareProc'_imp_hoareProc {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B : sig.ret → ProcedureState (sig.ProcedureScope p.locals) → Prop}
    (h : hoareProc' A p B) : hoareProc A p (fun ret σ => ∀ l, ¬ B ret ⟨σ, l⟩) :=
  hoareProc_iff_hoareProc'.mpr (hoareProc'_mono (fun _ σ hb hc => hc σ.locals hb) h)

/-- A single point's mass as a `wp`: the postcondition that picks out `x` is the indicator of
    `{x}`, and `expectation_indicator` at `c = 1` identifies the two. -/
-- TODO rename and move to suitable file? Or drop and just use `hoare`?
lemma tmp {sig m σ E} {p : Procedure sig} :
  (procedureDenotation p m).wp (Set.indicator E fun _ => 1) σ = 0 →
  (procedureDenotation p m σ).ofEvent E = 0
  := by
  intro h
  simp only [ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero] at h
  exact h

/-- `tmp` at the level of a whole triple: to prove a `hoareProc`, it is enough to kill the `wp` of
    the bad event's indicator from every state the precondition admits.  `apply` it to a `hoareProc`
    goal and what is left is the `wp` calculation the `wp_*` lemmas do.

    One-directional for the same reason `tmp` is — nothing here needs the converse, though it holds
    (`expectation_indicator` is an equation, and the `ENNReal`/`NNReal` coercion reflects `0`). -/
lemma hoareProc_of_wp {sig} {A : sig.ParamType → State → Prop} {p : Procedure sig}
    {B : sig.ret → State → Prop}
    (h : ∀ args σ, A args σ →
      (procedureDenotation p args).wp
        (Set.indicator {r | B r.1 r.2} fun _ => 1) σ = 0) :
    hoareProc A p B :=
  fun args σ hA => tmp (h args σ hA)

-- TODO: Concrete syntax for Module.app. Either a special infix symbol, or a coercion that allows M(A,B).

theorem pedersen_correctness2 :
    hoareProc (fun _ _ => True)
      (Module.app (Correctness group.types) (Pedersen group)).main.procedure
      (fun r _ => r = false) := by
  apply hoareProc_of_wp
  intro args σ
  -- Inlining everything (should be a tactic)
  simp
  -- TODO: why does this not use proc syntax?
  simp only [Correctness.main.procedure.apply_simp]
  simp
  simp only [Pedersen]
  simp
  simp only [Pedersen.commit.procedure]
  simp only [Pedersen.gen.procedure]
  simp only [Pedersen.verify.procedure]
  simp

  -- Doing wp calculus
  simp only [procedureDenotation_eq_procWrap]
  rw [wp_procWrap]
  simp only [programDenotation]
  simp only [StmtWithHoles.call]
  simp only [StmtWithHoles.assign]
  simp only [wp_bind]
  simp only [programDenotation]
  simp only [procedureDenotation_eq_procWrap]
  simp only [wp_bind]
  simp only [wp_get_g]
  simp only [wp_zoom]
  simp only [wp_set_g]
  simp only [AsGetter.toG]
  simp only [id_eq]
  rw [wp_procWrap]
  simp only [programDenotation]
  simp only [wp_bind]
  simp only [wp_get_g]
  simp only [wp_set_g]
  simp only [wp_lift]
  simp only [AsGetter.toG]
  simp only [id_eq]
  simp only [uniform_expected]
  simp only [expected_pure]
  simp only [ProcedureSignature.localVariableInit]
  -- `args` still carries the `group.types.Message` spelling of its type, which blocks every
  -- further `simp` (the goal is then not type-correct at `instances` transparency); unfolding
  -- `ParamType` in the hypothesis puts it in the tuple form the goal expects
  simp only [ProcedureSignature.ParamType] at args
  simp only [Set.indicator]
  simp only [Set.mem_setOf_eq]
  -- Stalls here: the `commit` and `verify` calls' `procWrap`s sit under the `fun as' ↦ …` binders
  -- `wp_bind` introduced, so `rw [wp_procWrap]` cannot reach them, and `simp only [wp_procWrap]`
  -- refuses because the goal is no longer type-correct at `instances` transparency (`Set` vs
  -- `_ → Prop`, `Stmt` vs `StmtWithHoles .empty`, `ParamType` vs the tuple — all plain `def`s).
  sorry

end UnfinitedExperimentsByDominique

end GaudisCrypt.Examples.Pedersen
