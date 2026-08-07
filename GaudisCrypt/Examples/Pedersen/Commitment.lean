import GaudisCrypt.Language.Syntax2

/-!
# Generic commitment schemes

A transliteration of EasyCrypt's `theories/crypto/Commitment.ec` (theory
`CommitmentProtocol`) into the Gaudí module/procedure syntax.

* EC's abstract theory types `value`, `message`, `commitment`, `openingkey` become the
  type class `CommitmentTypes` (instance-implicit section parameters, so the
  `moduletype`-generated definitions elaborate — the same pattern as `[ProgramSpec]`).
* EC `module type`s become `moduletype`s.
* EC's parameterized modules (`Correctness(S)`, `HidingExperiment(S,U)`,
  `BindingExperiment(S,B)`) become `module X (P : T) { … }` declarations: the calls are written
  against the parameters' own fields and the holes are inferred from them.
-/

namespace GaudisCrypt.Examples.Pedersen

/-

Dominique's TODOs.  Status re-checked against the code 2026-08-07 (after the untyped-calculus
refactor + the `module` command); each entry below was verified, not assumed.

Done since the list was written:
- [X] class IsModule, and instances for it
- [X] `→ₘ` is `Type → Type → Type` via the instance
      (`Module.Arr (M N : Type _) [IsModule M] [IsModule N]`, Modules.lean)
- [X] `moduletype X` also defines `X.typeRep` …
- [X] … and emits `instance IsModule X` itself (Syntax2.lean) — so a hand-written
      `instance : IsModule CommitmentScheme` here is now redundant and has been removed
- [X] `module A(params) : X { ... }` syntax, `(params)` optional — used by `Correctness` below
      and by `Pedersen` in `Pedersen.lean`

Abandoned:
- `rename ModuleTypeRep -> ModuleTypeRepRep` was ticked, but no `ModuleTypeRepRep` exists
  anywhere; the type is still `ModuleTypeRep`.  Reading it as dropped rather than pending.
  (The related note "no pretty syntax for it" *is* the current state, and is documented at
  its source in Syntax2.lean: `ModuleTypeRep`'s constructors stay `.arr`/`.prod`/`.unit`.)

Still open:
- Maybe also support `let A := module ...` or `def A := module ...`
- `DoesNotUse A X.op` (in a proof, do induction, derive ⊥ from a use of `X.op`) — nothing of
  the sort exists yet.
-/

open GaudisCrypt


/-- The abstract types of EC's `theory CommitmentProtocol`: the public value (key), the
    message space, commitments, and opening keys.  `Inhabited` is needed for program
    local variables of these types — that one is real content (a default value has to *exist*).

    There is deliberately **no** `DecidableEq` here.  It was a field (`message_deceq`), justified
    by EC's binding experiment comparing `m ≠ m'`, but decidability is never needed for *proofs* —
    only to form a `Bool`-valued program expression via `BEq` — and no program in this development
    compares messages, so nothing consumed it.  (`Commitment` never had one either, and that has
    never been missed.)  When `BindingExperiment` does need `m ≠ m'`, note that these programs are
    never executed — the semantics is a measure and every `proc` is `noncomputable` — so
    `Classical.decEq` at the point of use is enough; a class field buys nothing.  See
    `Lib/RO/CollisionResistance.lean`, which does exactly that. -/
class CommitmentTypes where
  Value : Type
  Message : Type
  Commitment : Type
  OpeningKey : Type
  -- Local variables need a default: `localDefaults` (Language/Programs.lean) takes
  -- `List (Σ t : Type, Inhabited t)` and projects `.default`, so `Inhabited`-as-data is what the
  -- *language* demands, not a choice made here.
  --
  -- TODO "change to Nonempty": tried 2026-08-07 — it does work (carry `Nonempty`, derive
  -- `Inhabited` via `Classical.inhabited_of_nonempty`; whole build passes).  Reverted, because:
  --  (1) it removes nothing — the DSL still needs the data, so it only relabels who supplies the
  --      witness: same field count, plus four indirections;
  --  (2) unlike `Decidable`, `Inhabited` is *not* a subsingleton, so the classical default is not
  --      a different-but-equal witness, it is potentially a different *element*, with no
  --      `Subsingleton.elim` to bridge it — harmless only while every local is written before
  --      it is read, which the types do not enforce.
  -- If it is worth doing, the place is `localDefaults` itself: have locals require `Nonempty` and
  -- take the default classically *once*, so every downstream class benefits and `PedersenGroup`
  -- does not end up inconsistent with this one.
  --
  -- TODO  Use individual [Nonempty types.Value] etc. instead of NonEmptyCommitmentTypes
  -- (that separate-class approach is the one sketched, and rejected, in the DON'T DO block below)
  value_inhabited : Inhabited Value
  message_inhabited : Inhabited Message
  commitment_inhabited : Inhabited Commitment
  openingKey_inhabited : Inhabited OpeningKey



-- TODO Make CommitmentTypes into a structure
-- variable (types : CommitmentTypes) in the section
-- ⚠ This looks blocked, not merely pending: the class form is *forced*, because the
-- `moduletype`-generated definitions only re-resolve instance-implicit section parameters (the
-- same reason `[ProgramSpec]` is a class).  A plain `variable (types : CommitmentTypes)` would
-- not reach them.  Worth confirming before spending time on it.

/- DON'T DO:

class NonEmptyCommitmentTypes (types : CommitmentTypes) where
  nonempty_value : Nonempty types.Value
  nonempty_message : Nonempty types.Message
  nonempty_commitment : Nonempty types.Commitment
  nonempty_openingKey : Nonempty types.OpeningKey

  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Value := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Message := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Commitment := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.OpeningKey := sorry

instance (t : CommitmentTypes) [Nonempty t.Value] [Nonempty t.Message] [Nonempty t.Commitment]
[Nonempty t.OpeningKey] : NonEmptyCommitmentTypes t :=
sorry

  variable (types : CommitmentTypes)
  variable [NonEmptyCommitmentTypes types]
-/


instance [CommitmentTypes] : Inhabited CommitmentTypes.Value :=
  CommitmentTypes.value_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.Message :=
  CommitmentTypes.message_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.Commitment :=
  CommitmentTypes.commitment_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.OpeningKey :=
  CommitmentTypes.openingKey_inhabited

/-! ### Disjointness of tuple-projection lenses

The `proc` macro binds each local variable to a `Lens.id.ofst/.osnd` projection chain into
the local-state tuple; tuple *assignment* (`c, d <- …`) pairs those lenses via `Lens.pair`,
which needs them `disjoint`.  Distinct projection paths are always disjoint, and the instances
deriving that (`Lens.disjoint_ofst_osnd`, `Lens.disjoint_chain`, …) now live in
`Language/Lens.lean` — the "move them to the proper place" TODO that used to sit here is done,
and they are no longer declared in this file.

⚠ They still do **not** make tuple assignment of *locals* work (re-tested 2026-08-07): the macro
binds locals as `let`-variables, and instance search does not unfold local `let`s, so
`disjoint c d` is searched at the opaque variables and never reaches these instances —
`c, d <- call commit (…)` fails with `failed to synthesize instance of type class disjoint c d`.
Until the macro binds locals differently (or registers the disjointness facts itself), the
experiments below use pair-typed locals and `$`-projections instead of tuple assignment. -/

-- TODO: changes to named variable if CommitmentTypes becomes a structure (but see the
-- ⚠ above: that may be blocked)
variable [ProgramSpec] [CommitmentTypes]

-- With structure, replace by `local(?) abbrev Value := CommitmentTypes.Value types` etc.
-- and remove the `open` below
open CommitmentTypes (Value Message Commitment OpeningKey)

/-! ## Module types

```
module type CommitmentScheme = {
  proc gen() : value
  proc commit(x: value, m: message) : commitment * openingkey
  proc verify(x: value, m: message, c: commitment, d: openingkey) : bool
}.
``` -/

moduletype CommitmentScheme {
  proc gen () -> Value;
  proc commit (Value, Message) -> Commitment × OpeningKey;
  proc verify (Value, Message, Commitment, OpeningKey) -> Bool;
}

-- EC's `Unhider`: the hiding-game adversary.
moduletype Unhider {
  proc choose (Value) -> Message × Message;
  proc guess (Commitment) -> Bool;
}

-- EC's `Binder`: the binding-game adversary.
moduletype Binder {
  proc bind (Value) -> Commitment × Message × OpeningKey × Message × OpeningKey;
}

/- The naming question that used to be deliberated here ("what do we call the underlying
`ModuleTypeRep`, and what the `Module` over it?") is settled by what `moduletype` generates:
the type is `CommitmentScheme` and its representation is `CommitmentScheme.typeRep`.  A
hand-written `CommitmentSchemeT` is no longer needed; the `example` below records the bridge. -/
example : CommitmentScheme = Module CommitmentScheme.typeRep := rfl

/-! ## Experiments (parameterized modules)

Each EC functor becomes a `module X (P : T) { … }` declaration.  The command builds what used to
be written out by hand here: a procedure with holes — the holes being the parameter modules'
procedures, discovered from the call sites — wrapped in a `ModuleExpression.abs` whose body
repackages the parameter record (declaration order, no unit) into the holes tuple (reverse
order, `.unit`-terminated) with `fst`/`snd`/`pair`. -/



/- EC's `module Correctness (S : CommitmentScheme) = { proc main(m) = { … } }` — the module
command takes the parameter directly, so the calls are written against `S`'s own fields and the
holes are inferred from them.

(A `/-- … -/` docstring cannot be attached: the `module` command does not accept one, same gap
as `moduletype`.)

That replaces the hand-written functor this used to be: a `proc … uses (gen, commit, verify)`
body plus an explicit `ModuleExpression.abs` wrapping a `.pair`/`.fst`/`.snd` adapter that
repackaged the scheme record into the holes tuple.  The command derives exactly that adapter —
`(.var 0).snd.snd` for `verify`, `.snd.fst` for `commit`, `.fst` for `gen`, right-nested and
reversed — from the call sites, so the two really are the same term; it just is not written out
by hand any more (which is what Dominique's TODO at the bottom of `Syntax2.lean` was asking for).

It declares `Correctness.main.procedure` (the body, with its holes), `Correctness.main` (that
procedure as a functor of `S`), `Correctness` itself, and `Correctness.apply_simp`. -/
module Correctness (S : CommitmentScheme) {
  proc main(m : Message) : Bool {
    var x : Value;
    var cd : Commitment × OpeningKey;
    var b : Bool;
    x <- call S.gen ();
    cd <- call S.commit ($x, $m);
    b <- call S.verify ($x, $m, ($cd).1, ($cd).2);
    return $b
  };
}

/-- `Correctness(S)` elaborates: the functor applies to any `S : CommitmentScheme`. -/
noncomputable example (S : CommitmentScheme) : Module (procmod (Message) -> Bool) :=
  Module.app Correctness S


end GaudisCrypt.Examples.Pedersen
