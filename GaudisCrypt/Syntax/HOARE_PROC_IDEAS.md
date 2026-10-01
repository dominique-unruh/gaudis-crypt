Now add concrete syntax `hoare[ P ==> Q ] ( module-term )` (where M := module-term is the same syntax as in, e.g., call-locations in proc's in modules). 

This should translate to `hoareProc P' M' Q'` where:

M' is basically M, possibly M.procedure (if needed)

P' is parsed with local let binders for the parameters of M'. So that I can use $x to refer to the getter applied to the param $x of the proc. Also `params` is parsed as meaning all the parameters (i.e., simply a getter into to the params), so $params will evaluate to the parameters without needing the local names.
At the same time $y for a global y should also work.

Q' is parsed with a local let binder for `res`, referring to the result, so I can use $res (and $y for global y).

Where should this know the names of the proc from? It should only work when the module expression has a concrete MT.procname in it where MT is a module type defined by `moduletype`. So we use the parameter names defined there.

However, `moduletype` does not define parameter names. So we need to change the syntax of `moduletype` first to actually use `proc f(x: type, y: type)...` not `proc f(type, type)...`. This syntax should also be allowed for plain procsig, procmod (though it is irrelevant there since the names are ignored), but there optional.

`moduletype` needs to store these names somewhere so that parsers and tactics can access them. Maybe as metadata of `MT.procname`?

---

# Analysis

Written for: whoever implements this (you or a future contributor); assumes the `ProgramSyntax`/`ModuleSyntax` internals.

## Summary of opinion

The feature is worth having, and most of it is cheap. But the plan as written front-loads
the *expensive and invasive* part (named parameters in `moduletype`, plus a new metadata
channel) to buy a *convenience* (writing `$x` instead of naming the parameters at the triple).
I would cut it into three independent steps and ship them in this order:

1. **`hoare[ M (x, m) : P ==> Q ]`, with the parameter names written at the triple site.** No
   `moduletype` change, no metadata, no attribute. Covers every module expression, abstract or
   concrete.
2. **Names recovered from a concrete procedure term.** Free for `proc`-literals and
   `module`-declared procedures; the names are already in the elaborated term (see below).
3. **Names from `moduletype` declarations.** The invasive step; only needed for an *abstract*
   module of a declared module type — which admittedly is the interesting case for a
   scheme-generic theorem, so it does eventually pay for itself.

Details, and the problems each step runs into, below.

## 1. What `hoareProc` actually asks for

```lean
def hoareProc {sig} (A : sig.ParamType → State → Prop) (p : Procedure sig)
    (B : sig.ret → State → Prop)
```

Note what this does **not** say:

* The pre/postcondition see `State` (globals) and their own argument, not a `ProcedureState`.
  `GaudiExpr[ ]` always reads from a `ProcedureState S` (that is `CurrentState`'s field type),
  so the notation installs one — at `S := Unit`, see below — rather than bending either side.
* **The postcondition cannot mention the parameters at all**, and that stays so (decision 1 in
  §7). It is a definitional choice in `Logic/Hoare.lean`, not something the syntax could paper
  over: a property relating the result to an argument is not a `hoareProc` triple and must be
  stated another way (save the argument into a global, or use a relational judgment). EasyCrypt
  imposes the same restriction. The notation therefore binds `res` and the globals in the
  postcondition, and the parameter names only in the precondition.

### The conditions are plain lambdas — no combinator, no packing

Target `hoareProc` directly, with each condition a lambda of exactly the shape it asks for.
The elaborator writes no types at all: the binders take theirs from `hoareProc`'s expected
argument type, so `sig` is never named in generated syntax — which was the one thing that
looked as though it needed a helper definition.

For `hoare[ M (x, m) : P ==> Q ]`:

```lean
hoareProc
  (fun args σ =>
    letI : CurrentState Unit := ⟨⟨σ, ()⟩⟩
    let x := Getter.mk fun _ => Lens.get ‹slot 0 of 2› args
    let m := Getter.mk fun _ => Lens.get ‹slot 1 of 2› args
    let params := Getter.mk fun _ => args
    ⟪P⟫)
  (Module.Proc.procedure M)
  (fun res σ =>
    letI : CurrentState Unit := ⟨⟨σ, ()⟩⟩
    let res := Getter.mk fun _ => res
    ⟪Q⟫)
```

Why each piece:

* **Carrier `ProcedureState Unit`.**  `GaudiExpr`'s ambient state is a `ProcedureState S`
  (`CurrentState.state : ProcedureState S`, `ExpressionSyntax.lean`), so a condition that wants
  the same `§`/`$` sigil as a statement body has to install one.  `Unit` locals is the smallest
  choice, mentions no `sig`, and is writable with zero knowledge — `⟨σ, ()⟩` needs at most the
  closed ascription `ProcedureState Unit`.  A global `y : Lens Int State` then reads through the
  existing `Evaluatable S (Lens T State) T` instance, and there are no locals, which is right.
  **No `ProcedureScope`, hence no `⟨σ, ⟨args, ()⟩⟩` and no result-as-parameter pun.**
* **Parameters are constant getters, read with the sigil** — `§x`, not bare `x`.  One spelling
  for every variable, so a condition can be lifted out of a procedure body unchanged, and
  anything processing triples mechanically sees the same `eval`-shaped read throughout.
* **The slot is the *same lens chain* the body uses.**  `proc` binds its `k`-th parameter to
  `Lens.intoParams $slot` with `slot = ProgramSyntax.mkChain (ProgramSyntax.navSteps k np)`; the
  triple emits that identical `$slot` and applies it, `Lens.get $slot args`.  So a parameter
  getter in a triple and the parameter lens in the body are visibly the same navigation, which
  is what lets a tactic match one against the other instead of having to know two unrelated
  encodings.  Both helpers are already public for `HoareSyntax.lean`.
* **`$params` is a constant getter onto `args`** itself, and **`$res`** onto the result binder.
  Neither is special; both are the degenerate case of the above.

Nothing here needs a new definition in `Logic/Hoare.lean`, a new instance in
`ExpressionSyntax.lean`, or a type reconstructed from an elaborated `sig`.  The elaborator
needs `sig` for exactly two things: the **arity**, to know how many slots to emit, and the
check that a written binder list matches it.

### Rejected: a `Getter`-valued combinator

For the record, since it shaped the earlier draft.  Elaborating the conditions over
`ProcedureState (ProcedureScope sig.params [])` and `ProcedureState (ProcedureScope [sig.ret]
[])` also works, with

```lean
def hoareProcG {sig} (p : Procedure sig)
    (A : Getter Prop (ProcedureState (ProcedureScope sig.params [])))
    (B : Getter Prop (ProcedureState (ProcedureScope [sig.ret] []))) : Prop :=
  hoareProc (fun args σ => A.get ⟨σ, ⟨args, ()⟩⟩) p (fun r σ => B.get ⟨σ, ⟨r, ()⟩⟩)
```

so that `sig` flows from `p` into the carrier by unification and the parameters are the
`Lens.intoParams $slot` lenses the body uses, verbatim.

Three things are wrong with it.  It needs the packing `⟨σ, ⟨args, ()⟩⟩`; the postcondition's
carrier is the result pretending to be a one-element parameter list, a pun belonging to no
layer in particular; and it introduces a second name for the triple that every proof then has
to unfold before reaching `hoareProc_mono` and friends.  The lambda form above has none of
these, and loses nothing: the `$slot` chain still appears, just applied rather than
composed.

## 2. `M'` — which terms to accept

`M.procedure` is `Module.Proc.procedure`, so the middle argument is
`Module.Proc.procedure $M`.  Suggestions:

* Accept a bare `Procedure sig` too, not only a `Module.Proc sig`. `proc (…) {…}` literals and
  `X.f.procedure` are the things one reaches for in a smoke test, and they are what the
  statement is about after `simp` has pushed `apply_simp` through. Elaborate with expected type
  `Module.Proc ?sig`, fall back to `Procedure ?sig`.
* Reject `Module.Arr …` with a message that says "apply the module parameters first". A module
  with parameters has no `sig` and hence no arity, so nothing downstream can work.
* The arity is needed to build the slot chains, so `sig.params` has to reduce to a **list
  literal**. `ModuleSyntax.lean` already has `listLit?` (~line 1254) for exactly this, plus the
  error-message precedent at line 1276 ("must elaborate to a literal `procsig (…) -> …`").
  Reuse both.

Consequence: this cannot be a `macro`. It needs to elaborate `M` first (to learn the arity, and
in step 3 the names), then build and elaborate the conditions. So it is an `elab` term
elaborator, with the two-stage shape `ModuleSyntax.checkBody` already uses. That is the single
biggest implementation cost of the whole feature and it is unavoidable in *any* variant —
including step 1, since even there the arity check needs `sig`.

## 3. Where the names come from — three sources, not one

### (a) Written at the triple (recommended first step)

```
hoare[ S.commit (x, m) : §x = 1 ∧ §y = 0 ==> §res ≠ §y ]
```

The user names the parameters where the triple is stated. Then:

* arity comes from the binder list and is *checked* against `sig`;
* works for an abstract `m : CommitmentScheme` exactly as well as for a concrete procedure;
* no `moduletype` change, no metadata, no environment lookup;
* nothing silently disagrees with the declaration, because nothing is inferred.

Cost: the names are repeated at every triple, and nothing forces them to match the
declaration's names. For a two-parameter procedure that is a fair trade. This also makes
`$params` less necessary, though it stays useful for a `_`-heavy case.

I would build this first regardless of whether (c) is ever implemented, because (c) then
becomes pure sugar — *omit* the binder list and the names are looked up — rather than the
precondition for having the feature at all.

### (b) Recovered from the procedure term (free, and already half-written)

Parameter names are **not lost during elaboration**. A `proc`-built procedure is a
`ProcedureWithHoles.mk` whose body is a nest of `let x := Lens.intoParams …` binders, and
`delabProc` in [ProgramSyntax.lean:882-920](ProgramSyntax.lean#L882-L920) already recovers
them with `withPeeledLets … (·.isAppOf ``Lens.intoParams)`. So for any procedure that whnfs to
a literal `ProcedureWithHoles.mk` — `proc` terms, `module`-declared procedures via
`X.f.procedure.apply_simp`, anything printed by `delabProc` — the same peel gives the declared
names with no new machinery and no syntax change.

This does **not** work for `MT.f m` with `m` abstract: there is no literal procedure to peel.
Which is precisely the case (c) exists for. Still worth having as a fallback, and it is a
half-day's work reusing the delaborator's helper.

### (c) From the `moduletype` declaration

This is the plan in the file, and the two sub-problems are worth separating.

**Syntax.** A per-argument category is the clean move:

```lean
/-- One argument slot of a signature: a type, optionally preceded by a name.
The name is ignored everywhere except `moduletype`, which records it. -/
declare_syntax_cat proc_arg
syntax (atomic(ident " : "))? term : proc_arg

/-- The declared type of an argument slot, and its name if one was given. -/
def ProgramSyntax.parseArg : TSyntax `proc_arg → MacroM (Option Ident × Term)
  | `(proc_arg| $id:ident : $ty:term) => pure (some id, ty)
  | `(proc_arg| $ty:term)             => pure (none, ty)
  | _ => Macro.throwUnsupported
```

Swap `term,*` → `proc_arg,*` in exactly four places — `procsig`
(`ProgramSyntax.lean:552`), `proctype` (`ProgramSyntax.lean:482`), `procmod`
(`ModuleSyntax.lean:45`) and the `moduletype` `proc` field (`ModuleSyntax.lean:641`). The first
three macros drop the names and build `[$types,*]` as they do today; only `moduletype` keeps
them. Notes:

* The name is optional **everywhere**, including `moduletype`, so all 173 existing signature
  occurrences (84 `procsig`, 43 `proctype`, 46 `procmod`, plus 32 `moduletype proc` fields —
  counting the docstring examples in `ModuleSyntax.lean`, which are compiled) keep parsing.
  Requiring the name instead means touching all of them and re-pinning every `#guard_msgs`
  that prints a signature.
* **Leave `proc_binder` alone**, and do not try to make it serve both jobs. `proc_binder`
  (`ProgramSyntax.lean:291-296`) is the *named* binder — `x : T` or `x y : T` — and all five
  of its positions require a name: `proc (…)` params, `var …;` locals (also in
  `HoareSyntax.lean`), `module … using (…)`, `module`'s `proc f (…) : R { … };` fields, and the
  `gaudi_param` group for Lean parameters. Serving signature positions from it would mean
  adding a bare-type production `syntax term : proc_binder`, and because `proc_binder` is a
  `declare_syntax_cat` that production lands in all five: `var Int;`, `proc (Int) { … }` and
  `module X using (Int)` would then *parse* and fail late in `parseBinder`'s
  `| _ => Macro.throwUnsupported` arm, instead of failing at the parser with "expected
  identifier". A separate category costs one `declare_syntax_cat` and keeps those errors
  intact. (The multi-name form `x y : T` would be harmless in a signature — `parseBinder`
  flattens it to two slots — so that is not the objection.)
* The unexpanders need a small touch-up: `procsigParts?` and its consumers
  (`ProgramSyntax.lean:510`, 518, 537, 561, `ModuleSyntax.lean:56`) pass a
  `TSepArray `term ","` around today. The raw argument positions do not move, so this is a type
  change plus wrapping each delaborated type as `` `(proc_arg| $t:term) `` at the
  `ProcedureSignature.mk` unexpander.
* Printing does not round-trip the names: a `ProcedureSignature` carries only types, so those
  unexpanders keep printing bare types, and `moduletype`'s `#guard_msgs` output shows
  `proc f (Nat) -> Bool` for a field declared `proc f (n : Nat) -> Bool`. Not a regression (the
  names were never in the term). Per decision 6, the names go into the per-field docstring
  `moduletype` already generates, which is the only place they can be read back without
  metaprogramming.
* Should `hole_sig` (`proctype … uses (…)`) get names too? I would say no — holes are named as
  a whole, their arguments never referred to by name.

**Storage: a parametric attribute on the accessor.**

```lean
syntax (name := gaudiProcParamNames) "gaudiProcParamNames" ident,* : attr

initialize gaudiProcParamNamesAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `gaudiProcParamNames
    descr := "parameter names of this procedure-valued declaration"
    getParam := fun _ stx => match stx with
      | `(attr| gaudiProcParamNames $ids,*) => return ids.getElems.map (·.getId)
      | _ => throwError "invalid gaudiProcParamNames attribute"
  }
```

Read back with `gaudiProcParamNamesAttr.getParam? env declName`.

An attribute *is* an environment extension — `registerParametricAttribute` is backed by a
`MapDeclarationExtension` keyed by declaration name — plus a way to write that extension by
hand. So it strictly dominates a bare extension, and it beats a generated
`MT.f.paramNames` constant on every count that matters here:

* `moduletype` already attaches an attribute to exactly this declaration:
  `ModuleSyntax.lean:759` emits `@[module_accessor] noncomputable def $accId …`. Adding
  `gaudiProcParamNames` to that quotation is one line, with no new plumbing.
* No extra name per field, so the `logDeclared` `Defined:` listing does not grow.
* Declaration granularity matches: one `MT.f` per field.
* It can be applied **retroactively** — `attribute [gaudiProcParamNames h, m] someAxiomatizedProc` —
  which a generated constant cannot do, and which matches the repo's existing
  `attribute [instance] x_y_disjoint` idiom for axiomatized game variables.

Costs: the names are invisible in the generated `Defined:` report (put them in the per-field
docstring instead), and `local`/`scoped` become available, which one probably never wants here
but which do no harm.

**`module` must register names too** (agreed): `module X { proc f (x : T) : R { … } }` declares
procedures with parameter names in the source, and `X.f` is *not* a `moduletype` accessor. If
only `moduletype` writes the attribute, a triple about a `module`-declared procedure gets
nothing — and that is the most common concrete case. Same one-line change at `module`'s
accessor emission, names taken from its `proc_binder` parameter list (which already has them,
and is already flattened by `ModuleSyntax.binderNames`). Source (b) covers the same case by
other means, so the two are belt and braces rather than one waiting on the other.

**Resolution.** "Only works when the module expression has a concrete `MT.procname` in it" —
prefer finding that in the **elaborated** term (head constant of the accessor application, or
the `@[module_accessor]` attribute, which already exists and marks exactly these accessors)
over pattern-matching the *syntax* for `ident.ident`. Syntax matching breaks on `abbrev`s,
`open`, and local notation; the elaborated form is what determines the type anyway. Fall back
to (a)/(b)/`$params` rather than erroring when no accessor is found.

## 4. Surface syntax shape

`hoare[ P ==> Q ] ( M )` vs EasyCrypt's own `hoare[ M : P ==> Q ]`.

* **`(M)` after the bracket** (the plan): trivially distinguishable from the existing statement
  form, because the token after `] ` is `(` rather than `{` — no backtracking over a `term`.
  Reading cost: `$res` and the parameter names appear in `P`/`Q` *before* the reader (and,
  under option (a), the binder list) knows which procedure they belong to.
* **`hoare[ M : P ==> Q ]`**: matches EasyCrypt, which the header docstring of
  `HoareSyntax.lean` already cites as the reason for the glued `hoare[` token, and reads in the
  right order. Cost: after `hoare[ `, the parser must parse a term and then branch on `:` vs
  `==>`, i.e. `(atomic(term " : "))?` and one wasted parse of `P` in the statement case. `:` is
  not a top-level term infix, so this is unambiguous; error messages get slightly worse.

Given the file already justifies the token shape by pointing at EasyCrypt, I would spend the
re-parse and use `hoare[ M : P ==> Q ]`, with option (a)'s binders as
`hoare[ M (x, m) : P ==> Q ]` — which then reads almost exactly like the procedure's own
declaration. But `(M)` is defensible and cheaper; it is not worth a long argument.

## 5. Smaller points

* `params` and `res` are silently bound in the condition's scope, so a global lens named `res`
  is shadowed inside a postcondition. Harmless (it is a `let` in generated code) but document
  it, and use it as a reason to keep both names short and fixed rather than configurable.
* A `moduletype` field written the long way, `module f : ModuleTypeRep.proc (procsig (…) -> R);`,
  has nowhere to put names. Only the `proc` shorthand can carry them. That asymmetry is fine
  but should be in the docstring.
* Nothing here prints back: `hoareProc` triples will show as `hoareProc (fun args σ => …) …`,
  and even the conditions print as `{ get := fun st ↦ … }.get` (see the `#guard_msgs` in
  `HoareSyntaxTest.lean`). The existing `hoare[ … ] { … }` has the same hole. A delaborator for
  both is worth a separate TODO, not part of this work. The `Getter` printing TODO at the end
  of `ProgramSyntax.lean` is the prerequisite.
* Tests: follow `HoareSyntaxTest.lean` — one `example : Prop` per surface feature (abstract
  module, concrete procedure, zero parameters, one parameter, several parameters, `$params`,
  `$res`, a global in the pre and in the post), plus `:= rfl` pins against hand-written
  `hoareProc` applications, and one `#guard_msgs`-pinned `#check`. A `moduletype`-sourced name
  lookup also needs a negative test: a module expression with no recoverable accessor must
  produce a readable error, not a `sorry`-shaped mess.

## 6. Status

Decisions 5-8 below are **implemented**: signature positions take named arguments
(`proc_arg`), and `moduletype`/`module` record the names in `@[gaudiProcParamNames]`.  See
`ProgramSyntax.lean` (the category, the helpers, the attribute) and `ModuleSyntax.lean` (the
two commands), with tests in `ProgramSyntaxTest.lean` and `ModuleSyntaxTest.lean`.
`Pedersen/Commitment.lean` names the `CommitmentScheme`, `Unhider`, `Binder` and
`CorrectnessT` parameters as the EasyCrypt module types it transcribes do.

The notation itself — decisions 1-4 and 9-13 — is not built yet.

## 7. Decisions

1. **`hoareProc` keeps its signature.** The postcondition sees `sig.ret` and `State`, *not* the
   entry parameters. A property that relates the result to an argument is not expressible as a
   `hoareProc` triple and has to be stated some other way (save the argument into a global, or
   use a relational judgment). Same restriction as EasyCrypt.
2. **Surface shape: `hoare[ M (x, m) : P ==> Q ]`** — EasyCrypt order, at the price of one
   re-parse of the first term in the statement-form case (`(atomic(term " : "))?`). Matches the
   reason the header docstring of `HoareSyntax.lean` gives for the glued `hoare[` token.
3. **Triple-site names win over the attribute, with a warning on mismatch.** An absent binder
   list means "look the names up"; an explicit `()` asserts zero parameters.
4. **Both `Module.Proc sig` and a bare `Procedure sig` are accepted** as the callee — `proc`
   literals and `X.f.procedure` are what smoke tests and post-`simp` goals contain. Elaborate
   against `Module.Proc ?sig`, fall back to `Procedure ?sig`. `Module.Arr …` is rejected with
   "apply the module parameters first".
5. **Attribute name: `gaudiProcParamNames`.**
6. **`moduletype` carries the parameter names into the per-field docstring** it already
   generates, since the signature itself prints as bare types (a `ProcedureSignature` holds no
   names).
7. **Signature positions get a new `proc_arg` category** with an optional name; `proc_binder` is
   left alone (§3c).
8. **The names live in a parametric attribute on the accessor**, written by both `moduletype`
   and `module` (§3c).
9. **The notation goes in `HoareSyntax.lean`**, which gains
   `import GaudisCrypt.Syntax.ModuleSyntax` (for `Module.Proc`, `Module.Proc.procedure` and
   `listLit?`). No cycle — `ModuleSyntax` imports only `ProgramSyntax` and
   `Language/Modules.lean`. The two triple forms share the `hoare[` token and the
   condition-building code, so splitting them into a second file would mean exporting those
   helpers. Knock-on: the barrel docstring at `Syntax/Syntax.lean:12` says `HoareSyntax.lean`
   is the one file there reaching past `Language/`; it now also reaches into its sibling
   `ModuleSyntax.lean`.
10. **The procedure form takes no block at all** — no `{ … }`, no `var` lines, no `let`/`have`.
    The whole triple is `hoare[ M (x, m) : P ==> Q ]` and nothing follows the bracket. There is
    no body at the triple site, and the procedure's own locals are invisible to `hoareProc`
    (the pre sees parameters and globals, the post sees `res` and globals), so there is nothing
    for a `var` to declare. No optional binder prefix either: a Lean `let`/`have` before the
    triple already scopes over both conditions, which covers the "abbreviation shared by `P`
    and `Q`" case. Add one later if it is missed.

    This is about the procedure form only. The statement form
    `hoare[ P ==> Q ] { var u : Int; let two := 2; … }` keeps its `var` lines and spine
    binders, and keeps repeating both around `P` and `Q`, exactly as
    `HoareSyntax.lean` does today.
11. **The conditions are lambdas applied straight to `hoareProc`** — no intermediate
    combinator, and nothing new in `Logic/Hoare.lean`. The ambient state is installed at the
    closed carrier `ProcedureState Unit`, so no `ProcedureScope` appears, no `⟨σ, ⟨args, ()⟩⟩`
    packing is needed, and the result never has to masquerade as a parameter (§1).
12. **Parameters, `params` and `res` are bound as constant getters and read with the sigil** —
    `§x`, `§params`, `§res`, not bare names. One spelling for every variable, so a condition
    lifted out of a procedure body still parses and anything processing triples mechanically
    sees one `eval`-shaped read everywhere.
13. **A parameter's slot is the lens chain the body uses.** `proc` binds its `k`-th parameter to
    `Lens.intoParams $slot` for `slot = ProgramSyntax.mkChain (ProgramSyntax.navSteps k np)`;
    the triple emits the same `$slot` and applies it, `Lens.get $slot args`. The two encodings
    of "parameter `k` of `n`" then coincide, which is what lets a tactic relate a triple's
    parameter getter to the body's parameter lens.
