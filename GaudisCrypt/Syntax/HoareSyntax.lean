import GaudisCrypt.Logic.Hoare
import GaudisCrypt.Syntax.ProgramSyntax

/-!
# Concrete syntax for Hoare triples

`hoare[ P ==> Q ] { … }` is the triple `hoare P p Q`, where the body is parsed by the
statement parser of `ProgramSyntax.lean` (the same one `proc` and the module syntax use):

    hoare[ §x = 1 ==> §x = 2 ] {
      var u : Nat;
      let one := 1;
      u <- $x + one;
      x <- $u;
    }

Like a `proc` body, the block may open with `var` declarations and may contain Lean
binders (`let`/`have`/`letI`/`haveI`) in statement position.  Both kinds of binder are
**repeated around `P` and `Q`**: the `var` lenses (as `let`s, exactly as in the body) and
the binders on the *spine* of the statement sequence (`ProgramSyntax.wrapSpineBinders`,
which is what `proc` does for its return value).  So a precondition or postcondition may
mention the local program variables and the body's `let`s.

`P` and `Q` are ordinary `GaudiExpr[ ]` expressions of type `Prop`, so program variables
are read with the `$`/`§` sigil.  The local state is `ProcedureScope [] locals` — no
parameters; a triple about a procedure is `hoareProc`, which has no notation yet.

## Why `hoare[` and not `hoare [`

The leading atom is glued to the bracket on purpose.  A term-level syntax cannot start
with a *non-reserved* identifier-like atom (Lean's leading-parser table never reaches it),
so `hoare [ … ] { … }` would require making `hoare` a keyword — which would break every
ordinary application `hoare A p B` and print the constant as `«hoare»`.  Gluing makes
`hoare[` a token of its own while leaving the identifier `hoare` untouched.  EasyCrypt
spells its triples `hoare[ … : pre ==> post ]`, so this is also the familiar form.
-/

namespace GaudisCrypt

open Lean in section

variable [ProgramSpec]

syntax ppGroup("hoare[ " term " ==> " term " ] " "{")
         (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))*
         gaudi_stmt*
       ppDedent(ppDedent(ppLine)) "}" : term

macro_rules
  | `(hoare[ $pre:term ==> $post:term ] {
        $[var $locals:proc_binder,* ;]*
        $stmts:gaudi_stmt*
      }) => do
    -- multiple `var …;` lines are concatenated into a single local-variable list, and a
    -- binder declaring several names is flattened into one entry each
    let localBs := (← (locals.toList.flatMap (·.getElems.toList)).mapM
      ProgramSyntax.parseBinder).flatten.toArray
    let nl := localBs.size
    let localSigmas ← localBs.mapM fun (_, ty) => `(⟨$ty, inferInstance⟩)
    let localsTerm ← `([$localSigmas,*])
    -- the local state: no parameters, just the declared locals
    let L ← `(ProcedureScope [] $localsTerm)
    -- one `let` per local, binding it to its lens into `ProcedureState L`
    let mut binds : Array (Ident × Term × Term) := #[]
    for j in [0:nl] do
      let (id, ty) := localBs[j]!
      let slot ← ProgramSyntax.mkChain (ProgramSyntax.navSteps j nl)
      binds := binds.push (id, ← `(Lens $ty (ProcedureState $L)), ← `(Lens.intoLocalVars $slot))
    let wrap (bs : Array (Ident × Term × Term)) (inner : Term) : MacroM Term :=
      bs.foldrM (fun (id, ty, val) acc => `(let $id : $ty := $val; $acc)) inner
    let body ← wrap binds (← `((GaudiProg[ $stmts* ] : Stmt $L)))
    -- a condition sees the local lenses *and* the body's spine binders; `GaudiExpr[ ]`
    -- gives a `Getter Prop …`, and `hoare` wants the underlying predicate
    let cond (p : Term) : MacroM Term := do
      wrap binds (← ProgramSyntax.wrapSpineBinders stmts
        (← `((GaudiExpr[ $p ] : Getter Prop (ProcedureState $L)).get)))
    `(hoare $(← cond pre) $body $(← cond post))

end

end GaudisCrypt
