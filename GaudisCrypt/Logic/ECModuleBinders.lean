import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.PHoare

/-!
# EasyCrypt's module binders in formulas, and `islossless`

    ∃ (S <: SIMULATOR {-Bounder, -A}), P      -- EC's `exists (S <: SIMULATOR {-Bounder, -A}), P`
    ∀ (F <: FUNCTIONALITY), P                 -- EC's `forall (F <: FUNCTIONALITY), P`
    islossless S(F).init                      -- EC's `islossless S(F).init`

A module bound in a formula is a declared module (`declare module`): with EC's restriction, and
finitely many globals.  So `∃ (S <: T {-X}), P` is `∃ (S : T) (_ : Module.Declared S R), P` and
`∀ (F <: T {-X}), P` is `∀ (F : T) [Module.Declared F R], P`, `R` the restriction's footprint
computed as `declare module` computes it (`⊥` for an `∃` without one).  Introduced
(`rintro ⟨S, _, …⟩`, `intro F _`), the declaration is an instance in context, which
`fp_disjoint` reads.  `∀ (F <: T), P` without a restriction is `∀ F : T, P`: EC's `forall` then
asks nothing of `F`, and the formula applies to a concrete module as it stands (EC's
`S_ll RO _`), with no declaration to show.

`islossless M` is `M.procedure.IsLossless` for a procedure module `M` (a path `S(F).init`, a
field `F.get`).
-/

namespace GaudisCrypt

open Lean Elab Term Meta DeclareModule

/-- `∃ (S <: T {-X₁, …}), P`: see the module docstring. -/
syntax (name := existsDeclared) "∃ " "(" ident " <: " term:max (" {" ("-" ident),* "}")? ")"
  ", " term : term

/-- `∀ (F <: T {-X₁, …}), P`: see the module docstring. -/
syntax (name := forallDeclared) "∀ " "(" ident " <: " term:max (" {" ("-" ident),* "}")? ")"
  ", " term : term

elab_rules : term
  | `(∃ ($S:ident <: $T $[{ $[- $xs:ident],* }]?), $P) => do
    let R ← DeclareModule.restrictionTerm (xs.getD #[])
    elabTerm (← `(Exists fun ($S : $T) => Exists fun (_ : Module.Declared $S $R) => $P)) none
  | `(∀ ($F:ident <: $T $[{ $[- $xs:ident],* }]?), $P) => do
    match xs with
    | none => elabTerm (← `(∀ ($F : $T), $P)) none
    | some xs =>
      let R ← DeclareModule.restrictionTerm xs
      elabTerm (← `(∀ ($F : $T) [Module.Declared $F $R], $P)) none

/-- EC's `islossless M`: the procedure module `M` terminates with probability `1`. -/
macro "islossless " M:term:max : term => `(Procedure.IsLossless (Module.Proc.procedure $M))

end GaudisCrypt
