import GaudisCrypt.FV
import GaudisCrypt.Syntax.ExpressionSyntax

/-!
# EasyCrypt's `glob M`

    equiv[ CF(DRestr(D)).main ~ G1(DRestr(D)).main : ={glob D} ==> … ]

`glob M` is the part of the globals the module `M` touches: the getter
`(FVP.fvP M).touched_getter`, whose value at two global states agrees exactly when they agree on
`M`'s globals (`Language/Footprint.lean`).  A getter is read like a variable, so `={glob D}` in a
relational condition is `§(glob D){1} = §(glob D){2}`, EC's `={glob D}`.

`glob` is a keyword where this file is imported: the call tactics (`equiv_call (_ : ={glob A, …})`,
the frames `/ glob A`) read it in this form.
-/

namespace GaudisCrypt

/-- EC's `glob M`: the getter of the globals the module `M` touches. -/
syntax (name := ecGlob) "glob " term:max : term

macro_rules
  | `(glob $M) => `((FVP.fvP $M).touched_getter)

end GaudisCrypt
