import GaudisCrypt.FV
import GaudisCrypt.Syntax.ExpressionSyntax

/-!
# EasyCrypt's `glob M`

    equiv[ CF(DRestr(D)).main ~ G1(DRestr(D)).main : ={glob D} ==> … ]

`glob M` is the part of the globals the module `M` touches: the getter `R.touched_getter` of a
region `R` (`glob_region M`), whose value at two global states agrees exactly when they agree on
`R` (`Language/Footprint.lean`).  A getter is read like a variable, so `={glob D}` in a
relational condition is `§(glob D){1} = §(glob D){2}`, EC's `={glob D}`.

The region is EC's:
* a concrete module's `glob` is its variables (EC's `var`s of the module, here the `global_var`s
  `C.x` its procedures use): their footprints joined, `C.c.footprint ⊔ C.queries.footprint` for
  `module C` with `C.c`, `C.queries` (the region of their tuple `Lens.pair C.c C.queries`); the
  closers read `={glob C}` as `={C.c, C.queries}` (`TacticMisc.globTuples`);
* any other module (a declared one, an application) has the footprint `FVP.fvP M`.

`glob` is a keyword where this file is imported: the call tactics (`equiv_call (_ : ={glob A, …})`,
the frames `/ glob A`) read it in this form.
-/

namespace GaudisCrypt

namespace ECGlob

open Lean

/-- EC's variables of the concrete module `c`: the `global_var`s `c.x` (those with a `c.x.key_eq`)
that `c`'s definition and its procedures' (`c.f`, `c.f.procedure`, …) mention. -/
def moduleVars (env : Environment) (c : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[c]
  let mut out := #[]
  for _ in [0:256] do
    let some n := todo.back? | break
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let some v := ci.value? | continue
    for u in v.getUsedConstants do
      if env.contains (u ++ `key_eq) then
        if u.getPrefix == c && !out.contains u then out := out.push u
      else if c.isPrefixOf u && !seen.contains u then todo := todo.push u
  return out

end ECGlob

/-- EC's `glob M` as a region: see the module docstring. -/
syntax (name := ecGlobRegion) "glob_region " term:max : term

open Lean Elab Term in
elab_rules : term
  | `(glob_region $M) => do
    let e ← instantiateMVars (← elabTerm M none)
    if let some c := e.getAppFn.constName? then
      let vs := ECGlob.moduleVars (← getEnv) c
      if let some last := vs.back? then
        -- EC's tuple of the module's variables, as a region: their footprints joined
        let fp (v : Name) : TermElabM Term := `(Lens.footprint $(mkCIdent v))
        let R ← (vs.pop).foldrM (fun v acc => do `($(← fp v) ⊔ $acc)) (← fp last)
        return ← elabTerm R none
    elabTerm (← `(FVP.fvP $M)) none

/-- EC's `glob M`: the getter of the globals of the module `M`. -/
syntax (name := ecGlob) "glob " term:max : term

macro_rules
  | `(glob $M) => `((glob_region $M).touched_getter)

end GaudisCrypt
