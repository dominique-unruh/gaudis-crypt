import Lean

/-!
# The variables of a concrete module (for EasyCrypt's `glob M`)

`ECGlob.moduleVars`: what `glob M` is made of for a concrete module (`Logic/ECGlob.lean`).  In a
file of its own: the printer of relational conditions (`Syntax/PRHLSyntax.lean`) asks it whether
`(FVP.fvP M).touched_getter` is what `glob M` stands for, without importing the keyword `glob`.
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

end GaudisCrypt
