import Lean

/-!
# Reporting what a tactic did not do

A tactic of the EC layer that cannot do a step as specified and continues another way (a weaker
rule, a goal left in another shape) says so: `ECReport.fallback`.  By default this is a warning,
so the proof still goes through and the build lists every place where it happens; with

    set_option ec.strict true

it is an error.  What is too frequent for a warning goes to the trace classes `ec.frame` (what a
frame keeps and drops), `ec.rule` (which rule or form a tactic chose), `ec.close` (the closers'
steps): `set_option trace.ec true` shows all of them.

Failures that are part of a search (the next candidate is tried) are not reported.
-/

/-- A fallback of an EC-layer tactic is an error, not a warning (`ECReport.fallback`). -/
register_option ec.strict : Bool := {
  defValue := false
  descr := "a fallback of an EC-layer tactic (`ECReport.fallback`) is an error"
}

namespace GaudisCrypt.ECReport

open Lean

initialize registerTraceClass `ec
initialize registerTraceClass `ec.frame (inherited := true)
initialize registerTraceClass `ec.rule (inherited := true)
initialize registerTraceClass `ec.close (inherited := true)

/-- `tac` could not do `what` and continues without it; `err?` is the reason.  A warning, or an
error under `set_option ec.strict true`.  Call it after any state restore (a restore drops the
messages logged before it). -/
def fallback (tac : String) (what : MessageData) (err? : Option Exception := none) :
    CoreM Unit := do
  let reason := match err? with
    | some e => m!"\nreason: {e.toMessageData}"
    | none => m!""
  let msg := m!"{tac}: {what}{reason}"
  if ec.strict.get (← getOptions) then throwError msg else logWarning msg

end GaudisCrypt.ECReport
