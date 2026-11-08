import GaudisCrypt.Logic.Inline
import GaudisCrypt.Logic.HoareWp

/-!
# Reads through the inliner's renamings of the locals

Inlining runs the inlined code on the locals renamed (`Flatten.trafo`: the caller's names, `@…`
escaped; `Flatten.rename ren`: the cleanup permutation), and a condition about the state before it
comes back as a condition about the renamed state, `L.get σ`.  A read of a local `n` the renaming
keeps (`ι n = n`, computed: no `@` at the start, not among `ren`'s names) is the read of `n`
itself (`localVarLens_get_mapLocal_embed_of_fix`); a global's read is unchanged
(`globals_trafo_get`, `globals_rename_get`).

    rename_reads        -- these reads simplified in the goal and every hypothesis
-/

namespace GaudisCrypt

/-- A local read through a renaming of the locals is the renamed local's read. -/
theorem localVarLens_get_mapLocal_embed (ι : String → String) (hι : ι.Injective) (n : String)
    (T : Type) [i : Nonempty T] {k : Nat} (hk : k = VariableName.encode n) (σ : ProgramState) :
    (@localVarLens n T i k hk).get ((ProgramState.mapLocal (VariableAssignment.embed ι hι)).get σ) =
      (@localVarLens (ι n) T i (VariableName.encode (ι n)) rfl).get σ :=
  congrArg (fun L : Lens T ProgramState => L.get σ)
    (ProgramState.mapLocal_embed_chain_varLens ι hι n T i k hk)

/-- … the same local's read, for a name the renaming keeps. -/
theorem localVarLens_get_mapLocal_embed_of_fix (ι : String → String) (hι : ι.Injective)
    (n : String) (T : Type) [i : Nonempty T] {k : Nat} (hk : k = VariableName.encode n)
    (hfix : ι n = n) (σ : ProgramState) :
    (@localVarLens n T i k hk).get ((ProgramState.mapLocal (VariableAssignment.embed ι hι)).get σ) =
      (@localVarLens n T i k hk).get σ := by
  rw [localVarLens_get_mapLocal_embed]
  subst hk
  generalize ι n = m at hfix ⊢
  subst hfix
  rfl

/-- A renaming of the locals keeps the globals. -/
theorem ProgramState.mapLocal_get_globals (m : Lens VariableAssignment VariableAssignment)
    (t : ProgramState) : ((ProgramState.mapLocal m).get t).globals = t.globals := rfl

/-- A read through a chain of lenses, one at a time. -/
theorem Lens.chain_get_apply {a b c : Type _} (x : Lens b c) (y : Lens a b) (s : c) :
    (x.chain y).get s = y.get (x.get s) := rfl

/-- `escape` keeps a name that does not start with `@`. -/
theorem Flatten.escape_of_head {n : String} (h : n.toList.head? ≠ some '@') :
    Flatten.escape n = n := by
  have : Flatten.escapeChars n.toList = n.toList := by
    cases hn : n.toList with
    | nil => rfl
    | cons c cs =>
      rw [hn] at h
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      simp [Flatten.escapeChars, h]
  rw [Flatten.escape, this, String.ofList_toList]

end GaudisCrypt

/-- `rename_reads`: the reads through the inliner's renamings of the locals simplified, in the
goal and every hypothesis (see the module docstring). -/
macro "rename_reads" : tactic => `(tactic|
  simp (disch := simp (config := { decide := true }) (disch := decide) only
      [GaudisCrypt.Flatten.renameName, GaudisCrypt.Flatten.swaps,
        GaudisCrypt.Flatten.escape_of_head, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        Equiv.Perm.one_apply, if_false]) only
    [GaudisCrypt.Lens.chain_get_apply, GaudisCrypt.Flatten.rename, GaudisCrypt.Flatten.trafo,
      GaudisCrypt.localVarLens_get_mapLocal_embed_of_fix,
      GaudisCrypt.ProgramState.mapLocal_get_globals] at *)
