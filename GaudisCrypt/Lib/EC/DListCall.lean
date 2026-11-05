import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Logic.PRHLStmt

/-!
# A call of `LoopSnoc.sample` is a sampling of `dlist`

EasyCrypt's `Sample_LoopSnoc_eq` (`DList.ec`'s `Program` theory), at the level of statements: the
call `x <@ LoopSnoc.sample(n)` has the runs of the sampling `x <$ dlist d n`
(`LoopSnoc.call_denotation`).  `prhlStmt_seq_dlist_left` is EasyCrypt's
`transitivity{1} { x <@ LoopSnoc.sample(n); } (true ==> ={x}) (…)` on a leading sampling: it
replaces it by the call, whose loop can then be inlined and related to another loop.  Kept apart
from `DList.lean` so that its importers need not be rebuilt.
-/

namespace GaudisCrypt.EC

namespace DList.Program

open GaudisCrypt

variable (t : Type) [Inhabited t] (d : SubProbability t)

/-- The call `x <@ LoopSnoc.sample(n)` runs as the sampling `x <$ dlist d n`. -/
theorem LoopSnoc.call_denotation (x : Setter (List t) ProgramState) (n : Getter ℤ ProgramState)
    (e : Getter (SubProbability (List t)) ProgramState) (he : ∀ σ, e.get σ = dlist d (n.get σ))
    (σ : ProgramState) :
    programDenotation (Stmt.call x (LoopSnoc.sample t d).procedure n) σ =
      programDenotation (StmtWithHoles.sample x e) σ := by
  rw [programDenotation_call_apply, LoopSnoc.sample_denotation, programDenotation_sample_apply,
    he]
  refine SubProbability.ext_of_expected fun F => ?_
  simp only [SubProbability.expected_hbind, expected_pure]
  rw [show ProgramState.globalL.set σ.globals σ = σ from ProgramState.globalL.get_set σ]

end DList.Program

open DList.Program in
/-- EC's `transitivity{1} { x <@ LoopSnoc.sample(n); } (true ==> ={x}) (…)`: a leading sampling of
`dlist d n` on the left is replaced by the call of `LoopSnoc.sample(n)` (`Sample_LoopSnoc_eq`). -/
theorem prhlStmt_seq_dlist_left {t : Type} [Inhabited t] {d : SubProbability t}
    {A B : ProgramState → ProgramState → Prop} {b c₂ : Stmt}
    (x : Setter (List t) ProgramState) (n : Getter ℤ ProgramState)
    {e : Getter (SubProbability (List t)) ProgramState} (he : ∀ σ, e.get σ = dlist d (n.get σ))
    (h : prhlStmt A (.seq (Stmt.call x (LoopSnoc.sample t d).procedure n) b) c₂ B) :
    prhlStmt A (.seq (StmtWithHoles.sample x e) b) c₂ B :=
  prhlStmt_seq_congr_left (fun σ₁ _ _ => (LoopSnoc.call_denotation t d x n e he σ₁).symm) h

open DList.Program in
/-- `prhlStmt_seq_dlist_left` for a left statement that is the sampling alone. -/
theorem prhlStmt_dlist_left {t : Type} [Inhabited t] {d : SubProbability t}
    {A B : ProgramState → ProgramState → Prop} {c₂ : Stmt}
    (x : Setter (List t) ProgramState) (n : Getter ℤ ProgramState)
    {e : Getter (SubProbability (List t)) ProgramState} (he : ∀ σ, e.get σ = dlist d (n.get σ))
    (h : prhlStmt A (Stmt.call x (LoopSnoc.sample t d).procedure n) c₂ B) :
    prhlStmt A (StmtWithHoles.sample x e) c₂ B := by
  unfold prhlStmt at h ⊢
  rw [show programDenotation (StmtWithHoles.sample x e) =
      programDenotation (Stmt.call x (LoopSnoc.sample t d).procedure n) from
    funext fun σ => (LoopSnoc.call_denotation t d x n e he σ).symm]
  exact h

end GaudisCrypt.EC
