import GaudisCrypt.Logic.LoopTransform

/-!
# EasyCrypt's `transitivity{1}` with a reflexive first leg

`transitivity{1} { c₂ } (E ==> F) (P ==> Q)` replaces the left program `c₁` by `c₂`: a judgment
`c₁ ~ c₂ : E ==> F`, with `E` reflexive (EC: its `forall &1 &2, P => exists &m, E /\ P` side goal,
discharged by taking `&m = &1`), and the judgment `c₂ ~ c₃ : P ==> Q'` where `Q'` asks `Q` of every
left state that `F` relates to the middle one.  `prhlStmt.trans_left` is that instance of
`prhlStmt.trans`; it fixes the middle judgment's conditions, so that it can be left as a goal.
-/

namespace GaudisCrypt

variable {A B : ProgramState → ProgramState → Prop}

/-- **`transitivity{1}`**: replace the left program `c₁` by `c₂`, related by `E ==> F` with `E`
reflexive. -/
theorem prhlStmt.trans_left {E F : ProgramState → ProgramState → Prop} {c₁ c₂ c₃ : Stmt}
    (h₁ : prhlStmt E c₁ c₂ F) (hE : ∀ σ, E σ σ)
    (h₂ : prhlStmt A c₂ c₃ fun τ₂ τ₃ => ∀ τ₁, F τ₁ τ₂ → B τ₁ τ₃) : prhlStmt A c₁ c₃ B :=
  prhlStmt_conseq (prhlStmt.trans h₁ h₂) (fun σ₁ _ hA => ⟨σ₁, hE σ₁, hA⟩)
    (fun τ₁ _ ⟨_, hF, hB⟩ => hB τ₁ hF)

end GaudisCrypt
