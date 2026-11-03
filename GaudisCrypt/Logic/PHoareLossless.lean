import GaudisCrypt.Logic.PHoareWp

/-!
# Lower bounds through compound statements

`phoare_wp` handles a conditional only when the expectations of both branches can be computed
(no loop inside). These two rules let a lower-bound proof go through such statements. Losslessness
proofs (`phoare[ True ==> 1 ] ≥ 1`) of procedures whose loops are guarded by a conditional need
them.

* `phoareStmt_if_ge`: a conditional, one judgment per branch (EC's `if` in `phoare`).
* `phoareStmt_seq_ge_one`: `p; q`, where `q` gets expectation at least `1` from everywhere, so `p`
  only needs a bound for the expectation `1` (EC's `seq` with a lossless suffix).
-/

namespace GaudisCrypt

/-- **Conditional, lower bound**: one judgment per branch, each with the test's value in its
precondition. -/
theorem phoareStmt_if_ge {A : ProgramState → Prop} {c : Getter Bool ProgramState}
    {t e : Stmt} {g r : ProgramState → ENNReal}
    (ht : phoareStmt (fun σ => A σ ∧ c.get σ = true) t g GE.ge r)
    (he : phoareStmt (fun σ => A σ ∧ c.get σ = false) e g GE.ge r) :
    phoareStmt A (.ifThenElse c t e) g GE.ge r := by
  intro σ hA
  rw [Stmt.ewp_ifThenElse]
  cases hc : c.get σ
  · simpa [hc] using he σ ⟨hA, hc⟩
  · simpa [hc] using ht σ ⟨hA, hc⟩

/-- **Sequence through a lossless suffix**: if `q` reaches `g` with expectation at least `1` from
every state, then a lower bound on `p` for the expectation `1` is one on `p; q` for `g`. -/
theorem phoareStmt_seq_ge_one {A : ProgramState → Prop} {p q : Stmt}
    {g r : ProgramState → ENNReal}
    (hq : phoareStmt (fun _ => True) q g GE.ge (fun _ => 1))
    (hp : phoareStmt A p (fun _ => 1) GE.ge r) :
    phoareStmt A (.seq p q) g GE.ge r := by
  rw [phoareStmt_seq_iff]
  exact phoareStmt_ge_of_ge hp (fun σ => hq σ trivial)

end GaudisCrypt
