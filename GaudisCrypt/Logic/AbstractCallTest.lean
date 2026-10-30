import GaudisCrypt.Logic.AbstractCall
import GaudisCrypt.Logic.PRHLWp

/-! Smoke test for the abstract call rule: an abstract adversary with one oracle, run against a
counter that adds 1 and one that adds 2, keeps `count₂ = 2 · count₁`. -/

namespace GaudisCrypt.AbstractCallTest

open GaudisCrypt

global_var count : ℕ

moduletype Oracle {
  proc query (x : ℕ) -> ℕ;
}

module Count1 : Oracle {
  proc query(x : ℕ) : ℕ {
    count <- $count + 1;
    return $x
  };
}

module Count2 : Oracle {
  proc query(x : ℕ) : ℕ {
    count <- $count + 2;
    return $x
  };
}

abbrev oracleHoles : HoleSigs := .cons (procsig (ℕ) -> ℕ) .empty

theorem count_query (A : ProcedureWithHoles oracleHoles (procsig () -> Bool))
    (hdisj : FVP.fvP_proc A ≤ (count.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInv count A (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂)
      (Oracle.query Count1).procedure (Oracle.query Count2).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInv count A (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂) := by
  equiv_proc
  stmt_inline 0
  stmt_wp
  equiv_skip
  have hc : count.footprint ≤ (FVP.fvP_proc A)ᶜ := (Footprint.le_compl_comm _ _).mp hdisj
  rintro g₁ g₂ x₁ x₂ ⟨hx, hg, hI⟩
  refine ⟨hx, ?_, ?_⟩
  · rw [glob_set_of_le_compl hc, glob_set_of_le_compl hc]
    exact hg
  · simp only [Lens.set_get] at hI ⊢
    omega

/-- EC: `equiv[ A(Count1).main ~ A(Count2).main : ={glob A} ∧ count{2} = 2 * count{1} ==>
={res, glob A} ∧ count{2} = 2 * count{1} ]` by `proc (count{2} = 2 * count{1})`. -/
theorem adversary_count (A : ProcedureWithHoles oracleHoles (procsig () -> Bool))
    (hdisj : FVP.fvP_proc A ≤ (count.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInv count A (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂)
      (A.instantiate (Oracle.query Count1).procedure)
      (A.instantiate (Oracle.query Count2).procedure)
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInv count A (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂) :=
  prhlProc_abstract_call count _ _ A hdisj _
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable ℕ)
      | succ m => nomatch m)
    (fun n => by cases n with
      | zero => exact count_query A hdisj
      | succ m => nomatch m)

end GaudisCrypt.AbstractCallTest
