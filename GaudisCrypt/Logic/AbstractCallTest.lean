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

/-- The oracle premise, for any region `F` disjoint from the counter. -/
theorem count_query (F : Footprint VariableAssignment) (hF : F ≤ (count.footprint)ᶜ) :
    prhlProc (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF count F (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂)
      (Oracle.query Count1).procedure (Oracle.query Count2).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF count F (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂) := by
  equiv_proc
  stmt_inline 0
  stmt_wp
  equiv_skip
  have hc : count.footprint ≤ Fᶜ := (Footprint.le_compl_comm _ _).mp hF
  rintro g₁ g₂ x₁ x₂ ⟨hx, hg, hI⟩
  refine ⟨hx, ?_, ?_⟩
  · rw [touched_set_of_le_compl hc, touched_set_of_le_compl hc]
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
      | zero => exact count_query _ hdisj
      | succ m => nomatch m)

/-- The same at module level: the adversary is a module of the functor type, as EasyCrypt declares
it (`declare module D <: Adv {-count}`), with the representation hypothesis (exception E2). -/
theorem module_adversary_count (D : Module.Arr Oracle (procmod () → Bool))
    (hD : Module.Representable D (holes := oracleHoles) fun O => (Oracle.query O).procedure)
    (hdisj : FVP.fvP D ≤ (count.footprint)ᶜ) :
    prhlProc
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ globInvF count (FVP.fvP D) (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂)
      (Module.app D Count1).procedure (Module.app D Count2).procedure
      (fun r₁ g₁ r₂ g₂ => r₁ = r₂ ∧ globInvF count (FVP.fvP D) (fun c₁ c₂ => c₂ = 2 * c₁) g₁ g₂) :=
  prhlProc_abstract_call_module count D _ hD hdisj _
    (fun n => by cases n with
      | zero => exact inferInstanceAs (Countable ℕ)
      | succ m => nomatch m)
    Count1 Count2
    (fun n => by cases n with
      | zero => exact count_query _ hdisj
      | succ m => nomatch m)

-- A concrete distinguisher, written with the `module` command, is representable
-- (`Module.representedBy_of_app_eq`).  The footprint bound goes through the oracle `Zero`, whose
-- footprint is empty.
module Guess using (O : Oracle) {
  proc main() : Bool {
    var y : ℕ;
    y <- call O.query ((3 : ℕ));
    return $y == 3
  };
}

module Zero : Oracle {
  proc query(x : ℕ) : ℕ {
    return 0
  };
}

theorem fvP_Zero : FVP.fvP Zero = ⊥ := by
  change FVP.fvP (Module.proc Zero.query.procedure) = ⊥
  rw [FVP.fvP_module_proc]
  refine le_bot_iff.mp (sup_le ?_ ?_)
  · change Lens.reduceFootprint ProgramState.globalL ⊥ ≤ ⊥
    rw [Lens.reduceFootprint_bot]
  · refine le_trans (Lens.reduceFootprint_mono _ ?_) (Lens.reduceFootprint_bot _).le
    exact ProgramDenotation.footprint_le_of_inFootprint (ProgramDenotation.inFootprint_pure _ _)

theorem guess_representable :
    Module.Representable (holes := oracleHoles) Guess fun O => (Oracle.query O).procedure :=
  ⟨_, Module.representedBy_of_app_eq Guess _ Guess.main.procedure
    (fun O => by simp [Guess.apply_simp, Guess.main.apply_simp]) Zero fvP_Zero⟩

end GaudisCrypt.AbstractCallTest
