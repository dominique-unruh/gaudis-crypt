import GaudisCrypt.Logic.PHoare
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.PRHL2

/-!
# pHL loops that terminate with probability `1`: EC's `while I V k ε`

EC's rule for `phoare[ while b c : P ==> Q ] = r` (`ecPhlWhile.ml`, `t_bdhoare_while_rev_geq`):
an invariant `I`, an integer variant `V` bounded by `k` on `I` and positive where the test
passes, and a probability `ε > 0` with which one round decreases the variant.  Then the loop
terminates with probability `1` from `I` (`Stmt.ewp_while_one_of_variant`), and its expectation
is the one solution of the loop's equation (`phoareStmt_while_rev_eq`).

The zero-one argument of `Stmt.ewp_while_one` (`Logic/PHoare.lean`) is the case `I = True`,
`k = 1`: there, one round leaves the loop with probability `ε`.
-/

namespace GaudisCrypt

/-- An event of probability `1` may be assumed under an expectation at most `1`. -/
theorem Stmt.ewp_ge_of_certain (s : Stmt) {Ψ : ProgramState → Prop} {f h : ProgramState → ENNReal}
    {σ : ProgramState} (hΨ : s.ewp (fun τ => indicatorE (Ψ τ)) σ = 1)
    (hf : ∀ τ, f τ ≤ 1) (hle : ∀ τ, Ψ τ → f τ ≤ h τ) : s.ewp f σ ≤ s.ewp h σ := by
  classical
  have hnot : s.ewp (fun τ => indicatorE (¬ Ψ τ)) σ = 0 := by
    have hsum : s.ewp (fun τ => indicatorE (Ψ τ) + indicatorE (¬ Ψ τ)) σ ≤ 1 := by
      refine (Stmt.ewp_mono s (G := fun _ => 1) (fun τ => ?_) σ).trans (Stmt.ewp_const_le s 1 σ)
      by_cases hτ : Ψ τ <;> simp [hτ]
    rw [Stmt.ewp_add, hΨ] at hsum
    exact le_antisymm ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp (by simpa using hsum))
      bot_le
  calc s.ewp f σ ≤ s.ewp (fun τ => h τ + indicatorE (¬ Ψ τ)) σ := by
        refine Stmt.ewp_mono s (fun τ => ?_) σ
        by_cases hτ : Ψ τ
        · exact (hle τ hτ).trans le_self_add
        · rw [indicatorE_of hτ]; exact (hf τ).trans le_add_self
    _ = s.ewp h σ := by rw [Stmt.ewp_add, hnot, add_zero]

/-- A statement that reaches an event with probability `1` is lossless. -/
theorem Stmt.ewp_one_of_certain (s : Stmt) {Ψ : ProgramState → Prop} {σ : ProgramState}
    (hΨ : s.ewp (fun τ => indicatorE (Ψ τ)) σ = 1) : s.ewp (fun _ => 1) σ = 1 :=
  le_antisymm (Stmt.ewp_const_le s 1 σ)
    (hΨ.symm.le.trans (Stmt.ewp_mono s (fun _ => indicatorE_le_one _) σ))

/-- `Stmt.ewp_while_one_of_variant` for `ε ≤ 1`. -/
private theorem Stmt.ewp_while_one_of_variant_aux {c : Getter Bool ProgramState} {body : Stmt}
    (I : ProgramState → Prop) (V : ProgramState → ℤ) (k : ℤ) (ε : ENNReal) (hε0 : ε ≠ 0)
    (hε1 : ε ≤ 1)
    (hterm : ∀ σ, I σ → V σ ≤ k ∧ (V σ ≤ 0 → c.get σ = false))
    (hinv : ∀ σ, I σ → c.get σ = true → body.ewp (fun τ => indicatorE (I τ)) σ = 1)
    (hvar : ∀ σ, I σ → c.get σ = true →
      ε ≤ body.ewp (fun τ => indicatorE (V τ < V σ)) σ)
    (σ : ProgramState) (hI : I σ) :
    Stmt.ewp (StmtWithHoles.while c body) (fun _ => 1) σ = 1 := by
  classical
  set T := Stmt.ewp (StmtWithHoles.while c body) (fun _ => 1) with hT
  have hT1 : ∀ τ, T τ ≤ 1 := fun τ => Stmt.ewp_const_le _ 1 τ
  have hunfold : ∀ τ, T τ = if c.get τ then body.ewp T τ else 1 :=
    fun τ => Stmt.ewp_while_unfold c body _ τ
  -- the least termination probability over the invariant's states of variant at most `j`
  let m : ℕ → ENNReal := fun j => (⨅ τ : {τ // I τ ∧ V τ ≤ (j : ℤ)}, T τ) ⊓ 1
  have hm1 : ∀ j, m j ≤ 1 := fun j => inf_le_right
  have hmT : ∀ (j : ℕ) τ, I τ → V τ ≤ (j : ℤ) → m j ≤ T τ := fun j τ h1 h2 =>
    inf_le_left.trans (iInf_le (fun τ : {τ // I τ ∧ V τ ≤ (j : ℤ)} => T τ) ⟨τ, h1, h2⟩)
  have hmono : ∀ i j : ℕ, i ≤ j → m j ≤ m i := fun i j hij =>
    le_inf (le_iInf fun τ => hmT j τ τ.2.1 (τ.2.2.trans (by exact_mod_cast hij))) (hm1 j)
  set N := k.toNat with hN
  have hkN : k ≤ (N : ℤ) := Int.self_le_toNat k
  -- every state of the invariant terminates with probability at least `m N`
  have hall : ∀ τ, I τ → m N ≤ T τ := fun τ h => hmT N τ h ((hterm τ h).1.trans hkN)
  -- variant `0`: the loop is left
  have h0 : m 0 = 1 := by
    refine le_antisymm (hm1 0) (le_inf (le_iInf fun τ => ?_) le_rfl)
    rw [hunfold τ, (hterm τ τ.2.1).2 (by exact_mod_cast τ.2.2)]
    simp
  -- one more unit of variant costs a factor `ε`
  have hstep : ∀ j, j < N → m N + (m j - m N) * ε ≤ m (j + 1) := by
    intro j hj
    have hle : m N ≤ m j := hmono j N hj.le
    have hL1 : m N + (m j - m N) * ε ≤ 1 := by
      calc m N + (m j - m N) * ε ≤ m N + (m j - m N) * 1 := by gcongr
        _ = m j := by rw [mul_one, add_tsub_cancel_of_le hle]
        _ ≤ 1 := hm1 j
    refine le_inf (le_iInf fun τ => ?_) hL1
    obtain ⟨τ, hIτ, hVτ⟩ := τ
    rw [hunfold τ]
    split_ifs with hc
    · -- after one round: the invariant, and with probability `ε` a smaller variant
      have hpt : ∀ τ', I τ' →
          m N + (m j - m N) * indicatorE (V τ' < V τ) ≤ T τ' := by
        intro τ' hI'
        by_cases hlt : V τ' < V τ
        · rw [indicatorE_of hlt, mul_one, add_tsub_cancel_of_le hle]
          exact hmT j τ' hI' (by push_cast at hVτ; omega)
        · rw [indicatorE_of_not hlt, mul_zero, add_zero]
          exact hall τ' hI'
      have hf1 : ∀ τ', m N + (m j - m N) * indicatorE (V τ' < V τ) ≤ 1 := by
        intro τ'
        calc m N + (m j - m N) * indicatorE (V τ' < V τ)
            ≤ m N + (m j - m N) * 1 := by gcongr; exact indicatorE_le_one _
          _ = m j := by rw [mul_one, add_tsub_cancel_of_le hle]
          _ ≤ 1 := hm1 j
      calc m N + (m j - m N) * ε
          ≤ m N * body.ewp (fun _ => 1) τ
              + (m j - m N) * body.ewp (fun τ' => indicatorE (V τ' < V τ)) τ := by
            rw [Stmt.ewp_one_of_certain body (hinv τ hIτ hc), mul_one]
            gcongr
            exact hvar τ hIτ hc
        _ = body.ewp (fun τ' => m N + (m j - m N) * indicatorE (V τ' < V τ)) τ := by
            rw [Stmt.ewp_add, Stmt.ewp_const_mul]
            congr 1
            have := Stmt.ewp_const_mul body (m N) (fun _ => 1) τ
            simp only [mul_one] at this
            exact this.symm
        _ ≤ body.ewp T τ := Stmt.ewp_ge_of_certain body (hinv τ hIτ hc) hf1 hpt
    · exact hL1
  -- so `(1 − m N) ε ^ j ≤ m j − m N`, and at `j = N` the left side is `0`
  have hpow : ∀ j, j ≤ N → (1 - m N) * ε ^ j ≤ m j - m N := by
    intro j
    induction j with
    | zero => intro _; rw [pow_zero, mul_one, h0]
    | succ j ih =>
      intro hj
      have h1 := hstep j (by omega)
      have hfin : m N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hm1 N)
      calc (1 - m N) * ε ^ (j + 1) = (1 - m N) * ε ^ j * ε := by rw [pow_succ, mul_assoc]
        _ ≤ (m j - m N) * ε := by gcongr; exact ih (by omega)
        _ ≤ m (j + 1) - m N := by
            refine ENNReal.le_sub_of_add_le_left hfin ?_
            exact h1
  have hz : (1 - m N) * ε ^ N = 0 := by
    have := hpow N le_rfl
    rwa [tsub_self, nonpos_iff_eq_zero] at this
  have hm : 1 ≤ m N :=
    tsub_eq_zero_iff_le.mp ((mul_eq_zero.mp hz).resolve_right (pow_ne_zero N hε0))
  exact le_antisymm (hT1 σ) (hm.trans (hall σ hI))

/-- **Almost-sure termination from a variant** (EC's `while I V k ε`): from the invariant `I`,
with a variant `V` that is at most `k` on `I` and positive where the test passes, if one round
keeps `I` with probability `1` and decreases `V` with probability at least `ε > 0`, the loop
terminates with probability `1`. -/
theorem Stmt.ewp_while_one_of_variant {c : Getter Bool ProgramState} {body : Stmt}
    (I : ProgramState → Prop) (V : ProgramState → ℤ) (k : ℤ) (ε : ENNReal) (hε0 : ε ≠ 0)
    (hterm : ∀ σ, I σ → V σ ≤ k ∧ (V σ ≤ 0 → c.get σ = false))
    (hinv : ∀ σ, I σ → c.get σ = true → body.ewp (fun τ => indicatorE (I τ)) σ = 1)
    (hvar : ∀ σ, I σ → c.get σ = true →
      ε ≤ body.ewp (fun τ => indicatorE (V τ < V σ)) σ)
    (σ : ProgramState) (hI : I σ) :
    Stmt.ewp (StmtWithHoles.while c body) (fun _ => 1) σ = 1 :=
  Stmt.ewp_while_one_of_variant_aux I V k (ε ⊓ 1) (by simp [hε0]) inf_le_right hterm hinv
    (fun τ h1 h2 => inf_le_left.trans (hvar τ h1 h2)) σ hI

/-- A statement with a prescribed expectation of `g`: go to the state `τ₁` with probability
`J σ`, fail otherwise.  (The stand-in for EC's abstract statement in the loop rule below.) -/
noncomputable def Stmt.jumpWith (J : ProgramState → ENNReal) (hJ : ∀ σ, J σ ≤ 1)
    (τ₁ : ProgramState) : Stmt :=
  StmtWithHoles.sample (⟨fun _ _ => τ₁, fun _ _ _ => rfl⟩ : Setter Unit ProgramState)
    (Getter.mk fun σ => SubProbability.scale (J σ) (pure ()) (by
      have h1 : (pure () : SubProbability Unit).1 Set.univ ≤ 1 := by
        simpa using (pure () : SubProbability Unit).2.1
      calc J σ * (pure () : SubProbability Unit).1 Set.univ ≤ 1 * 1 :=
            mul_le_mul' (hJ σ) h1
        _ = 1 := one_mul 1))

theorem Stmt.ewp_jumpWith (J : ProgramState → ENNReal) (hJ : ∀ σ, J σ ≤ 1) (τ₁ : ProgramState)
    (g : ProgramState → ENNReal) (σ : ProgramState) :
    (Stmt.jumpWith J hJ τ₁).ewp g σ = J σ * g τ₁ := by
  rw [Stmt.jumpWith, Stmt.ewp_sample]
  simp [SubProbability.scale_expected, expected_pure]

open Classical in
/-- **EC's `while I V k ε`** on `phoare[ while b c : P ==> g ] = bd` (`ecPhlWhile.ml`,
`t_bdhoare_while_rev_geq`), EC's six conditions in its order:

* `hpre`: the precondition gives the invariant;
* `hbound`: where the loop is not entered, the bound is the postcondition;
* `hterm`: on the invariant the variant is at most `k`, and positive where the test passes;
* `hbody`: one round followed by *any* statement `w` that meets the judgment meets it (EC's
  abstract statement standing for the loop);
* `hinv`: one round keeps the invariant, with probability `1`;
* `hε0`, `hvar`: one round decreases the variant with probability at least `ε > 0`.

Beyond EC's: `g ≤ 1` and `bd ≤ 1` (an event and a probability), and some state satisfies the
postcondition (`hsat`).  The last is needed here because `w` is a quantified statement, not
EC's abstract one: if no state satisfies the postcondition, no `w` meets the judgment with a
bound other than `0`, and `hbody` holds for want of one — `while (b) b <- false` from `b` with
the postcondition `false` would pass the six conditions for any bound.  (In EC the judgment
about `w` is a hypothesis that can only be used, not refuted.) -/
theorem phoareStmt_while_rev_eq {P : ProgramState → Prop} {body : Stmt}
    {c : Getter Bool ProgramState} {g bd : ProgramState → ENNReal}
    (I : ProgramState → Prop) (V : ProgramState → ℤ) (k : ℤ) (ε : ENNReal)
    (hpre : ∀ σ, P σ → I σ)
    (hbound : ∀ σ, P σ → c.get σ = false → bd σ = g σ)
    (hterm : ∀ σ, I σ → V σ ≤ k ∧ (V σ ≤ 0 → c.get σ = false))
    (hbody : ∀ w : Stmt, phoareStmt P w g Eq bd →
      phoareStmt (fun σ => P σ ∧ c.get σ = true) (.seq body w) g Eq bd)
    (hinv : phoareStmt (fun σ => I σ ∧ c.get σ = true) body (fun τ => indicatorE (I τ)) Eq
      (fun _τ => 1))
    (hε0 : ε ≠ 0)
    (hvar : ∀ z, phoareStmt (fun σ => I σ ∧ c.get σ = true ∧ V σ = z) body
      (fun τ => indicatorE (V τ < z)) GE.ge (fun _τ => ε))
    (hg1 : ∀ τ, g τ ≤ 1) (hbd1 : ∀ σ, P σ → bd σ ≤ 1) (hsat : ∃ τ, g τ = 1) :
    phoareStmt P (StmtWithHoles.while c body) g Eq bd := by
  intro σ hP
  obtain ⟨τ₁, hτ₁⟩ := hsat
  have hterm1 : Stmt.ewp (StmtWithHoles.while c body) (fun _ => 1) σ = 1 :=
    Stmt.ewp_while_one_of_variant I V k ε hε0 hterm (fun τ h1 h2 => hinv τ ⟨h1, h2⟩)
      (fun τ h1 h2 => hvar (V τ) τ ⟨h1, h2, rfl⟩) σ (hpre σ hP)
  -- one round, then an expectation that is the bound on `P`: the bound again
  have hround : ∀ J : ProgramState → ENNReal, (∀ τ, J τ ≤ 1) → (∀ τ, P τ → J τ = bd τ) →
      ∀ τ, P τ → c.get τ = true → body.ewp J τ = bd τ := by
    intro J hJ1 hJ τ hτ hc
    have h := hbody (Stmt.jumpWith J hJ1 τ₁)
      (fun ρ hρ => by rw [Stmt.ewp_jumpWith, hτ₁, mul_one, hJ ρ hρ]) τ ⟨hτ, hc⟩
    rw [Stmt.ewp_seq] at h
    rw [← h]
    exact congrArg (fun F => body.ewp F τ) (funext fun ρ => by
      rw [Stmt.ewp_jumpWith, hτ₁, mul_one])
  -- from above: the bound on `P`, `1` elsewhere, is an invariant
  let J : ProgramState → ENNReal := fun τ => if P τ then bd τ else 1
  have hJ1 : ∀ τ, J τ ≤ 1 := fun τ => by
    simp only [J]; split_ifs with h
    · exact hbd1 τ h
    · exact le_rfl
  have hJ : ∀ τ, P τ → J τ = bd τ := fun τ h => if_pos h
  have hup : Stmt.ewp (StmtWithHoles.while c body) g σ ≤ J σ := by
    refine Stmt.ewp_while_le J g (fun τ hc => ?_) (fun τ hc => ?_) σ
    · by_cases hτ : P τ
      · rw [hround J hJ1 hJ τ hτ hc, hJ τ hτ]
      · have : J τ = 1 := if_neg hτ
        rw [this]; exact (Stmt.ewp_mono _ hJ1 τ).trans (Stmt.ewp_const_le _ 1 τ)
    · by_cases hτ : P τ
      · rw [hJ τ hτ, hbound τ hτ hc]
      · have : J τ = 1 := if_neg hτ
        rw [this]; exact hg1 τ
  -- from below, by complement: the loop terminates
  let J' : ProgramState → ENNReal := fun τ => if P τ then bd τ else 0
  have hJ'1 : ∀ τ, J' τ ≤ 1 := fun τ => by
    simp only [J']; split_ifs with h
    · exact hbd1 τ h
    · exact zero_le_one
  have hJ' : ∀ τ, P τ → J' τ = bd τ := fun τ h => if_pos h
  have hlow : Stmt.ewp (StmtWithHoles.while c body) (fun τ => 1 - g τ) σ ≤ 1 - J' σ := by
    refine Stmt.ewp_while_le (fun τ => 1 - J' τ) _ (fun τ hc => ?_) (fun τ hc => ?_) σ
    · by_cases hτ : P τ
      · have hll : body.ewp (fun _ => 1) τ = 1 :=
          Stmt.ewp_one_of_certain body (hinv τ ⟨hpre τ hτ, hc⟩)
        rw [Stmt.ewp_one_sub body hJ'1 hll, hround J' hJ'1 hJ' τ hτ hc, hJ' τ hτ]
      · have : J' τ = 0 := if_neg hτ
        rw [this, tsub_zero]
        exact (Stmt.ewp_mono _ (fun _ => tsub_le_self) τ).trans (Stmt.ewp_const_le _ 1 τ)
    · by_cases hτ : P τ
      · rw [hJ' τ hτ, hbound τ hτ hc]
      · have : J' τ = 0 := if_neg hτ
        rw [this, tsub_zero]; exact tsub_le_self
  rw [Stmt.ewp_one_sub _ hg1 hterm1, hJ' σ hP] at hlow
  have hfin : Stmt.ewp (StmtWithHoles.while c body) g σ ≤ 1 :=
    (Stmt.ewp_mono _ hg1 σ).trans (Stmt.ewp_const_le _ 1 σ)
  refine le_antisymm (by rw [← hJ σ hP]; exact hup) ?_
  calc bd σ = 1 - (1 - bd σ) := (ENNReal.sub_sub_cancel ENNReal.one_ne_top (hbd1 σ hP)).symm
    _ ≤ 1 - (1 - Stmt.ewp (StmtWithHoles.while c body) g σ) := tsub_le_tsub_left hlow 1
    _ = _ := ENNReal.sub_sub_cancel ENNReal.one_ne_top hfin

/-- `phoareStmt_while_rev_eq` with the rate a real, as EC writes it. -/
theorem phoareStmt_while_rev_eq_ofReal {P : ProgramState → Prop} {body : Stmt}
    {c : Getter Bool ProgramState} {g bd : ProgramState → ENNReal}
    (I : ProgramState → Prop) (V : ProgramState → ℤ) (k : ℤ) (ε : ℝ)
    (hpre : ∀ σ, P σ → I σ)
    (hbound : ∀ σ, P σ → c.get σ = false → bd σ = g σ)
    (hterm : ∀ σ, I σ → V σ ≤ k ∧ (V σ ≤ 0 → c.get σ = false))
    (hbody : ∀ w : Stmt, phoareStmt P w g Eq bd →
      phoareStmt (fun σ => P σ ∧ c.get σ = true) (.seq body w) g Eq bd)
    (hinv : phoareStmt (fun σ => I σ ∧ c.get σ = true) body (fun τ => indicatorE (I τ)) Eq
      (fun _τ => 1))
    (hε0 : 0 < ε)
    (hvar : ∀ z, phoareStmt (fun σ => I σ ∧ c.get σ = true ∧ V σ = z) body
      (fun τ => indicatorE (V τ < z)) GE.ge (fun _τ => ENNReal.ofReal ε))
    (hg1 : ∀ τ, g τ ≤ 1) (hbd1 : ∀ σ, P σ → bd σ ≤ 1) (hsat : ∃ τ, g τ = 1) :
    phoareStmt P (StmtWithHoles.while c body) g Eq bd :=
  phoareStmt_while_rev_eq I V k (ENNReal.ofReal ε) hpre hbound hterm hbody hinv
    (by simpa using hε0) hvar hg1 hbd1 hsat

namespace PHoareWp

open Lean Meta Elab Tactic

/-- EC's `while I V k ε` on `phoareStmt P (while c body) g = bd` (`phoareStmt_while_rev_eq`):
EC's goals in its order — `pre_inv`, `pre_bound`, `term`, `body`, `inv`, `rate` (`0 < ε`),
`variant` — then `post_le_one`, `bound_le_one`, `sat`.  The goals that are not judgments are
closed when trivial (EC's `=> //`). -/
def phoareWhileRevStep (I V k ε : Lean.Expr) (g : MVarId) : TacticM (List MVarId) :=
    g.withContext do
  let rule ← mkConstWithFreshMVarLevels ``phoareStmt_while_rev_eq_ofReal
  let (ms, _, ty) ← forallMetaTelescope (← inferType rule)
  let names := (← inferType rule).getForallBinderNames
  let arg (n : Name) : MetaM Lean.Expr := do
    let some i := names.findIdx? (· == n) | throwError "phoare_while: no argument `{n}`"
    return ms[i]!
  for (n, e, what) in [(`I, I, "the invariant is not a condition on the program state"),
      (`V, V, "the variant is not an integer on the program state"),
      (`k, k, "the variant's bound is not an integer"),
      (`ε, ε, "the rate is not a real")] do
    unless ← isDefEq (← arg n) e do throwError "phoare_while: {what}"
  unless ← isDefEq ty (← g.getType) do
    throwError "phoare_while: the goal is not an exact `phoare` judgment about a loop alone \
      (EC's rule wants the loop to be the only statement: `seq` first):{indentExpr (← g.getType)}"
  g.assign (mkAppN rule ms)
  let tagged (n tag : Name) : MetaM MVarId := do
    let m := (← arg n).mvarId!
    m.setTag tag
    return m
  -- the conditions about values: over values, closed when trivial
  let mut out : List MVarId := []
  let pure' (n tag : Name) (close : TSyntax `tactic) : TacticM (List MVarId) := do
    let m ← tagged n tag
    let m ← try cleanSideGoal m catch _ => pure m
    let s ← saveState
    try evalTacticAt close m catch _ => do s.restore; pure [m]
  let triv ← `(tactic| (intros; first | trivial | (simp; done)))
  out := out ++ (← pure' `hpre `pre_inv triv)
  out := out ++ (← pure' `hbound `pre_bound triv)
  out := out ++ (← pure' `hterm `term triv)
  out := out ++ [← tagged `hbody `body, ← tagged `hinv `inv]
  out := out ++ (← pure' `hε0 `rate triv)
  out := out ++ [← tagged `hvar `variant]
  let le1 ← `(tactic| (intros; first | trivial | (le_one; done)))
  out := out ++ (← pure' `hg1 `post_le_one le1)
  out := out ++ (← pure' `hbd1 `bound_le_one le1)
  -- some state reaches the postcondition: any state, when it is `true`
  let m ← tagged `hsat `sat
  let s ← saveState
  let rest ← try evalTacticAt (← `(tactic| first
      | exact ⟨⟨VariableAssignment.init, VariableAssignment.init⟩, rfl⟩
      | exact ⟨⟨VariableAssignment.init, VariableAssignment.init⟩, indicatorE_of trivial⟩)) m
    catch _ => do s.restore; pure [m]
  out := out ++ rest
  return out

end PHoareWp

open Lean Elab Tactic PHoareWp in
/-- **EC's `while I V k ε`** on `phoare[ while b c : P ==> Q ] = r` (the loop alone): the
invariant `I` and the integer variant `V` written like the judgment's conditions, `k` an
integer and `ε` a real.  See `phoareStmt_while_rev_eq` for the goals. -/
elab "phoare_while " I:term:max ppSpace V:term:max ppSpace k:term:max ppSpace ε:term:max :
    tactic => withMainContext do
  let Ie ← elabGoalFunction I (mkSort 0)
  let Ve ← elabGoalFunction V (mkConst ``Int)
  let ke ← Term.elabTermEnsuringType k (mkConst ``Int)
  let εe ← Term.elabTermEnsuringType ε (mkConst ``Real)
  Term.synthesizeSyntheticMVarsNoPostponing
  let gs ← phoareWhileRevStep Ie Ve (← instantiateMVars ke) (← instantiateMVars εe)
    (← getMainGoal)
  replaceMainGoal gs

end GaudisCrypt
