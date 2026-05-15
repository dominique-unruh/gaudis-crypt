import PlonkLean.Semantics


/-!
# Discrete subprobability monad
-/

/-- Expected value of f under the distribution μ -/
noncomputable
def SubProbability.expected (μ : SubProbability a) (f : a → ENNReal) : ENNReal :=
  ∫⁻ x, f x ∂μ.1

theorem uniform_expected [Fintype a] [Nonempty a] (f: a → ENNReal):
  SubProbability.uniform.expected f = ∑ x:a, f x / Fintype.card a
  := sorry

theorem expected_pure (x : a) : (pure x : SubProbability a).expected f = f x := by
  have h : (pure x : SubProbability a) = ⟨@MeasureTheory.Measure.dirac _ ⊤ x, _⟩ := rfl
  simp [SubProbability.expected, h]

/-!

# Stateful programs

-/

@[reducible]
def Program.WP s a := a × s → ENNReal

noncomputable
def Program.wp (prog : Program s a) (f : Program.WP s a) (st : s) : ENNReal :=
  (prog st).expected f

theorem final_probability_wp [DecidableEq a] (prog : Program s a) st x :
  ↑(prog.finalProb1 st x) = prog.wp (fun (y, _) => if y = x then 1 else 0) st :=
    sorry

theorem final_probability_wp' [DecidableEq a] (prog : Program s a) st x :
  prog.finalProb1 st x = (prog.wp (fun (y, _) => if y = x then 1 else 0) st).toNNReal :=
    sorry

theorem wp_lift (μ : SubProbability a) : μ.toProgram.wp f = fun st => μ.expected (fun x => f (x,st))
  := sorry

theorem wp_uniform [h : Fintype a] [h : Nonempty a] (f : Program.WP s a) :
  Program.uniform.wp f = (fun s => ∑ i:a, f (i,s) / Fintype.card a) := by
  simp [wp_lift, Program.uniform, uniform_expected]

theorem wp_bind {α β : Type} (prog : Program s α) (f : α → Program s β)
    (g : Program.WP s β) (st : s) :
    (prog >>= f).wp g = prog.wp (fun (a, s') => (f a).wp g s') := by
  sorry

theorem wp_pure {s α : Type} (x : α) (f : Program.WP s α) :
    (pure x : Program s α).wp f = fun st => f (x, st) := by
    have h : (pure x : Program s α) = fun s => pure (x, s) := rfl  -- Can't we somehow unfold `pure x` without auxiliary def?
    ext
    simp [h, Program.wp, expected_pure]

theorem wp_ite {α : Type} (b : Bool) (p1 p2 : Program s α)
    (f : α × s → ENNReal) (st : s) :
    (if b then p1 else p2).wp f st = if b then p1.wp f st else p2.wp f st := by
  cases b <;> rfl

theorem wp_set (st' : s) (f : Unit × s → ENNReal) (st : s) :
    Program.wp (StateT.set st' : Program s Unit) f st = f ((), st') := by  -- Why doesn't (...).wp syntax work?
  simp [Program.wp, StateT.set, expected_pure]

theorem wp_get (f : Program.WP s s) (st : s) :
    Program.wp (StateT.get) f st = f (st, st) := by
  simp [Program.wp, StateT.get, expected_pure]
