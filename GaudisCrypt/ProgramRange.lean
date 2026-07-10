import GaudisCrypt.Language.Semantics
import GaudisCrypt.WeakestPreconditions
import GaudisCrypt.DetermFootprint

open GaudisCrypt

namespace GaudisCrypt

/-!
# ProgramDenotation.range and `glob` foundations  — **LEGACY `DetermFootprint` theory
    (quarantined)**

> **Deprecated / quarantined.** This is the deterministic `DetermFootprint`/`inRange` program-range
> theory, superseded by `Footprint` + `ProbProgramRange` (the `inFootprint` analogues — they are
> countability-free and a read's range does not collapse). Retained only for `CounterExamples` (which
> need the `DetermFootprint` pathology) and for `QueryHit.lean` (via `Lib/RO/LegacyRange.lean`, the
> last not-yet-migrated consumer); new code should use `Footprint`/`inFootprint`. The probabilistic
> wp-layer lives in `ProbProgramRange`; the range-free generic material that used to live here
> (`liftF`, `loop_n`, `up_to_bad`, `IgnoresLens`, `Lens.lift`/`factor`, …) is now in
> `WeakestPreconditions`.

This file defines

* `liftF`, which embeds a deterministic state-update `f : s → s` as a `ProgramDenotation s Unit`,
* `ProgramDenotation.inRange p R`, capturing that `p`'s reads and writes live in the region `R`,
* `ProgramDenotation.range p`, the smallest such `R` (via `sInf`),
* `ProgramDenotation.range'`, the family-version for `a → ProgramDenotation s b`.

The definition uses the commutant `Rᶜ` (`Compl` instance from `DetermFootprint.lean`): `p` lies
in `R` iff `p` commutes with everything outside `R`. By the bicommutant closure of `DetermFootprint`,
this is equivalent to "the actions of `p` (lifted to deterministic updates) lie in `R`".
-/


/-- A program is *in* a DetermFootprint `R` iff it commutes with every update in `Rᶜ`
    (the commutant of `R`). By bicommutant closure, this is equivalent to
    "every state-transition `p` can perform lies in `R`".

    The two sides are compared as `ProgramDenotation s a`: on the left, `f` runs before `p`
    and `p`'s return is preserved; on the right, `p`'s return is captured, then
    `f` runs, then the saved return is produced. -/
def _root_.GaudisCrypt.ProgramDenotation.inRange {s a : Type} (p :
    ProgramDenotation s a) (R : DetermFootprint s) : Prop :=
  ∀ f ∈ Rᶜ.updates,
    (liftF f >>= fun _ => p)
  = (p >>= fun x => liftF f >>= fun _ => pure x)

/-- The smallest DetermFootprint in which `p` lives. -/
noncomputable def _root_.GaudisCrypt.ProgramDenotation.range {s a : Type} (p :
    ProgramDenotation s a) : DetermFootprint s :=
  sInf { R | p.inRange R }

/-- Family version: the smallest DetermFootprint in which every `progs x` lives.
    Equivalently the supremum `⨆ x, (progs x).range`. -/
noncomputable def ProgramDenotation.range' {s a b : Type} (progs : a → ProgramDenotation s b) :
    DetermFootprint s :=
  sInf { R | ∀ x, (progs x).inRange R }

/-! ## `glob`: the global variables read/written by a program -/

/-- The *type* of `A`'s global variables: the quotient of state by
    `(A.range)ᶜ`-orbit equivalence. Two states have the same `Globals` value
    iff they differ only by an update outside `A`'s range — i.e., they are
    indistinguishable from `A`'s perspective. Use this anywhere
    `Quotient (A.range)ᶜ.orbit_setoid` would otherwise appear. -/
noncomputable abbrev _root_.GaudisCrypt.ProgramDenotation.Globals {s a : Type} (A
    : ProgramDenotation s a) : Type :=
  Quotient (A.range)ᶜ.orbit_setoid

/-- Family-version type: the globals of the parameterized family `progs`. -/
noncomputable abbrev ProgramDenotation.Globals' {s a b : Type} (progs : a → ProgramDenotation s b) :
    Type :=
  Quotient (ProgramDenotation.range' progs)ᶜ.orbit_setoid

/-- The global variables of `A` — a Getter projecting `state s` onto the data
    `A` can observe or modify. Built from `A.range` via the DetermFootprint-level
    `touched_getter` (which uses the *commutant* `Rᶜ`-orbit equivalence). -/
noncomputable def ProgramDenotation.glob {s a : Type} (A : ProgramDenotation s a) :
    Getter A.Globals s :=
  A.range.touched_getter

/-- Family version of `glob`. -/
noncomputable def ProgramDenotation.glob' {s a b : Type} (progs : a → ProgramDenotation s b) :
    Getter (ProgramDenotation.Globals' progs) s :=
  (ProgramDenotation.range' progs).touched_getter

/-! ## Structural lemmas -/

/-- `pure x` is in every range — it touches no state. -/
theorem ProgramDenotation.inRange_pure {s a : Type} (x : a) (R : DetermFootprint s) :
    (pure x : ProgramDenotation s a).inRange R := by
  intro f _
  -- LHS: liftF f; pure x
  -- RHS: pure x ; liftF f ; pure x' = liftF f ; pure x   (by pure_bind on the outer)
  rw [ProgramDenotation.pure_bind]

/-- Bind composition: if `p` and every `f x` live in `R`, then so does `p >>= f`. -/
theorem ProgramDenotation.inRange_bind {s a b : Type}
    {p : ProgramDenotation s a} {f : a → ProgramDenotation s b} {R : DetermFootprint s}
    (hp : p.inRange R) (hf : ∀ x, (f x).inRange R) :
    (p >>= f).inRange R := by
  intro g hg
  calc (liftF g >>= fun _ => p >>= f)
      = ((liftF g >>= fun _ => p) >>= f) := by rw [ProgramDenotation.bind_assoc]
    _ = ((p >>= fun x => liftF g >>= fun _ => pure x) >>= f) := by rw [hp g hg]
    _ = (p >>= fun x => (liftF g >>= fun _ => pure x) >>= f) := by rw [ProgramDenotation.bind_assoc]
    _ = (p >>= fun x => liftF g >>= fun _ => pure x >>= f) := by
            congr 1; funext x; rw [ProgramDenotation.bind_assoc]
    _ = (p >>= fun x => liftF g >>= fun _ => f x) := by
            congr 1; funext x; congr 1; funext _; rw [ProgramDenotation.pure_bind]
    _ = (p >>= fun x => f x >>= fun y => liftF g >>= fun _ => pure y) := by
            congr 1; funext x; exact hf x g hg
    _ = ((p >>= f) >>= fun y => liftF g >>= fun _ => pure y) := by
            rw [ProgramDenotation.bind_assoc]

/-- Monotonicity: a larger range still contains the program. -/
theorem ProgramDenotation.inRange_mono {s a : Type} {p : ProgramDenotation s a} {R R' :
    DetermFootprint s}
    (h : p.inRange R) (hR : R ≤ R') : p.inRange R' := by
  intro f hf
  -- R ≤ R' implies R'ᶜ ≤ Rᶜ, so f ∈ R'ᶜ ⊆ Rᶜ.
  -- We show f ∈ Rᶜ via the antitone property of complement.
  apply h
  -- need: f ∈ Rᶜ.updates, given f ∈ R'ᶜ.updates and R ≤ R'
  -- Rᶜ.updates = centralizer of R.updates
  -- R'ᶜ.updates = centralizer of R'.updates
  -- R ≤ R' means R.updates ⊆ R'.updates
  -- centralizer is antitone in the input, so centralizer R'.updates ⊆ centralizer R.updates
  -- i.e., R'ᶜ.updates ⊆ Rᶜ.updates
  have : R'ᶜ.updates ⊆ Rᶜ.updates := by
    change (Submonoid.centralizer R'.updates).carrier ⊆ (Submonoid.centralizer R.updates).carrier
    exact Submonoid.centralizer_le hR
  exact this hf


/-! ## Primitive `inRange` lemmas

These say that a primitive program (`uniform`, `set`, `get`) lives in the obvious range.
-/

/-- `ProgramDenotation.uniform` lives in the trivial range (it doesn't touch state). -/
theorem ProgramDenotation.inRange_uniform {s α : Type} [Fintype α] [Nonempty α] :
    (ProgramDenotation.uniform : ProgramDenotation s α).inRange ⊥ := by
  intro f _
  apply ProgramDenotation.ext_of_wp
  intro F
  funext σ
  simp only [wp_bind, wp_liftF, wp_uniform, wp_pure]

/-- `ProgramDenotation.uniformOfFinset` lives in the trivial range (it doesn't touch
    state — it only samples its return value). -/
theorem ProgramDenotation.inRange_uniformOfFinset {s α : Type} [Fintype α]
    (fs : Finset α) (hs : fs.Nonempty) :
    (ProgramDenotation.uniformOfFinset fs hs : ProgramDenotation s α).inRange ⊥ := by
  intro f _
  apply ProgramDenotation.ext_of_wp
  intro F
  funext σ
  simp only [wp_bind, wp_liftF, wp_uniformOfFinset, wp_pure]

/-- `ProgramDenotation.set v x` lives in `v.range`. -/
theorem ProgramDenotation.inRange_set {s a : Type} (v : Lens a s) (x : a) :
    (ProgramDenotation.set v x).inRange v.range := by
  intro f hf
  -- Step 1: extract lens-commutativity from `hf : f ∈ v.rangeᶜ.updates`.
  have h_comm : ∀ σ : s, v.set x (f σ) = f (v.set x σ) := by
    intro σ
    have hmem : f ∈ Submonoid.centralizer v.range.updates := hf
    rw [Submonoid.mem_centralizer_iff] at hmem
    have hvx : v.liftFunction (Function.const _ x) ∈ v.range.updates :=
      ⟨Function.const _ x, Set.mem_univ _, rfl⟩
    have hcomm := congr_fun (hmem _ hvx) σ
    change v.liftFunction (Function.const _ x) (f σ) = f (v.liftFunction (Function.const _ x) σ) at hcomm
    show v.set x (f σ) = f (v.set x σ)
    simp only [Lens.liftFunction, Function.const_apply] at hcomm
    exact hcomm
  -- Step 2: prove the equation via wp.
  apply ProgramDenotation.ext_of_wp
  intro F
  funext σ
  simp only [wp_bind, wp_liftF, wp_set, wp_pure]
  -- LHS reduces to F ((), v.set x (f σ)); RHS reduces to F ((), f (v.set x σ)).
  exact congr_arg (fun st : s => F ((), st)) (h_comm σ)


/-- `ProgramDenotation.get v` lives in `v.range`: it reads from `v`, doesn't write. -/
theorem ProgramDenotation.inRange_get {s a : Type} (v : Lens a s) :
    (ProgramDenotation.get v).inRange v.range := by
  intro f hf
  -- Extract: f preserves v.get.
  have h_get_pres : ∀ σ : s, v.get (f σ) = v.get σ := by
    intro σ
    have hmem : f ∈ Submonoid.centralizer v.range.updates := hf
    rw [Submonoid.mem_centralizer_iff] at hmem
    have hv_upd : v.liftFunction (Function.const _ (v.get σ)) ∈ v.range.updates :=
      ⟨Function.const _ (v.get σ), Set.mem_univ _, rfl⟩
    have hcomm := congr_fun (hmem _ hv_upd) σ
    change v.liftFunction (Function.const _ (v.get σ)) (f σ)
         = f (v.liftFunction (Function.const _ (v.get σ)) σ) at hcomm
    simp only [Lens.liftFunction, Function.const_apply] at hcomm
    rw [v.get_set] at hcomm
    -- hcomm: v.set (v.get σ) (f σ) = f σ
    have := congr_arg v.get hcomm
    rw [v.set_get] at this
    exact this.symm
  -- Prove the inRange equation via wp.
  apply ProgramDenotation.ext_of_wp
  intro F
  funext σ
  simp only [wp_bind, wp_liftF, wp_get, wp_pure]
  -- LHS: F (v.get (f σ), f σ); RHS: F (v.get σ, f σ).
  rw [h_get_pres]

/-- **`ProgramDenotation.set` is in `L.compl.range`** when the setter `v` is disjoint
    from the reader `L`. Common one-liner replacing
    `inRange_mono (inRange_set _ _) (Lens.range_le_compl_of_disjoint v L)`. -/
lemma ProgramDenotation.set_inRange_compl_of_disjoint
    {s α β : Type} (v : Lens α s) (L : Lens β s) [disjoint v L] (x : α) :
    (ProgramDenotation.set v x).inRange L.compl.range :=
  ProgramDenotation.inRange_mono (ProgramDenotation.inRange_set v x)
    (Lens.range_le_compl_of_disjoint v L)

/-- **`ProgramDenotation.get` is in `L.compl.range`** when the reader `v` is disjoint
    from `L`. Common one-liner replacing
    `inRange_mono (inRange_get _) (Lens.range_le_compl_of_disjoint v L)`. -/
lemma ProgramDenotation.get_inRange_compl_of_disjoint
    {s α β : Type} (v : Lens α s) (L : Lens β s) [disjoint v L] :
    (ProgramDenotation.get v).inRange L.compl.range :=
  ProgramDenotation.inRange_mono (ProgramDenotation.inRange_get v)
    (Lens.range_le_compl_of_disjoint v L)


/-- `loop_n n body` stays in the same range as `body`. -/
lemma loop_n_inRange {s : Type} {R : DetermFootprint s}
    (body : ProgramDenotation s Unit) (h_body : body.inRange R) (n : ℕ) :
    (loop_n n body).inRange R := by
  induction n with
  | zero => exact ProgramDenotation.inRange_pure _ _
  | succ n ih =>
    show (body >>= fun _ => loop_n n body).inRange R
    exact ProgramDenotation.inRange_bind h_body (fun _ => ih)


/-! ## SubProbability-level characterization of `inRange` -/

/-- `inRange` lifted to the SubProbability level: at state `σ`, applying a commutant update
    `f ∈ Rᶜ` *before* `p` gives the same distribution as running `p` first and then applying
    `f` to the state coordinate of each outcome. -/
lemma ProgramDenotation.inRange_subprob {s a : Type} {p : ProgramDenotation s a} {R :
    DetermFootprint s}
    (hp : p.inRange R) {f : s → s} (hf : f ∈ Rᶜ.updates) (σ : s) :
    p (f σ) = (p σ) >>= (fun (xs : a × s) => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
  have h_eq := congr_fun (hp f hf) σ
  -- LHS of h_eq simplifies to p (f σ) via SubProbability.pure_bind.
  have hL : (liftF f >>= fun _ => p) σ = p (f σ) := by
    show (liftF f σ) >>= (fun (us : Unit × s) => p us.2) = p (f σ)
    show (pure ((), f σ) : SubProbability (Unit × s)) >>= (fun (us : Unit × s) => p us.2)
       = p (f σ)
    rw [SubProbability.pure_bind]
  -- RHS of h_eq simplifies to (p σ) >>= (fun (x, s') => pure (x, f s')).
  have hR : (p >>= fun x => liftF f >>= fun _ => pure x) σ
          = (p σ) >>= (fun (xs : a × s) => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
    show (p σ) >>= (fun (xs : a × s) => (liftF f >>= fun _ => (pure xs.1 : ProgramDenotation s a))
        xs.2)
       = (p σ) >>= (fun (xs : a × s) =>
                       (pure (xs.1, f xs.2) : SubProbability (a × s)))
    congr 1
    funext xs
    obtain ⟨x, s'⟩ := xs
    show (liftF f s') >>= (fun (us : Unit × s) => (pure (x, us.2) : SubProbability (a × s)))
       = (pure (x, f s') : SubProbability (a × s))
    show (pure ((), f s') : SubProbability (Unit × s))
           >>= (fun (us : Unit × s) => (pure (x, us.2) : SubProbability (a × s)))
       = (pure (x, f s') : SubProbability (a × s))
    rw [SubProbability.pure_bind]
  rw [← hL, h_eq, hR]


/-- wp form of `inRange`: shifting the input state by `f ∈ Rᶜ` is equivalent to
    post-composing `f` on the state coordinate of the postcondition. -/
lemma ProgramDenotation.wp_shift_input {s a : Type} {p : ProgramDenotation s a} {R : DetermFootprint
    s}
    (hp : p.inRange R) {f : s → s} (hf : f ∈ Rᶜ.updates) (F : a × s → ENNReal) (σ : s) :
    p.wp F (f σ) = p.wp (fun (xs : a × s) => F (xs.1, f xs.2)) σ := by
  show (p (f σ)).expected F = (p σ).expected (fun (xs : a × s) => F (xs.1, f xs.2))
  rw [ProgramDenotation.inRange_subprob hp hf σ]
  rw [SubProbability.expected_bind]
  congr 1
  funext xs
  rw [expected_pure]

/-- **Lens-preservation strengthening**: if `prog` modifies only the complement
    of `L`, then on the support of `prog σ` every output state has the same
    `L.get` as `σ`. We can therefore strengthen the postcondition with an
    `if L.get = L.get σ then F else 0` check without changing the `wp` value.

    Proved by a double-shift via `ProgramDenotation.wp_shift_input`: shifting `F` and the
    strengthened post by `f := L.liftFunction (Function.const _ (L.get σ))` (which
    forces `L.get` to `L.get σ`) makes both inner posts identical, so the
    `wp` values match. -/
lemma ProgramDenotation.wp_strengthen_lens_preserved {s α γ : Type} [DecidableEq γ]
    (L : Lens γ s) {p : ProgramDenotation s α} (h_inRange : p.inRange L.compl.range)
    (F : α × s → ENNReal) (σ : s) :
    p.wp F σ
      = p.wp (fun aσ' : α × s => if L.get aσ'.2 = L.get σ then F aσ' else 0) σ := by
  set f : s → s := L.liftFunction (Function.const _ (L.get σ)) with hf_def
  have h_f_in_Rc : f ∈ ((L.compl.range : DetermFootprint s)ᶜ).updates := by
    rw [show ((L.compl.range : DetermFootprint s)ᶜ) = L.range from by
      rw [DetermFootprint.complement_range, DetermFootprint.compl_compl]]
    exact ⟨Function.const _ (L.get σ), Set.mem_univ _, rfl⟩
  have h_f_fix : f σ = σ := by
    show L.set ((Function.const _ (L.get σ)) (L.get σ)) σ = σ
    rw [Function.const_apply, L.get_set]
  have h_f_L_get : ∀ σ' : s, L.get (f σ') = L.get σ := by
    intro σ'
    show L.get (L.set ((Function.const _ (L.get σ)) (L.get σ')) σ') = L.get σ
    rw [Function.const_apply, L.set_get]
  have h_shift_F := ProgramDenotation.wp_shift_input h_inRange h_f_in_Rc F σ
  rw [h_f_fix] at h_shift_F
  have h_shift_strong := ProgramDenotation.wp_shift_input h_inRange h_f_in_Rc
    (fun aσ' : α × s => if L.get aσ'.2 = L.get σ then F aσ' else 0) σ
  rw [h_f_fix] at h_shift_strong
  rw [h_shift_F, h_shift_strong]
  congr 1
  funext xs
  show F (xs.1, f xs.2) = if L.get (f xs.2) = L.get σ then F (xs.1, f xs.2) else 0
  rw [if_pos (h_f_L_get xs.2)]


namespace IgnoresLens

/-- L-ignoring is preserved when post-composing with an L-disjoint program. -/
lemma comp_inRange {γ s α β : Type} [DecidableEq γ] {L : Lens γ s}
    {F : β × s → ENNReal} (h_F : IgnoresLens L F)
    (k : α → ProgramDenotation s β) (h_k : ∀ a, (k a).inRange L.compl.range) :
    IgnoresLens L (fun aσ : α × s => (k aσ.1).wp F aσ.2) := by
  intro aσ v
  have hf : (fun s' : s => L.set v s') ∈ ((L.compl.range : DetermFootprint s)ᶜ).updates := by
    rw [show ((L.compl.range : DetermFootprint s)ᶜ) = L.range from by
        rw [DetermFootprint.complement_range, DetermFootprint.compl_compl]]
    exact ⟨Function.const _ v, Set.mem_univ _, rfl⟩
  show (k aσ.1).wp F (L.set v aσ.2) = (k aσ.1).wp F aσ.2
  rw [ProgramDenotation.wp_shift_input (h_k aσ.1) hf]
  congr 1
  funext xs
  exact h_F xs v

end IgnoresLens

/-- **wp is invariant under `L.set v` on input** when `p` is `L`-disjoint and
    `F` is invariant under `L.set v` on its state argument. The intuition:
    writing `v` into `L` before `p` is invisible because `p` doesn't read
    `L`, and `F` doesn't see the `L`-content of the output.

    Note: the hypothesis on `F` is *single-value* (only requires invariance
    at this `v`), not the full `IgnoresLens` (invariance at every value).
    Callers that have the stronger `IgnoresLens L F` can supply
    `fun aσ => h_F aσ v`. -/
lemma ProgramDenotation.wp_invariant_under_lens_set
    {s α γ : Type} [DecidableEq γ] (L : Lens γ s)
    {p : ProgramDenotation s α} (h_p : p.inRange L.compl.range)
    (v : γ) {F : α × s → ENNReal}
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    p.wp F (L.set v σ) = p.wp F σ := by
  have h_f_updates : L.liftFunction (Function.const _ v)
      ∈ ((L.compl.range : DetermFootprint s)ᶜ).updates := by
    rw [show ((L.compl.range : DetermFootprint s)ᶜ) = L.range from by
        rw [DetermFootprint.complement_range, DetermFootprint.compl_compl]]
    exact ⟨Function.const _ v, Set.mem_univ _, rfl⟩
  have h_set_eq : L.liftFunction (Function.const _ v) σ = L.set v σ := by
    show L.set ((Function.const _ v) (L.get σ)) σ = L.set v σ
    rfl
  rw [← h_set_eq]
  rw [ProgramDenotation.wp_shift_input h_p h_f_updates]
  congr 1
  funext xs
  show F (xs.1, L.liftFunction (Function.const _ v) xs.2) = F xs
  show F (xs.1, L.set v xs.2) = F xs
  exact h_F xs

/-- **Conditional set is wp-invisible at posts that ignore the set value**.
    `if c then set L v else pure ()` has wp equal to `F ((), σ)` for any
    post `F` that doesn't observe `L.set v`. Both branches converge:
    when `c` holds, `set L v` is invisible by `h_F`; otherwise `pure ()`
    is a no-op. Captures the "conditional tracking write" pattern. -/
lemma ProgramDenotation.wp_cond_set_invisible
    {s γ : Type} (L : Lens γ s) (cond : Prop) [Decidable cond] (v : γ)
    (F : Unit × s → ENNReal)
    (h_F : ∀ aσ : Unit × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    (if cond then ProgramDenotation.set L v else (pure () : ProgramDenotation s Unit)).wp F σ
    = F ((), σ) := by
  by_cases h : cond
  · rw [if_pos h, wp_set]
    exact h_F ((), σ)
  · rw [if_neg h, wp_pure]

/-- **Read-modify-write on `L` is wp-invisible at `L`-ignoring posts**.
    `get L >>= fun a => set L (g a)` has the same wp as `pure ()` for any
    pure modification `g : γ → γ` of the lens value, provided the post `F`
    doesn't read `L`. Captures the "tracking variable updated in place"
    pattern: the modification is invisible if downstream code doesn't
    observe `L`. -/
lemma ProgramDenotation.wp_get_modify_invisible
    {s γ : Type} (L : Lens γ s) (g : γ → γ)
    (F : Unit × s → ENNReal) (h_F : IgnoresLens L F) (σ : s) :
    (ProgramDenotation.get L >>= fun a : γ => ProgramDenotation.set L (g a)).wp F σ = F ((),
        σ) := by
  rw [wp_bind, wp_get]
  dsimp only
  rw [wp_set]
  exact h_F ((), σ) _

/-- **Vanishing-post zero**: if `p` is `L`-disjoint, `F` vanishes on every state
    where `L.get = v`, and the input state already has `L.get σ = v`, then
    `p.wp F σ = 0`. Captures the standard "bad-event vanishing" pattern in
    security proofs: once the bad flag is set, all post-outcomes count as bad
    too (and the post assigns them 0), so the wp is 0. -/
lemma ProgramDenotation.wp_zero_of_lens_preserves {s α γ : Type} [DecidableEq γ]
    {L : Lens γ s} {p : ProgramDenotation s α} (h_p : p.inRange L.compl.range)
    {F : α × s → ENNReal} {v : γ}
    (h_F_zero : ∀ aσ : α × s, L.get aσ.2 = v → F aσ = 0)
    {σ : s} (h_σ : L.get σ = v) :
    p.wp F σ = 0 := by
  rw [ProgramDenotation.wp_strengthen_lens_preserved L h_p]
  rw [show (fun aσ : α × s =>
            if L.get aσ.2 = L.get σ then F aσ else 0)
          = (fun _ : α × s => (0 : ENNReal)) from by
    funext aσ
    by_cases h : L.get aσ.2 = L.get σ
    · simp only [if_pos h]
      exact h_F_zero aσ (h.trans h_σ)
    · simp only [if_neg h]]
  exact ProgramDenotation.wp_zero_post _ _

/-- **Drop a dead write**: prepending `ProgramDenotation.set L v` to a program `rest` that
    doesn't touch `L`'s range is a no-op for any post that ignores `L`'s value.
    Useful for cleaning up bookkeeping writes that downstream code doesn't read. -/
lemma ProgramDenotation.wp_set_disjoint_no_op {s γ : Type} [DecidableEq γ] {L : Lens γ s}
    {α : Type} {rest : ProgramDenotation s α} (h_rest : rest.inRange L.compl.range)
    (v : γ) (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    (ProgramDenotation.set L v >>= fun _ => rest).wp F σ = rest.wp F σ := by
  simp only [wp_bind, wp_set]
  set f : s → s := L.liftFunction (Function.const _ v) with hf_def
  have h_f_in_Rc : f ∈ ((L.compl.range : DetermFootprint s)ᶜ).updates := by
    rw [show ((L.compl.range : DetermFootprint s)ᶜ) = L.range from by
      rw [DetermFootprint.complement_range, DetermFootprint.compl_compl]]
    exact ⟨Function.const _ v, Set.mem_univ _, rfl⟩
  have h_f_eq : ∀ σ', f σ' = L.set v σ' := fun σ' => by
    show L.set (Function.const _ v (L.get σ')) σ' = L.set v σ'
    rw [Function.const_apply]
  rw [← h_f_eq σ]
  rw [ProgramDenotation.wp_shift_input h_rest h_f_in_Rc]
  congr 1
  funext xs
  rw [h_f_eq xs.2]
  exact h_F xs

/-- **Conditional dead write**: variant of `wp_set_disjoint_no_op` where the
    `set` is gated by a `Prop`. Useful for the tracking-variable pattern in
    cryptographic proofs, where an auxiliary flag is conditionally written
    inside a loop body whose remainder doesn't read it. -/
lemma ProgramDenotation.wp_conditional_set_disjoint_no_op {s γ : Type} [DecidableEq γ]
    {L : Lens γ s} {α : Type} (cond : Prop) [Decidable cond] (v : γ)
    {rest : ProgramDenotation s α} (h_rest : rest.inRange L.compl.range)
    (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L.set v aσ.2) = F aσ)
    (σ : s) :
    ((if cond then ProgramDenotation.set L v else pure ()) >>= fun _ => rest).wp F σ
    = rest.wp F σ := by
  by_cases h : cond
  · rw [if_pos h]
    exact ProgramDenotation.wp_set_disjoint_no_op h_rest v F h_F σ
  · rw [if_neg h]
    simp only [wp_bind, wp_pure]

/-- **Get-then-conditional-set is a no-op** when the conditional set targets a
    lens whose `compl.range` covers the rest. Captures the common shape
    `get L_get >>= fun cx => (if pred cx then set L_set v else pure) >>= rest`
    used in tracking-variable patterns. -/
lemma ProgramDenotation.wp_get_then_conditional_set_disjoint_no_op
    {s γ δ : Type} [DecidableEq γ] {L_get : Lens δ s} {L_set : Lens γ s}
    {α : Type} (pred : δ → Prop) [DecidablePred pred] (v : γ)
    {rest : ProgramDenotation s α} (h_rest : rest.inRange L_set.compl.range)
    (F : α × s → ENNReal)
    (h_F : ∀ aσ : α × s, F (aσ.1, L_set.set v aσ.2) = F aσ)
    (σ : s) :
    (ProgramDenotation.get L_get >>= fun cx =>
        (if pred cx then ProgramDenotation.set L_set v else (pure () : ProgramDenotation s Unit))
          >>= fun _ => rest).wp F σ
    = rest.wp F σ := by
  rw [wp_bind, wp_get]
  exact ProgramDenotation.wp_conditional_set_disjoint_no_op (pred (L_get.get σ)) v h_rest F h_F σ

/-- **Preservation under in-range**: if `prog` modifies only the complement of `L`,
    and the postcondition factors through `L.get` (i.e. depends only on `L`-content),
    then `prog.wp (P ∘ snd) σ ≤ P σ`. The sub-probability mass of `prog σ` only
    decreases the value below `P σ`. -/
lemma ProgramDenotation.wp_le_of_factors {s α γ : Type} (L : Lens γ s)
    {prog : ProgramDenotation s α} (h_inRange : prog.inRange L.compl.range)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ', L.get σ' = L.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  set f : s → s := L.liftFunction (Function.const _ (L.get σ)) with hf_def
  have h_f_in_Rc : f ∈ ((L.compl.range : DetermFootprint s)ᶜ).updates := by
    rw [show ((L.compl.range : DetermFootprint s)ᶜ) = L.range from by
      rw [DetermFootprint.complement_range, DetermFootprint.compl_compl]]
    exact ⟨Function.const _ (L.get σ), Set.mem_univ _, rfl⟩
  have h_f_fix : f σ = σ := by
    show L.set ((Function.const _ (L.get σ)) (L.get σ)) σ = σ
    rw [Function.const_apply, L.get_set]
  have h_f_P : ∀ σ' : s, P (f σ') = P σ := by
    intro σ'
    apply h_factors
    show L.get (L.set ((Function.const _ (L.get σ)) (L.get σ')) σ') = L.get σ
    rw [Function.const_apply, L.set_get]
  have h_shift := ProgramDenotation.wp_shift_input h_inRange h_f_in_Rc
    (fun xs : α × s => P xs.2) σ
  rw [h_f_fix] at h_shift
  rw [h_shift]
  rw [show (fun xs : α × s => P (f xs.2)) = (fun _ : α × s => P σ) from by
    funext xs; exact h_f_P xs.2]
  exact ProgramDenotation.wp_const_le prog (P σ) σ

/-- **Two-lens preservation**: same idea as `ProgramDenotation.wp_le_of_factors`, but `P`
    factors through the pair `(L₁.get, L₂.get)` and `prog` preserves both
    lenses. Iterates `wp_strengthen_lens_preserved` over two lenses. -/
lemma ProgramDenotation.wp_le_of_factors_two {s α γ₁ γ₂ : Type}
    [DecidableEq γ₁] [DecidableEq γ₂]
    (L₁ : Lens γ₁ s) (L₂ : Lens γ₂ s)
    {prog : ProgramDenotation s α}
    (h₁ : prog.inRange L₁.compl.range) (h₂ : prog.inRange L₂.compl.range)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ' : s,
        L₁.get σ' = L₁.get σ → L₂.get σ' = L₂.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  rw [ProgramDenotation.wp_strengthen_lens_preserved L₂ h₂]
  rw [ProgramDenotation.wp_strengthen_lens_preserved L₁ h₁]
  calc prog.wp _ σ
      ≤ prog.wp (fun _ : α × s => P σ) σ := by
        apply ProgramDenotation.wp_le_wp_of_le
        rintro ⟨_, σ'⟩; dsimp only
        split_ifs with h1 h2
        · exact le_of_eq (h_factors σ σ' h1 h2)
        all_goals exact bot_le
    _ ≤ P σ := ProgramDenotation.wp_const_le prog _ σ

/-- **Three-lens preservation**: same idea as `ProgramDenotation.wp_le_of_factors`, but
    `P` factors through three lens-gets and `prog` preserves all three. Used
    for indicators (e.g. OW's `useful_preimage`) that depend on multiple
    independent pieces of state. -/
lemma ProgramDenotation.wp_le_of_factors_three {s α γ₁ γ₂ γ₃ : Type}
    [DecidableEq γ₁] [DecidableEq γ₂] [DecidableEq γ₃]
    (L₁ : Lens γ₁ s) (L₂ : Lens γ₂ s) (L₃ : Lens γ₃ s)
    {prog : ProgramDenotation s α}
    (h₁ : prog.inRange L₁.compl.range)
    (h₂ : prog.inRange L₂.compl.range)
    (h₃ : prog.inRange L₃.compl.range)
    {P : s → ENNReal}
    (h_factors : ∀ σ σ' : s,
        L₁.get σ' = L₁.get σ → L₂.get σ' = L₂.get σ →
        L₃.get σ' = L₃.get σ → P σ' = P σ)
    (σ : s) :
    prog.wp (fun xs : α × s => P xs.2) σ ≤ P σ := by
  rw [ProgramDenotation.wp_strengthen_lens_preserved L₃ h₃]
  rw [ProgramDenotation.wp_strengthen_lens_preserved L₂ h₂]
  rw [ProgramDenotation.wp_strengthen_lens_preserved L₁ h₁]
  calc prog.wp _ σ
      ≤ prog.wp (fun _ : α × s => P σ) σ := by
        apply ProgramDenotation.wp_le_wp_of_le
        rintro ⟨_, σ'⟩; dsimp only
        split_ifs with h1 h2 h3
        · exact le_of_eq (h_factors σ σ' h1 h2 h3)
        all_goals exact bot_le
    _ ≤ P σ := ProgramDenotation.wp_const_le prog _ σ


/-! ## Orbit fact

  Outputs of `p.inRange R` started at `σ` must lie (a.e.) in the `R`-orbit of `σ`.
  We state this as the **measure** of the "outside-orbit" set being zero.

  The proof uses the SubProb-level invariance of `(p σ).1` under `(id × f)` pushforward
  for `f ∈ Rᶜ.updates` with `f σ = σ` (which follows from `inRange_subprob`). The key
  observation: any `f ∈ Rᶜ` that "merges" an off-orbit class `c'` into the σ-class kills
  the measure of `c'`.

  For *general* `DetermFootprint R`, constructing such an `f` from `Rᶜ` requires the
  `Rᶜ`-action on the orbit quotient to be rich enough to move any non-σ-class to
  the σ-class. This holds at least for lens-derived ranges (`R = l.range`).
-/

/-- A `DetermFootprint R` *collapses to σ* if there is a single `Rᶜ`-update that fixes `σ`
    and sends every state into the `R`-orbit of `σ`.

    For *lens-derived* `R = l.range`, this is provided by `l.compl.liftFunction (const [σ])`:
    a complement-set that "resets" any state's complement to match σ's.
    For an *abelian* bicommutant-closed `R`, no such update exists. -/
def DetermFootprint.HasOrbitCollapse (R : DetermFootprint m) (σ : m) : Prop :=
  ∃ f ∈ Rᶜ.updates, f σ = σ ∧ ∀ s, ∃ u ∈ R.updates, u σ = f s

/-- The orbit fact under the `HasOrbitCollapse` hypothesis: outcomes of `p σ` are
    a.e. in `R`-orbit(σ). -/
lemma ProgramDenotation.inRange_orbit_of_collapse {s a : Type} {p : ProgramDenotation s a} {R :
    DetermFootprint s}
    (hp : p.inRange R) (σ : s) (hcoll : R.HasOrbitCollapse σ) :
    (p σ).1 ((Set.univ : Set a) ×ˢ {s' : s | ∀ u ∈ R.updates, u σ ≠ s'}) = 0 := by
  obtain ⟨f, hf_in, hf_fix, hf_collapse⟩ := hcoll
  letI : MeasurableSpace (a × s) := ⊤
  -- Invariance: p σ = (p σ) >>= (fun (x, s') => pure (x, f s')).
  have h_inv : p σ
      = (p σ) >>= (fun (xs : a × s) => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
    have := ProgramDenotation.inRange_subprob hp hf_in σ
    rwa [hf_fix] at this
  -- The "bad" set.
  let A : Set (a × s) := (Set.univ : Set a) ×ˢ {s' : s | ∀ u ∈ R.updates, u σ ≠ s'}
  have hA_meas : MeasurableSet A := trivial
  -- Rewrite (p σ).1 A using invariance + map structure.
  have h_meas_eq : (p σ).1 A = (p σ).1 {xs : a × s | (xs.1, f xs.2) ∈ A} := by
    conv_lhs => rw [h_inv]
    change (MeasureTheory.Measure.bind (p σ).1
              (fun xs => (pure (xs.1, f xs.2) : SubProbability (a × s)).1)) A
         = (p σ).1 {xs : a × s | (xs.1, f xs.2) ∈ A}
    have hdirac : ∀ xs : a × s,
        ((pure (xs.1, f xs.2) : SubProbability (a × s)).1
          : MeasureTheory.Measure (a × s))
        = @MeasureTheory.Measure.dirac (a × s) ⊤ (xs.1, f xs.2) := fun _ => rfl
    simp_rw [hdirac]
    rw [MeasureTheory.Measure.bind_dirac_eq_map (p σ).1 measurable_from_top,
        MeasureTheory.Measure.map_apply measurable_from_top hA_meas]
    rfl
  -- The preimage is empty because `f` collapses every state into `R`-orbit(σ).
  have h_empty : {xs : a × s | (xs.1, f xs.2) ∈ A} = (∅ : Set (a × s)) := by
    ext ⟨x, s'⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, A,
               Set.mem_prod, Set.mem_univ, true_and, not_forall, not_not]
    obtain ⟨u, hu_in, hu_eq⟩ := hf_collapse s'
    exact ⟨u, hu_in, hu_eq⟩
  rw [h_meas_eq, h_empty]
  exact MeasureTheory.measure_empty

/-- Lens-derived ranges always collapse. -/
lemma Lens.range_hasOrbitCollapse {s c : Type} (l : Lens c s) (σ : s) :
    l.range.HasOrbitCollapse σ := by
  refine ⟨l.compl.liftFunction (Function.const _ (l.compl.get σ)), ?_, ?_, ?_⟩
  · -- f ∈ l.rangeᶜ.updates = (centralizer l.range.updates).carrier
    show l.compl.liftFunction (Function.const _ (l.compl.get σ))
         ∈ Submonoid.centralizer l.range.updates
    rw [Submonoid.mem_centralizer_iff]
    intro u hu
    obtain ⟨g, -, rfl⟩ := hu
    -- show: l.liftFunction g ∘ f = f ∘ l.liftFunction g (where ∘ is Monoid mul, which is Function.comp)
    show l.liftFunction g * l.compl.liftFunction (Function.const _ (l.compl.get σ))
       = l.compl.liftFunction (Function.const _ (l.compl.get σ)) * l.liftFunction g
    show l.liftFunction g ∘ l.compl.liftFunction (Function.const _ (l.compl.get σ))
       = l.compl.liftFunction (Function.const _ (l.compl.get σ)) ∘ l.liftFunction g
    funext s
    simp only [Function.comp_apply, Lens.liftFunction, Lens.compl, Quotient.lift_mk,
               Function.const_apply]
    rw [l.set_get, l.set_get, l.set_set]
  · -- f σ = σ
    show l.compl.liftFunction (Function.const _ (l.compl.get σ)) σ = σ
    show l.compl.set ((Function.const _ (l.compl.get σ)) (l.compl.get σ)) σ = σ
    simp only [Function.const_apply]
    exact l.compl.get_set σ
  · -- ∀ s, ∃ u ∈ l.range.updates, u σ = f s
    intro s
    refine ⟨l.liftFunction (Function.const _ (l.get s)),
            ⟨Function.const _ (l.get s), Set.mem_univ _, rfl⟩, ?_⟩
    show l.liftFunction (Function.const _ (l.get s)) σ
       = l.compl.liftFunction (Function.const _ (l.compl.get σ)) s
    show l.set ((Function.const _ (l.get s)) (l.get σ)) σ
       = l.compl.set ((Function.const _ (l.compl.get σ)) (l.compl.get s)) s
    simp only [Function.const_apply]
    -- l.compl.set (l.compl.get σ) s = l.set (l.get s) σ.
    change l.set (l.get s) σ = l.set (l.get s) σ
    rfl

/-- The general orbit fact, packaged with the `HasOrbitCollapse` precondition.
    For arbitrary `DetermFootprint R`, the precondition needs to be supplied externally;
    for lens-derived `R`, `Lens.range_hasOrbitCollapse` discharges it. -/
lemma ProgramDenotation.inRange_orbit {s a : Type} {p : ProgramDenotation s a} {R : DetermFootprint
    s}
    (hp : p.inRange R) (σ : s) (hcoll : R.HasOrbitCollapse σ) :
    (p σ).1 ((Set.univ : Set a) ×ˢ {s' : s | ∀ u ∈ R.updates, u σ ≠ s'}) = 0 :=
  ProgramDenotation.inRange_orbit_of_collapse hp σ hcoll

/-- **Headline payoff lemma**: programs with disjoint ranges commute.

    If `p` lives in `R` and `q` lives in `R'`, and the two ranges are disjoint
    (`R ≤ R'ᶜ`, equivalently every `R`-update commutes with every `R'`-update), then
    `p` and `q` may be run in either order with the same `(output, state)` distribution.

    Additional hypotheses:
    - `hp_coll`, `hq_coll`: for every starting state `σ`, a `Rᶜ`/`R'ᶜ`-update that
      "collapses" the orbit of `σ` to a single point. Lens-derived ranges discharge
      these via `Lens.range_hasOrbitCollapse`.
    - `[Countable a] [Countable b] [Countable s]`: needed to discharge the AEMeasurable
      side condition of `MeasureTheory.lintegral_lintegral_swap` — for countable types
      with top σ-algebra every function is measurable.

    Proof outline:
    1. `R ≤ R'ᶜ` ⇒ `R.updates ⊆ R'ᶜ.updates` (and symmetrically `R' ≤ Rᶜ`).
    2. Apply `ProgramDenotation.ext_of_wp` and unfold `wp_bind`/`wp_pure` on both sides.
    3. For each outcome `(x, s_p)` of `p σ` in the support: by `inRange_orbit_of_collapse`
       (using `hp_coll`), there is `u_p ∈ R.updates` with `u_p σ = s_p`. Choose via
       `Classical.choice`. Symmetrically `v_q` for `q`.
    4. Step (a) — rewrite the inner `(q xs.2).expected` to `(q σ).expected (post-shift)`
       via `inRange_subprob hq` and `lintegral_congr_ae` (ae on `hp_orbit`).
    5. Step (b) — Fubini swap via `MeasureTheory.lintegral_lintegral_swap`.
    6. Step (c) — rewrite `U xs ys.2 = V ys xs.2` using disjoint commutativity,
       ae on both `hp_orbit` and `hq_orbit`.
    7. Step (d) — rewrite the inner `(p σ).expected (... V ys xs.2 ...)` to
       `(p ys.2).expected (...)` via `inRange_subprob hp` and `lintegral_congr_ae`.
    8. Result matches RHS by `rfl`. -/
theorem ProgramDenotation.commute_of_disjoint
    {s a b : Type} [Countable a] [Countable b] [Countable s]
    {p : ProgramDenotation s a} {q : ProgramDenotation s b} {R R' : DetermFootprint s}
    (hp : p.inRange R) (hq : q.inRange R') (hdisj : R ≤ R'ᶜ)
    (hp_coll : ∀ σ, R.HasOrbitCollapse σ)
    (hq_coll : ∀ σ, R'.HasOrbitCollapse σ) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) := by
  classical
  -- Disjointness gives R ⊆ R'ᶜ and R' ⊆ Rᶜ as update sets.
  have hRR' : ∀ u ∈ R.updates, u ∈ R'ᶜ.updates := fun u hu => hdisj hu
  have hR'R : ∀ v ∈ R'.updates, v ∈ Rᶜ.updates := by
    intro v hv
    show v ∈ Submonoid.centralizer R.updates
    rw [Submonoid.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ Submonoid.centralizer R'.updates := hdisj hu
    rw [Submonoid.mem_centralizer_iff] at hu'
    exact (hu' v hv).symm
  -- Disjoint commutativity at the update level.
  have h_commute : ∀ u ∈ R.updates, ∀ v ∈ R'.updates, u ∘ v = v ∘ u := by
    intro u hu v hv
    have hu_in_cent : u ∈ Submonoid.centralizer R'.updates := hRR' u hu
    rw [Submonoid.mem_centralizer_iff] at hu_in_cent
    exact (hu_in_cent v hv).symm
  -- Approach: prove wp equality, expand wp to lintegrals, apply Fubini.
  apply ProgramDenotation.ext_of_wp
  intro F
  funext σ
  letI : MeasurableSpace (a × s) := ⊤
  letI : MeasurableSpace (b × s) := ⊤
  letI : MeasurableSpace ((a × b) × s) := ⊤
  -- Reduce wp_bind on both sides to expose the kernel structure.
  rw [wp_bind, wp_bind]
  simp only [wp_bind, wp_pure]
  -- Now goal is:
  --   p.wp (fun xs => q.wp (fun ys => F ((xs.1, ys.1), ys.2)) xs.2) σ
  -- = q.wp (fun ys => p.wp (fun xs => F ((xs.1, ys.1), xs.2)) ys.2) σ
  --
  -- Unfold both sides to lintegrals.
  show (p σ).expected (fun xs : a × s =>
          (q xs.2).expected (fun ys : b × s => F ((xs.1, ys.1), ys.2)))
     = (q σ).expected (fun ys : b × s =>
          (p ys.2).expected (fun xs : a × s => F ((xs.1, ys.1), xs.2)))
  -- The orbit-witness machinery.
  let orbR : Set (a × s) := {xs | ∃ u ∈ R.updates, u σ = xs.2}
  let orbR' : Set (b × s) := {ys | ∃ v ∈ R'.updates, v σ = ys.2}
  let U : a × s → s → s := fun xs =>
    if h : xs ∈ orbR then h.choose else id
  let V : b × s → s → s := fun ys =>
    if h : ys ∈ orbR' then h.choose else id
  have hU_in : ∀ xs ∈ orbR, U xs ∈ R.updates := by
    intro xs hxs; simp only [U, hxs, dif_pos]; exact hxs.choose_spec.1
  have hU_app : ∀ xs ∈ orbR, U xs σ = xs.2 := by
    intro xs hxs; simp only [U, hxs, dif_pos]; exact hxs.choose_spec.2
  have hV_in : ∀ ys ∈ orbR', V ys ∈ R'.updates := by
    intro ys hys; simp only [V, hys, dif_pos]; exact hys.choose_spec.1
  have hV_app : ∀ ys ∈ orbR', V ys σ = ys.2 := by
    intro ys hys; simp only [V, hys, dif_pos]; exact hys.choose_spec.2
  have hp_orbit : (p σ).1 orbRᶜ = 0 := by
    have : orbRᶜ = (Set.univ : Set a) ×ˢ {s' : s | ∀ u ∈ R.updates, u σ ≠ s'} := by
      ext ⟨x, s'⟩
      simp [orbR, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_prod, not_exists]
    rw [this]
    exact ProgramDenotation.inRange_orbit_of_collapse hp σ (hp_coll σ)
  have hq_orbit : (q σ).1 orbR'ᶜ = 0 := by
    have : orbR'ᶜ = (Set.univ : Set b) ×ˢ {s' : s | ∀ v ∈ R'.updates, v σ ≠ s'} := by
      ext ⟨y, s'⟩
      simp [orbR', Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_prod, not_exists]
    rw [this]
    exact ProgramDenotation.inRange_orbit_of_collapse hq σ (hq_coll σ)
  -- Step (a): on orbR, rewrite the inner q-expected using inRange_subprob q.
  have step_q_shift : ∀ xs ∈ orbR,
      (q xs.2).expected (fun ys : b × s => F ((xs.1, ys.1), ys.2))
    = (q σ).expected (fun ys : b × s => F ((xs.1, ys.1), U xs ys.2)) := by
    intro xs hxs
    have hUxs_in' : U xs ∈ R'ᶜ.updates := hRR' (U xs) (hU_in xs hxs)
    have hUxs_app : U xs σ = xs.2 := hU_app xs hxs
    have h_sp := ProgramDenotation.inRange_subprob hq hUxs_in' σ
    rw [hUxs_app] at h_sp
    rw [h_sp, SubProbability.expected_bind]
    congr 1
    funext ys
    exact expected_pure _
  -- Apply ae-rewrite to bring it under the outer p-integral.
  have ae_p_orbit : ∀ᵐ xs ∂(p σ).1, xs ∈ orbR := by
    rw [MeasureTheory.ae_iff]
    exact hp_orbit
  have lhs_shifted :
      (p σ).expected (fun xs : a × s =>
          (q xs.2).expected (fun ys : b × s => F ((xs.1, ys.1), ys.2)))
    = (p σ).expected (fun xs : a × s =>
          (q σ).expected (fun ys : b × s => F ((xs.1, ys.1), U xs ys.2))) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [ae_p_orbit] with xs hxs
    exact step_q_shift xs hxs
  rw [lhs_shifted]
  -- Step (b): Fubini swap.
  -- LHS: ∫⁻ xs, ∫⁻ ys, F((xs.1, ys.1), U xs ys.2) ∂(q σ).1 ∂(p σ).1
  -- → ∫⁻ ys, ∫⁻ xs, F((xs.1, ys.1), U xs ys.2) ∂(p σ).1 ∂(q σ).1
  have hp_fin : MeasureTheory.IsFiniteMeasure (p σ).1 :=
    ⟨lt_of_le_of_lt (p σ).2.1 ENNReal.one_lt_top⟩
  have hq_fin : MeasureTheory.IsFiniteMeasure (q σ).1 :=
    ⟨lt_of_le_of_lt (q σ).2.1 ENNReal.one_lt_top⟩
  have hp_sfin : MeasureTheory.SFinite (p σ).1 := inferInstance
  have hq_sfin : MeasureTheory.SFinite (q σ).1 := inferInstance
  have fubini :
      (p σ).expected (fun xs : a × s =>
          (q σ).expected (fun ys : b × s => F ((xs.1, ys.1), U xs ys.2)))
    = (q σ).expected (fun ys : b × s =>
          (p σ).expected (fun xs : a × s => F ((xs.1, ys.1), U xs ys.2))) := by
    show ∫⁻ xs, ∫⁻ ys, F ((xs.1, ys.1), U xs ys.2) ∂(q σ).1 ∂(p σ).1
       = ∫⁻ ys, ∫⁻ xs, F ((xs.1, ys.1), U xs ys.2) ∂(p σ).1 ∂(q σ).1
    refine MeasureTheory.lintegral_lintegral_swap (μ := (p σ).1) (ν := (q σ).1)
      (f := fun (xs : a × s) (ys : b × s) => F ((xs.1, ys.1), U xs ys.2)) ?_
    -- Under Countable {a, b, s}, every function on the (countable) product is measurable.
    refine Measurable.aemeasurable ?_
    intro T _
    -- The preimage of T is a subset of `(a × s) × (b × s)`, which is countable, hence
    -- measurable under any `MeasurableSingletonClass`-bearing MeasurableSpace.
    have : MeasurableSingletonClass ((a × s) × (b × s)) := by
      letI : MeasurableSingletonClass (a × s) := ⟨fun _ => trivial⟩
      letI : MeasurableSingletonClass (b × s) := ⟨fun _ => trivial⟩
      infer_instance
    exact Set.Countable.measurableSet (Set.to_countable _)
  rw [fubini]
  -- Step (c): on orbR' (ae over (q σ).1), and for xs ∈ orbR (ae over (p σ).1),
  -- replace U xs ys.2 with V ys xs.2 using Disjoint commute.
  have ae_q_orbit : ∀ᵐ ys ∂(q σ).1, ys ∈ orbR' := by
    rw [MeasureTheory.ae_iff]
    exact hq_orbit
  have step_commute : ∀ ys ∈ orbR', ∀ᵐ xs ∂(p σ).1, U xs ys.2 = V ys xs.2 := by
    intro ys hys
    filter_upwards [ae_p_orbit] with xs hxs
    -- U xs ys.2 = U xs (V ys σ) = V ys (U xs σ) = V ys xs.2
    rw [← hV_app ys hys]
    have h_comm := h_commute (U xs) (hU_in xs hxs) (V ys) (hV_in ys hys)
    have happ := congr_fun h_comm σ
    -- happ: (U xs ∘ V ys) σ = (V ys ∘ U xs) σ
    simp only [Function.comp_apply] at happ
    -- happ: U xs (V ys σ) = V ys (U xs σ)
    rw [hU_app xs hxs] at happ
    exact happ
  have commute_shifted :
      (q σ).expected (fun ys : b × s =>
          (p σ).expected (fun xs : a × s => F ((xs.1, ys.1), U xs ys.2)))
    = (q σ).expected (fun ys : b × s =>
          (p σ).expected (fun xs : a × s => F ((xs.1, ys.1), V ys xs.2))) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [ae_q_orbit] with ys hys
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [step_commute ys hys] with xs hxs
    rw [hxs]
  rw [commute_shifted]
  -- Step (d): unshift p using inRange_subprob p with V ys ∈ R' ⊆ Rᶜ.
  -- ∫⁻ xs, F((xs.1, ys.1), V ys xs.2) ∂(p σ).1 = ∫⁻ xs', F((xs'.1, ys.1), xs'.2) ∂(p ys.2).1
  have step_p_unshift : ∀ ys ∈ orbR',
      (p σ).expected (fun xs : a × s => F ((xs.1, ys.1), V ys xs.2))
    = (p ys.2).expected (fun xs : a × s => F ((xs.1, ys.1), xs.2)) := by
    intro ys hys
    have hVys_in : V ys ∈ R'.updates := hV_in ys hys
    have hVys_in' : V ys ∈ Rᶜ.updates := hR'R (V ys) hVys_in
    have hVys_app : V ys σ = ys.2 := hV_app ys hys
    have h_sp := ProgramDenotation.inRange_subprob hp hVys_in' σ
    rw [hVys_app] at h_sp
    rw [h_sp, SubProbability.expected_bind]
    congr 1
    funext xs
    rw [expected_pure]
  -- Apply step_p_unshift inside outer q-expected (ae on orbR').
  have rhs_form :
      (q σ).expected (fun ys : b × s =>
          (p σ).expected (fun xs : a × s => F ((xs.1, ys.1), V ys xs.2)))
    = (q σ).expected (fun ys : b × s =>
          (p ys.2).expected (fun xs : a × s => F ((xs.1, ys.1), xs.2))) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [ae_q_orbit] with ys hys
    exact step_p_unshift ys hys
  rw [rhs_form]

/-- Thin wrapper that specialises the disjointness statement to each program's own
    `range`. The user-facing signature mentions only `p.range` and `q.range` (no
    auxiliary `R, R'`). The two `inRange p p.range` / `inRange q q.range` premises
    must be discharged by the caller. -/
theorem ProgramDenotation.commute_of_disjoint'
    {s a b : Type} [Countable a] [Countable b] [Countable s]
    (p : ProgramDenotation s a) (q : ProgramDenotation s b)
    (hp : p.inRange p.range) (hq : q.inRange q.range)
    (hdisj : p.range ≤ q.rangeᶜ)
    (hp_coll : ∀ σ, p.range.HasOrbitCollapse σ)
    (hq_coll : ∀ σ, q.range.HasOrbitCollapse σ) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) :=
  ProgramDenotation.commute_of_disjoint hp hq hdisj hp_coll hq_coll

/-- Lens-derived variant: when `p` and `q` live in lens-derived ranges, the
    `HasOrbitCollapse` premises are discharged automatically by
    `Lens.range_hasOrbitCollapse`. So the user only needs to supply
    the `inRange` proofs and the disjointness of the lens ranges. -/
theorem ProgramDenotation.commute_of_disjoint_lens
    {s a b c d : Type} [Countable a] [Countable b] [Countable s]
    {p : ProgramDenotation s a} {q : ProgramDenotation s b}
    {l : Lens c s} {l' : Lens d s}
    (hp : p.inRange l.range) (hq : q.inRange l'.range)
    (hdisj : l.range ≤ (l'.range)ᶜ) :
    (p >>= fun x => q >>= fun y => pure (x, y))
  = (q >>= fun y => p >>= fun x => pure (x, y)) :=
  ProgramDenotation.commute_of_disjoint hp hq hdisj
    (fun σ => Lens.range_hasOrbitCollapse l σ)
    (fun σ => Lens.range_hasOrbitCollapse l' σ)

/-! ## Lens lifting and factoring

If `Adv : ProgramDenotation s a` is confined to a lens window `L : Lens c s`
(i.e. `Adv.inRange L.range`), then `Adv` is the lifting of some "inner"
program `Adv' : ProgramDenotation c a` along `L`. This is the converse to the
obvious direction that any lift lives in the lens's range.
-/


/-- **Factorization theorem**: every program confined to a lens window comes
    from running some inner program on the L-content.

    The witness is `L.factor Adv` (which depends on an arbitrary "padding"
    state); the equation `Adv = L.lift (L.factor Adv)` holds because
    `Adv.inRange L.range` makes `Adv` insensitive to the padding's
    outside content. -/
theorem Lens.factor_of_inRange {c s a : Type} [Nonempty s]
    (L : Lens c s) {Adv : ProgramDenotation s a} (h : Adv.inRange L.range) :
    Adv = L.lift (L.factor Adv) := by
  funext σ
  -- Abbreviations matching the proof sketch.
  set σ_pad : s := L.set (L.get σ) (Classical.arbitrary s) with hσ_pad_def
  set f : s → s := fun σ' => L.set (L.get σ') σ with hf_def
  -- (i) f σ_pad = σ — lens-law calculation.
  have h_fσ_pad : f σ_pad = σ := by
    show L.set (L.get (L.set (L.get σ) (Classical.arbitrary s))) σ = σ
    rw [L.set_get, L.get_set]
  -- (iii) f ∈ L.rangeᶜ.updates — via complement_range.
  have h_f_mem : f ∈ ((L.range : DetermFootprint s)ᶜ).updates := by
    rw [← DetermFootprint.complement_range]
    refine ⟨Function.const _ (L.compl.get σ), Set.mem_univ _, ?_⟩
    rfl
  -- (iv) inRange_subprob: Adv σ = Adv σ_pad >>= fun xs => pure (xs.1, f xs.2)
  have h_iv : Adv σ = (Adv σ_pad) >>=
              (fun xs : a × s => (pure (xs.1, f xs.2) : SubProbability (a × s))) := by
    rw [← h_fσ_pad]
    exact ProgramDenotation.inRange_subprob h h_f_mem σ_pad
  -- Unfold the RHS of the goal.
  change Adv σ = ((Adv σ_pad) >>= fun (xσ' : a × s) =>
                    (pure (xσ'.1, L.get xσ'.2) : SubProbability (a × c)))
                  >>= fun (xc : a × c) =>
                    (pure (xc.1, L.set xc.2 σ) : SubProbability (a × s))
  rw [h_iv, SubProbability.bind_assoc']
  -- Collapse the two inner pures into one.
  congr 1
  funext xσ'
  rw [SubProbability.pure_bind]


/-! ## Lifting a confined program along a chained lens

These close the `lift_inRange_chain` obligation used by the RO syntactic-
equivalence development.  All ranges here are *lens* ranges, so the orbit
machinery is not needed — the facts are pure lens algebra plus the existing
`inRange_get`/`inRange_set` extractions. -/


/-- **A lift lives in its lens's range.**  For any inner program `Q`, the lift
    `M.lift Q` is confined to `M.range`: it only touches the `M`-window. -/
theorem Lens.lift_inRange_self {c s a : Type} (M : Lens c s) (Q : ProgramDenotation c a) :
    (M.lift Q).inRange M.range := by
  intro f hf
  -- `f` outside `M.range` preserves `M.get` and commutes with `M.set`.
  have h_get : ∀ σ : s, M.get (f σ) = M.get σ := by
    intro σ
    have hmem : f ∈ Submonoid.centralizer M.range.updates := hf
    rw [Submonoid.mem_centralizer_iff] at hmem
    have hv_upd : M.liftFunction (Function.const _ (M.get σ)) ∈ M.range.updates :=
      ⟨Function.const _ (M.get σ), Set.mem_univ _, rfl⟩
    have hcomm := congr_fun (hmem _ hv_upd) σ
    change M.liftFunction (Function.const _ (M.get σ)) (f σ)
         = f (M.liftFunction (Function.const _ (M.get σ)) σ) at hcomm
    simp only [Lens.liftFunction, Function.const_apply] at hcomm
    rw [M.get_set] at hcomm
    have := congr_arg M.get hcomm
    rw [M.set_get] at this
    exact this.symm
  have h_set : ∀ (y : c) (σ : s), M.set y (f σ) = f (M.set y σ) := by
    intro y σ
    have hmem : f ∈ Submonoid.centralizer M.range.updates := hf
    rw [Submonoid.mem_centralizer_iff] at hmem
    have hvx : M.liftFunction (Function.const _ y) ∈ M.range.updates :=
      ⟨Function.const _ y, Set.mem_univ _, rfl⟩
    have hcomm := congr_fun (hmem _ hvx) σ
    change M.liftFunction (Function.const _ y) (f σ) = f (M.liftFunction (Function.const _ y) σ) at hcomm
    simp only [Lens.liftFunction, Function.const_apply] at hcomm
    exact hcomm
  apply ProgramDenotation.ext_of_wp
  intro F
  funext σ
  simp only [wp_bind, wp_liftF, wp_pure, ProgramDenotation.wp_lift, h_get]
  congr 1
  funext ac
  rw [h_set]

/-- **Lift confines the footprint through the chained lens.**  A program `P`
    confined to window `v` lifts (along `L`) to one confined to the composite
    `L ∘ v`.  Proof: `P` factors as `v.lift (v.factor P)` (by `factor_of_inRange`),
    lift composition turns the double lift into a single `(L.chain v)` lift, and
    `lift_inRange_self` confines that to `(L.chain v).range`. -/
theorem Lens.lift_inRange_chain {c s d a : Type} [Nonempty c] (L : Lens c s) (v : Lens d c)
    (P : ProgramDenotation c a) (hP : P.inRange v.range) :
    (L.lift P).inRange (L.chain v).range := by
  rw [Lens.factor_of_inRange v hP, Lens.lift_lift_chain]
  exact Lens.lift_inRange_self (L.chain v) (v.factor P)


/-- **A sampled value lives in every range.**  `μ.toProgramDenotation` only draws its
    return value; it never touches the state, so it commutes with every update. -/
theorem ProgramDenotation.inRange_toProgramDenotation {s a : Type} (μ : SubProbability a) (R :
    DetermFootprint s) :
    (SubProbability.toProgramDenotation μ : ProgramDenotation s a).inRange R := by
  intro f _
  apply ProgramDenotation.ext_of_wp
  intro F
  funext σ
  simp only [wp_bind, wp_liftF, wp_pure, ProgramDenotation.wp_toProgramDenotation]

/-- **Chaining focuses a sub-window**: `(L.chain v).range ≤ L.range`.  Every
    `L∘v`-update is an `L`-update (acting only inside the `L`-window). -/
theorem Lens.chain_range_le {a b c : Type} (L : Lens b c) (v : Lens a b) :
    (L.chain v).range ≤ L.range := by
  rintro _ ⟨f, -, rfl⟩
  exact ⟨fun s => v.set (f (v.get s)) s, Set.mem_univ _, by
    funext s; simp [Lens.chain, Lens.liftFunction]⟩

end GaudisCrypt
