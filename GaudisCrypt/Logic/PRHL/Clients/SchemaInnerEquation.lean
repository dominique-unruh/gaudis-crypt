import GaudisCrypt.Logic.PRHL

/-!
# Validation client 1: `schema_inner_equation`, relationally

A relational re-proof of `schema_inner_equation`
(`PlonkLean/RO/OneWayness_GameHop/GuessExperiment.lean`), the per-`σ', t`
correspondence between the *match-tracking* game (set a target, flag matches
on the fly) and the *recording* game (record all queries, compare at the
end).

The unary original needs ≈950 lines (state-alignment via `wp_shift_input`,
three `EquivModuloLens` chains, a bespoke invariant-agreement loop
induction, `maxHeartbeats 1600000`). Relationally it is one synchronized
loop invariant:

```
Inv σ₁ σ₂ := ∃ l, σ₂ = qs.set l (matched.set m₀ (target.set tv₀ σ₁))
               ∧ matched.get σ₁ = decide (t ∈ l)
```

("the recording state is the matching state with the three bookkeeping
lenses overwritten, and the matched flag agrees with membership in the
recorded list"), threaded through `relE.loop_n` and `relE.bind`. The shared
query `q` relates to itself across the lens overwrite by `self_lens_set`
(× 3, composed with `relE.trans`), framed by the matched-flag value.

Note the statement is *more general* than the original: generic in the
state type, and no `Fintype`/`Nonempty` assumptions on `T`.
-/

namespace PRHLSchema

variable {s T : Type} [DecidableEq T]
variable (target_var : Lens T s) (matched_var : Lens Bool s)
variable (queries_list_var : Lens (List T) s)
variable [disjoint matched_var queries_list_var]
variable [disjoint matched_var target_var]
variable [disjoint queries_list_var target_var]

/-- The coupling invariant between the match-tracking run (left) and the
    recording run (right). `m₀`/`tv₀` are the right run's (constant)
    matched/target values. -/
private abbrev Inv (t : T) (m₀ : Bool) (tv₀ : T) (σ₁ σ₂ : s) : Prop :=
  ∃ l : List T,
    σ₂ = queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ σ₁))
    ∧ matched_var.get σ₁ = decide (t ∈ l)

omit [DecidableEq T] [disjoint matched_var queries_list_var]
  [disjoint matched_var target_var] [disjoint queries_list_var target_var] in
/-- The shared query program relates to itself across the three-lens
    overwrite: same answer, overwrite carried to the output states. -/
private lemma q_shift (q : Program s T)
    (h_m : q.inRange matched_var.compl.range)
    (h_qs : q.inRange queries_list_var.compl.range)
    (h_tv : q.inRange target_var.compl.range)
    (l : List T) (m₀ : Bool) (tv₀ : T) :
    q.relE q
      (fun σ₁ σ₂ =>
        σ₂ = queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ σ₁)))
      (fun x y => y.1 = x.1
        ∧ y.2 = queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ x.2))) := by
  refine ((Program.relE.self_lens_set target_var h_tv tv₀).trans
    ((Program.relE.self_lens_set matched_var h_m m₀).trans
      (Program.relE.self_lens_set queries_list_var h_qs l))).conseq ?_ ?_
  · rintro σ₁ σ₂ rfl
    exact ⟨_, rfl, _, rfl, rfl⟩
  · rintro x z ⟨y, ⟨ha1, ha2⟩, y', ⟨hb1, hb2⟩, hc1, hc2⟩
    exact ⟨hc1.trans (hb1.trans ha1), by rw [hc2, hb2, ha2]⟩

omit [disjoint matched_var queries_list_var] [disjoint queries_list_var target_var] in
/-- The two loop tails (match-check vs record-append) preserve the
    invariant, with witness `l ++ [a]`. -/
private lemma tail_relE (t : T) (l : List T) (m₀ : Bool) (tv₀ : T) (a₁ a₂ : T) :
    (if a₁ = t then Program.set matched_var true
      else (pure () : Program s Unit)).relE
      (Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a₂]))
      (fun τ₁ τ₂ =>
        (a₁ = a₂
          ∧ τ₂ = queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ τ₁)))
        ∧ matched_var.get τ₁ = decide (t ∈ l))
      (fun x y => Inv target_var matched_var queries_list_var t m₀ tv₀ x.2 y.2) := by
  haveI htm : disjoint target_var matched_var := disjoint.symm inferInstance
  have hL : ∀ (F : Unit × s → ENNReal) (τ : s),
      (if a₁ = t then Program.set matched_var true
        else (pure () : Program s Unit)).wp F τ
      = F ((), if a₁ = t then matched_var.set true τ else τ) := by
    intro F τ
    by_cases h : a₁ = t
    · simp only [if_pos h, wp_set]
    · simp only [if_neg h, wp_pure]
  have hR : ∀ (G : Unit × s → ENNReal) (τ : s),
      (Program.get queries_list_var >>= fun qs : List T =>
        Program.set queries_list_var (qs ++ [a₂])).wp G τ
      = G ((), queries_list_var.set (queries_list_var.get τ ++ [a₂]) τ) := by
    intro G τ
    simp only [wp_bind, wp_get, wp_set]
  have hstate : ∀ τ₁ : s,
      queries_list_var.set
        (queries_list_var.get
          (queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ τ₁))) ++ [a₁])
        (queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ τ₁)))
      = queries_list_var.set (l ++ [a₁])
          (matched_var.set m₀ (target_var.set tv₀
            (if a₁ = t then matched_var.set true τ₁ else τ₁))) := by
    intro τ₁
    rw [Lens.set_get queries_list_var, queries_list_var.set_set]
    by_cases h : a₁ = t
    · simp only [if_pos h]
      rw [htm.commute, matched_var.set_set]
    · simp only [if_neg h]
  have hinv : ∀ τ₁ : s, matched_var.get τ₁ = decide (t ∈ l) →
      matched_var.get (if a₁ = t then matched_var.set true τ₁ else τ₁)
      = decide (t ∈ l ++ [a₁]) := by
    intro τ₁ hm
    by_cases h : a₁ = t
    · rw [if_pos h, Lens.set_get matched_var]
      symm
      rw [decide_eq_true_iff]
      exact List.mem_append_right l (List.mem_singleton.mpr h.symm)
    · rw [if_neg h, hm]
      have hmem : (t ∈ l ++ [a₁]) ↔ t ∈ l := by
        rw [List.mem_append, List.mem_singleton]
        exact ⟨fun hh => hh.elim id (fun he => absurd he.symm h), Or.inl⟩
      exact (decide_eq_decide.mpr hmem).symm
  constructor
  · intro F G hFG τ₁ τ₂ hpre
    obtain ⟨⟨ha, hτ⟩, hm⟩ := hpre
    subst ha; subst hτ
    rw [hL F τ₁, hR G _]
    exact hFG _ _ ⟨l ++ [a₁], hstate τ₁, hinv τ₁ hm⟩
  · intro F G hFG τ₂ τ₁ hpre
    obtain ⟨⟨ha, hτ⟩, hm⟩ := hpre
    subst ha; subst hτ
    rw [hR F _, hL G τ₁]
    exact hFG _ _ ⟨l ++ [a₁], hstate τ₁, hinv τ₁ hm⟩


omit [disjoint queries_list_var target_var] in
/-- **The body judgment**: one match-tracking iteration relates to one
    recording iteration, preserving `Inv`. -/
private lemma body_relE (q : Program s T)
    (h_m : q.inRange matched_var.compl.range)
    (h_qs : q.inRange queries_list_var.compl.range)
    (h_tv : q.inRange target_var.compl.range)
    (t : T) (m₀ : Bool) (tv₀ : T) :
    (q >>= fun a : T =>
      if a = t then Program.set matched_var true
      else (pure () : Program s Unit)).relE
    (q >>= fun a : T =>
      Program.get queries_list_var >>= fun qs : List T =>
      Program.set queries_list_var (qs ++ [a]))
    (Inv target_var matched_var queries_list_var t m₀ tv₀)
    (fun x y => Inv target_var matched_var queries_list_var t m₀ tv₀ x.2 y.2) := by
  haveI hqm : disjoint queries_list_var matched_var := disjoint.symm inferInstance
  apply Program.relE.exists_pre
  intro l
  refine Program.relE.bind
    (Mid := fun x y =>
      (x.1 = y.1
        ∧ y.2 = queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ x.2)))
      ∧ matched_var.get x.2 = decide (t ∈ l))
    ?_ (fun a₁ a₂ => tail_relE target_var matched_var queries_list_var t l m₀ tv₀ a₁ a₂)
  refine (Program.relE.frame matched_var matched_var h_m h_m
    (q_shift target_var matched_var queries_list_var q h_m h_qs h_tv l m₀ tv₀)
    (decide (t ∈ l)) m₀).conseq ?_ ?_
  · intro σ₁ σ₂ hpre
    refine ⟨hpre.1, hpre.2, ?_⟩
    rw [hpre.1, Lens.get_of_disjoint_set matched_var queries_list_var, Lens.set_get]
  · intro x y hpost
    exact ⟨⟨hpost.1.1.symm, hpost.1.2⟩, hpost.2.1⟩

omit [disjoint matched_var queries_list_var] [disjoint matched_var target_var]
  [disjoint queries_list_var target_var] in
/-- **The ending judgment**: reading the matched flag (left) returns the
    same boolean as the deferred membership test (right). -/
private lemma ending_relE (t : T) (m₀ : Bool) (tv₀ : T) :
    (Program.get matched_var).relE
      (Program.get queries_list_var >>= fun qs : List T =>
        Program.set matched_var (decide (t ∈ qs)) >>= fun _ : Unit =>
        Program.get matched_var)
      (Inv target_var matched_var queries_list_var t m₀ tv₀)
      (fun x y => x.1 = y.1) := by
  have hR : ∀ (G : Bool × s → ENNReal) (τ : s),
      (Program.get queries_list_var >>= fun qs : List T =>
        Program.set matched_var (decide (t ∈ qs)) >>= fun _ : Unit =>
        Program.get matched_var).wp G τ
      = G (decide (t ∈ queries_list_var.get τ),
           matched_var.set (decide (t ∈ queries_list_var.get τ)) τ) := by
    intro G τ
    simp only [wp_bind, wp_get, wp_set, Lens.set_get]
  have hpost : ∀ (τ₁ : s) (l : List T), matched_var.get τ₁ = decide (t ∈ l) →
      matched_var.get τ₁
      = decide (t ∈ queries_list_var.get
          (queries_list_var.set l (matched_var.set m₀ (target_var.set tv₀ τ₁)))) := by
    intro τ₁ l hm
    rw [Lens.set_get queries_list_var]
    exact hm
  constructor
  · intro F G hFG τ₁ τ₂ hpre
    obtain ⟨l, hτ, hm⟩ := hpre
    subst hτ
    rw [wp_get, hR G _]
    exact hFG _ _ (hpost τ₁ l hm)
  · intro F G hFG τ₂ τ₁ hpre
    obtain ⟨l, hτ, hm⟩ := hpre
    subst hτ
    rw [hR F _, wp_get]
    exact hFG _ _ (hpost τ₁ l hm)

/-- Peel a leading `set` off a `wp`. -/
private lemma wp_set_seq {γ α : Type} (L : Lens γ s) (v : γ) (P : Program s α)
    (F : α × s → ENNReal) (σ : s) :
    (Program.set L v >>= fun _ : Unit => P).wp F σ = P.wp F (L.set v σ) := by
  rw [wp_bind, wp_set]

omit [disjoint queries_list_var target_var] in
/-- **`schema_inner_equation`, relationally.** Same statement as the unary
    original, but generic in the state type, without `Fintype`/`Nonempty`
    assumptions on `T`, and needing only two of the original's three
    disjointness assumptions. -/
theorem schema_inner_equation_prhl
    (q_body q_final : Program s T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (h_q_body_target : q_body.inRange target_var.compl.range)
    (h_q_final_matched : q_final.inRange matched_var.compl.range)
    (h_q_final_qs : q_final.inRange queries_list_var.compl.range)
    (h_q_final_target : q_final.inRange target_var.compl.range)
    (n : ℕ) (σ' : s) (t : T) :
    (Program.set target_var t >>= fun _ : Unit =>
     Program.set matched_var false >>= fun _ : Unit =>
     loop_n n (q_body >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program s Unit))
      >>= fun _ : Unit =>
     (q_final >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program s Unit))
      >>= fun _ : Unit =>
     Program.get matched_var).wp
       (fun bσ : Bool × s => if bσ.1 then (1 : ENNReal) else 0) σ'
    = (Program.set queries_list_var [] >>= fun _ : Unit =>
       loop_n n (q_body >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       (q_final >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       Program.get queries_list_var >>= fun qs =>
       Program.set matched_var (decide (t ∈ qs)) >>= fun _ : Unit =>
       Program.get matched_var).wp
       (fun bσ : Bool × s => if bσ.1 then (1 : ENNReal) else 0) σ' := by
  haveI htm : disjoint target_var matched_var := disjoint.symm inferInstance
  -- The full relational judgment: loop, then final iteration, then ending.
  have hmain := Program.relE.bind
    (Program.relE.loop_n (body_relE target_var matched_var queries_list_var q_body
      h_q_body_matched h_q_body_qs h_q_body_target t (matched_var.get σ')
      (target_var.get σ')) n)
    (fun _ _ => Program.relE.bind
      (body_relE target_var matched_var queries_list_var q_final
        h_q_final_matched h_q_final_qs h_q_final_target t (matched_var.get σ')
        (target_var.get σ'))
      (fun _ _ => ending_relE target_var matched_var queries_list_var t
        (matched_var.get σ') (target_var.get σ')))
  -- The invariant holds at the two post-prefix states (witness `[]`).
  have h0 : Inv target_var matched_var queries_list_var t (matched_var.get σ')
      (target_var.get σ')
      (matched_var.set false (target_var.set t σ'))
      (queries_list_var.set [] σ') := by
    refine ⟨[], ?_, ?_⟩
    · rw [htm.commute, matched_var.set_set, target_var.set_set,
          Lens.get_set target_var, Lens.get_set matched_var]
    · rw [Lens.set_get matched_var]
      simp
  -- Peel the deterministic prefixes and conclude by the judgment.
  rw [wp_set_seq target_var t, wp_set_seq matched_var false,
      wp_set_seq queries_list_var ([] : List T)]
  exact hmain.wp_eq (fun x y h => by rw [h]) h0

end PRHLSchema
