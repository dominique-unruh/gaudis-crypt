import GaudisCrypt.WeakestPreconditions
import GaudisCrypt.Language.Footprint

open GaudisCrypt

namespace GaudisCrypt

/-!
# The `transferBy` calculus

The generic "sliding coupling" relation between programs:

* `ProgramDenotation.transferBy c p q` holds when the *coupling program* `c`
  (think: `convert`, filling in a lazily sampled random-oracle table) slides
  from after `p` to before `q`, preserving `p`'s value:
  `(p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q)`.

* Closure combinators: `transferBy_pure`, `transferBy_bind`,
  `transferBy_while_loop` (Kleene/ωSup argument), `transferBy_zoom`
  (lifting along a lens into a larger state).

* Reflexivity from commutation: `transferBy_refl_of_commute` and its
  footprint form `transferBy_refl_of_inFootprint_compl` — a program whose
  probabilistic footprint avoids `c`'s footprint transfers to itself.
  `transferBy_comm_cont` is the converse direction (self-transfer gives
  commutation in continuation-passing form).

* Consequences at the `wp`/marginal level: `transferBy_wp_invariant`,
  `transferBy_wp_value`, `transferBy_marginal_invariant`,
  `transferBy_value_marginal` — for `c`-invariant (resp. state-blind)
  postconditions, transfer gives wp-equality and equal output marginals.

The lazy/eager random-oracle transfer (`ProgramDenotation.transfer` in
`GaudisCrypt.Lib.RO.TransferConvert`) is `transferBy convert`; its
`ProcedureState` variant (`Stable`/`Loc` in
`GaudisCrypt.Lib.RO.TransferInstantiate`) is `transferBy convertL`.
-/

/-- Generic transfer: `c` slides from after `p` to before `q`, preserving the value. -/
def ProgramDenotation.transferBy {s α : Type} (c : ProgramDenotation s Unit)
    (p q : ProgramDenotation s α) : Prop :=
  (p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q)

/-! ## Monad-law combinators -/

/-- `pure` transfers to itself. -/
theorem ProgramDenotation.transferBy_pure {s α : Type} {c : ProgramDenotation s Unit} (a : α) :
    ProgramDenotation.transferBy c (pure a) (pure a) :=
  ProgramDenotation.pure_bind a _

/-- `transferBy` chains under `>>=`. -/
theorem ProgramDenotation.transferBy_bind {s α β : Type} {c : ProgramDenotation s Unit}
    {p q : ProgramDenotation s α} {p' q' : α → ProgramDenotation s β}
    (h : ProgramDenotation.transferBy c p q)
    (h' : ∀ a, ProgramDenotation.transferBy c (p' a) (q' a)) :
    ProgramDenotation.transferBy c (p >>= p') (q >>= q') := by
  change ((p >>= p') >>= fun b => c >>= fun _ => pure b) = (c >>= fun _ => q >>= q')
  rw [ProgramDenotation.bind_assoc]
  conv_lhs =>
    rhs; ext a
    rw [show (p' a >>= fun b => c >>= fun _ => (Pure.pure b : ProgramDenotation s β))
          = (c >>= fun _ => q' a) from h' a]
  conv_lhs =>
    rhs; ext a
    rw [show (c >>= fun _ => q' a)
          = (c >>= fun _ => (Pure.pure a : ProgramDenotation s α)) >>= q' from by
        rw [ProgramDenotation.bind_assoc]; congr 1; funext _; rw [ProgramDenotation.pure_bind]]
  rw [← ProgramDenotation.bind_assoc]
  rw [show (p >>= fun a => c >>= fun _ => (Pure.pure a : ProgramDenotation s α))
        = (c >>= fun _ => q) from h]
  rw [ProgramDenotation.bind_assoc]

/-- Re-passing a `Unit` value through `pure` after `c` is a no-op. -/
private lemma bind_c_pure_unit {s : Type} (c : ProgramDenotation s Unit) :
    (fun u : Unit => c >>= fun _ : Unit => (Pure.pure u : ProgramDenotation s Unit))
      = fun _ : Unit => c := by
  funext u
  rw [show (Pure.pure u : ProgramDenotation s Unit)
        = (Pure.pure () : ProgramDenotation s Unit) from rfl]
  exact ProgramDenotation.bind_pure _

/-- For `Unit`-valued programs the transfer is a plain bind equation:
    `p; c = c; q`. -/
theorem ProgramDenotation.transferBy_unit_bind {s : Type} {c p q : ProgramDenotation s Unit}
    (h : ProgramDenotation.transferBy c p q) :
    (p >>= fun _ : Unit => c) = (c >>= fun _ : Unit => q) := by
  have h' : (p >>= fun u : Unit =>
        c >>= fun _ : Unit => (Pure.pure u : ProgramDenotation s Unit))
      = (c >>= fun _ : Unit => q) := h
  rwa [bind_c_pure_unit] at h'

/-- Converse of `transferBy_unit_bind`: a plain bind equation between
    `Unit`-valued programs is a transfer. -/
theorem ProgramDenotation.transferBy_of_unit_bind {s : Type} {c p q : ProgramDenotation s Unit}
    (h : (p >>= fun _ : Unit => c) = (c >>= fun _ : Unit => q)) :
    ProgramDenotation.transferBy c p q := by
  change (p >>= fun u : Unit =>
        c >>= fun _ : Unit => (Pure.pure u : ProgramDenotation s Unit))
      = (c >>= fun _ : Unit => q)
  rw [bind_c_pure_unit]
  exact h

/-- `zoom` lifts `transferBy`: a state-level transfer becomes a zoomed one. -/
theorem ProgramDenotation.transferBy_zoom {s t α : Type} (lens : Lens s t)
    {c : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h : ProgramDenotation.transferBy c p q) :
    ProgramDenotation.transferBy (ProgramDenotation.zoom lens c)
        (ProgramDenotation.zoom lens p) (ProgramDenotation.zoom lens q) := by
  change (ProgramDenotation.zoom lens p >>= fun a =>
            ProgramDenotation.zoom lens c >>= fun _ => pure a)
      = (ProgramDenotation.zoom lens c >>= fun _ => ProgramDenotation.zoom lens q)
  rw [show (fun a => ProgramDenotation.zoom lens c >>= fun _ => (pure a : ProgramDenotation t α))
        = (fun a => ProgramDenotation.zoom lens (c >>= fun _ => pure a)) from by
      funext a; rw [ProgramDenotation.zoom_bind]; congr 1; funext _
      rw [ProgramDenotation.zoom_pure]]
  rw [← ProgramDenotation.zoom_bind, ← ProgramDenotation.zoom_bind]
  rw [show (p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q) from h]

/-! ## Reflexivity from commutation -/

/-- Self-transfer from pair-output commutation with `c`. -/
theorem ProgramDenotation.transferBy_refl_of_commute {s α : Type}
    {c : ProgramDenotation s Unit} {p : ProgramDenotation s α}
    (h : (p >>= fun a => c >>= fun b => pure (a, b))
       = (c >>= fun b => p >>= fun a => pure (a, b))) :
    ProgramDenotation.transferBy c p p := by
  have h' := congrArg (fun m : ProgramDenotation s (α × Unit) =>
    m >>= fun ab => (pure ab.1 : ProgramDenotation s α)) h
  simp only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind,
    ProgramDenotation.bind_pure] at h'
  exact h'

/-- Continuation form of the transfer: `c` slides past `p` in front of any
    continuation `k`, turning `p` into `q`. At `p = q` this says a
    self-transferring program commutes with `c` (the converse direction of
    `transferBy_refl_of_commute`). -/
theorem ProgramDenotation.transferBy_cont {s α β : Type}
    {c : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h : ProgramDenotation.transferBy c p q) (k : α → ProgramDenotation s β) :
    (p >>= fun a => c >>= fun _ => k a) = (c >>= fun _ => q >>= k) := by
  have h' := congrArg (fun m : ProgramDenotation s α => m >>= k)
    (show (p >>= fun a => c >>= fun _ => pure a) = (c >>= fun _ => q) from h)
  simpa only [ProgramDenotation.bind_assoc, ProgramDenotation.pure_bind] using h'

/-- **Self-transfer from footprint disjointness**: a program whose probabilistic
    footprint avoids `c`'s footprint commutes with `c`
    (`commute_of_disjoint_footprint`), so transfers to itself. The `ᶜ`-form makes
    the disjointness hypothesis `le_refl`. -/
theorem ProgramDenotation.transferBy_refl_of_inFootprint_compl {s α : Type}
    {F : Footprint s} {c : ProgramDenotation s Unit} (hc : c.inFootprint F)
    {p : ProgramDenotation s α} (hp : p.inFootprint Fᶜ) :
    ProgramDenotation.transferBy c p p :=
  ProgramDenotation.transferBy_refl_of_commute
    (ProgramDenotation.commute_of_disjoint_footprint hp hc (le_refl _))

/-! ## Closure under `while_loop` (Kleene/ωSup argument)

Couple every finite iterate of the two loops via an intermediate `whileBy_Ψ`
whose else-branch is `c` (representing "loop terminates, then couple"), then
take the ωSup. -/

/-- Intermediate iteration: the lazy body, but with `c` in the else branch. -/
private noncomputable def whileBy_Ψ {s : Type} (c : ProgramDenotation s Unit)
    (cond : ProgramDenotation s Bool) (body_lazy : ProgramDenotation s Unit) :
    (Unit → ProgramDenotation s Unit) →𝒄 (Unit → ProgramDenotation s Unit) :=
  OmegaCompletePartialOrder.ContinuousHom.ofFun fun (fp : Unit → ProgramDenotation s Unit) =>
      fun () =>
    do if ← cond then body_lazy; fp () else c

/-- Lazy iterate composed with `c` equals the `Ψ`-iterate. -/
private lemma whileBy_kleene_lazy {s : Type} (c : ProgramDenotation s Unit)
    (cond : ProgramDenotation s Bool) (body_lazy : ProgramDenotation s Unit) :
    ∀ n : ℕ,
    (((while_iteration cond body_lazy)^[n] (⊥ : Unit → ProgramDenotation s Unit)) ()
        >>= (fun _ => c))
    = ((whileBy_Ψ c cond body_lazy)^[n] (⊥ : Unit → ProgramDenotation s Unit)) () := by
  intro n
  induction n with
  | zero =>
    change ((⊥ : ProgramDenotation s Unit) >>= fun _ => c) = (⊥ : ProgramDenotation s Unit)
    exact ProgramDenotation.bot_bind _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (((cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((while_iteration cond body_lazy)^[n] ⊥) ()
              else (pure () : ProgramDenotation s Unit)) >>= fun _ => c)
        = (cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((whileBy_Ψ c cond body_lazy)^[n] ⊥) ()
              else c
    rw [ProgramDenotation.bind_assoc]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]; rw [ProgramDenotation.bind_assoc]; congr 1; funext _; exact ih
    · simp only [h]; exact ProgramDenotation.pure_bind () _

/-- `c` prepended to the eager iterate equals the `Ψ`-iterate. -/
private lemma whileBy_kleene_eager {s : Type} (c : ProgramDenotation s Unit)
    {cond : ProgramDenotation s Bool}
    (h_cond_comm : ∀ {β : Type} (k : Bool → ProgramDenotation s β),
        (cond >>= fun b => c >>= fun _ => k b) = (c >>= fun _ => cond >>= k))
    {body_lazy body_eager : ProgramDenotation s Unit}
    (h_body : (body_lazy >>= fun _ : Unit => c) = (c >>= fun _ : Unit => body_eager)) :
    ∀ n : ℕ,
    c >>= (fun _ => ((while_iteration cond body_eager)^[n]
        (⊥ : Unit → ProgramDenotation s Unit)) ())
    = ((whileBy_Ψ c cond body_lazy)^[n] (⊥ : Unit → ProgramDenotation s Unit)) () := by
  intro n
  induction n with
  | zero =>
    change (c >>= fun _ => (⊥ : ProgramDenotation s Unit)) = (⊥ : ProgramDenotation s Unit)
    exact ProgramDenotation.bind_bot _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (c >>= fun _ => (cond) >>= fun b =>
              if b = true then body_eager >>= fun _ => ((while_iteration cond body_eager)^[n] ⊥) ()
              else (pure () : ProgramDenotation s Unit))
        = (cond) >>= fun b =>
              if b = true then body_lazy >>= fun _ => ((whileBy_Ψ c cond body_lazy)^[n] ⊥) ()
              else c
    rw [show (c >>= fun _ => (cond) >>=
              fun b => if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) ()
                else (pure () : ProgramDenotation s Unit))
            = ((cond) >>= fun b => c >>= fun _ =>
                if b = true then body_eager >>= fun _ =>
                  ((while_iteration cond body_eager)^[n] ⊥) ()
                else (pure () : ProgramDenotation s Unit)) from
        (h_cond_comm _).symm]
    congr 1; funext b
    by_cases h : b = true
    · simp only [h, if_true]
      rw [← ProgramDenotation.bind_assoc]
      rw [show (c >>= fun _ : Unit => body_eager)
            = (body_lazy >>= fun _ : Unit => c) from h_body.symm]
      rw [ProgramDenotation.bind_assoc]; congr 1; funext _; exact ih
    · simp only [h]; exact ProgramDenotation.bind_pure _

/-- **`transferBy` is preserved by `while_loop`.** If the condition transfers to
    itself (e.g. by `transferBy_refl_of_inFootprint_compl`) and the body
    transfers, then the two loops transfer. -/
theorem ProgramDenotation.transferBy_while_loop {s : Type} {c : ProgramDenotation s Unit}
    {cond : ProgramDenotation s Bool}
    (h_cond : ProgramDenotation.transferBy c cond cond)
    {body_lazy body_eager : ProgramDenotation s Unit}
    (h_body : ProgramDenotation.transferBy c body_lazy body_eager) :
    ProgramDenotation.transferBy c (while_loop cond body_lazy) (while_loop cond body_eager) := by
  have h_cond_comm : ∀ {β : Type} (k : Bool → ProgramDenotation s β),
      (cond >>= fun b => c >>= fun _ => k b) = (c >>= fun _ => cond >>= k) :=
    fun {β} k => ProgramDenotation.transferBy_cont h_cond k
  have h_body_bind : (body_lazy >>= fun _ : Unit => c) = (c >>= fun _ : Unit => body_eager) :=
    ProgramDenotation.transferBy_unit_bind h_body
  change (while_loop cond body_lazy >>= fun u : Unit =>
          c >>= fun _ : Unit => (Pure.pure u : ProgramDenotation s Unit))
      = (c >>= fun _ : Unit => while_loop cond body_eager)
  rw [bind_c_pure_unit]
  let F_lazy := while_iteration cond body_lazy
  let F_eager := while_iteration cond body_eager
  have hL_chain : ∀ n, ((F_lazy^[n] ⊥ : Unit → ProgramDenotation s Unit) () >>= (fun _ => c))
                     = ((whileBy_Ψ c cond body_lazy)^[n] ⊥ : Unit → ProgramDenotation s Unit) () :=
    whileBy_kleene_lazy c cond body_lazy
  have hE_chain : ∀ n, c >>= (fun _ => (F_eager^[n] ⊥ : Unit → ProgramDenotation s Unit) ())
                     = ((whileBy_Ψ c cond body_lazy)^[n] ⊥ : Unit → ProgramDenotation s Unit) () :=
    whileBy_kleene_eager c h_cond_comm h_body_bind
  have h_bind_c_cont : OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : ProgramDenotation s Unit) => m >>= fun _ => c) := by fun_prop
  have h_c_bind_cont : OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : ProgramDenotation s Unit) => c >>= fun _ => m) := by fun_prop
  change (F_lazy.lfp ()) >>= (fun _ => c) = c >>= (fun _ => F_eager.lfp ())
  let chain_lazy : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F_lazy^[n] ⊥,
     Monotone.monotone_iterate_of_le_map F_lazy.monotone (OrderBot.bot_le _)⟩
  let chain_eager : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F_eager^[n] ⊥,
     Monotone.monotone_iterate_of_le_map F_eager.monotone (OrderBot.bot_le _)⟩
  have hLfpL : F_lazy.lfp = OmegaCompletePartialOrder.ωSup chain_lazy := rfl
  have hLfpE : F_eager.lfp = OmegaCompletePartialOrder.ωSup chain_eager := rfl
  have hLfpL_at : F_lazy.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_lazy.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by rw [hLfpL]; rfl
  have hLfpE_at : F_eager.lfp () = OmegaCompletePartialOrder.ωSup
                    (chain_eager.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := by rw [hLfpE]; rfl
  rw [hLfpL_at, hLfpE_at, h_bind_c_cont.map_ωSup, h_c_bind_cont.map_ωSup]
  congr 1
  ext n
  exact (hL_chain n).trans (hE_chain n).symm

/-! ## Consequences at the `wp` and marginal level -/

/-- `c.wp` of a constant post is that constant, provided `c` has total mass 1. -/
lemma ProgramDenotation.wp_const_of_mass_one {s : Type} {c : ProgramDenotation s Unit}
    (h_mass : ∀ σ, c.wp (fun _ : Unit × s => (1 : ENNReal)) σ = 1) (k : ENNReal) (σ : s) :
    c.wp (fun _ : Unit × s => k) σ = k := by
  have h := ProgramDenotation.wp_const_mul c k (fun _ : Unit × s => (1 : ENNReal)) σ
  simp only [mul_one] at h
  rw [h, h_mass, mul_one]

/-- **Transfer at the wp level for `c`-invariant postconditions**: if the post
    `F` is invariant under running `c` (in the wp sense), then transfer +
    absorption give wp-equality of `p` and `q` on `F` at any starting state. -/
theorem ProgramDenotation.transferBy_wp_invariant {s α : Type}
    {c : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h_transfer : ProgramDenotation.transferBy c p q)
    (h_absorb : (c >>= fun _ => q) = q)
    (F : α × s → ENNReal)
    (hF_inv : ∀ (a : α) (σ : s), c.wp (fun uσ : Unit × s => F (a, uσ.2)) σ = F (a, σ))
    (σ₀ : s) :
    p.wp F σ₀ = q.wp F σ₀ := by
  -- Combine transfer + absorb into the master equation:
  --   (p >>= a => c >>= pure a) = q.
  have h_eq : (p >>= fun a => c >>= fun _ => (Pure.pure a : ProgramDenotation s α)) = q := by
    rw [show (p >>= fun a => c >>= fun _ => (Pure.pure a : ProgramDenotation s α))
          = (c >>= fun _ => q) from h_transfer, h_absorb]
  have h_wp := congrArg (fun (r : ProgramDenotation s α) => r.wp F σ₀) h_eq
  rw [← h_wp]
  rw [wp_bind]
  congr 1
  funext aσ_p
  obtain ⟨a, σ_p⟩ := aσ_p
  change F (a, σ_p) = (c >>= fun _ => (Pure.pure a : ProgramDenotation s α)).wp F σ_p
  rw [wp_bind, wp_pure]
  exact (hF_inv a σ_p).symm

/-- **Transfer at the wp level for value-only postconditions**: for
    `G : α → ENNReal`, the wps of `p` and `q` against `fun aσ => G aσ.1` agree,
    given transfer, absorption, and that `c` is a probability (mass 1). -/
theorem ProgramDenotation.transferBy_wp_value {s α : Type}
    {c : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h_transfer : ProgramDenotation.transferBy c p q)
    (h_absorb : (c >>= fun _ => q) = q)
    (h_mass : ∀ σ, c.wp (fun _ : Unit × s => (1 : ENNReal)) σ = 1)
    (G : α → ENNReal) (σ₀ : s) :
    p.wp (fun aσ : α × s => G aσ.1) σ₀ = q.wp (fun aσ : α × s => G aσ.1) σ₀ :=
  ProgramDenotation.transferBy_wp_invariant h_transfer h_absorb _
    (fun a σ => ProgramDenotation.wp_const_of_mass_one h_mass (G a) σ) σ₀

/-- **Value marginal**: SubProb-level statement of the transfer. -/
theorem ProgramDenotation.transferBy_value_marginal {s α : Type}
    {c : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h_transfer : ProgramDenotation.transferBy c p q)
    (h_absorb : (c >>= fun _ => q) = q)
    (h_mass : ∀ σ, c.wp (fun _ : Unit × s => (1 : ENNReal)) σ = 1)
    (σ₀ : s) :
    (p σ₀ >>= fun aσ => (Pure.pure aσ.1 : SubProbability α))
  = (q σ₀ >>= fun aσ => (Pure.pure aσ.1 : SubProbability α)) := by
  apply Subtype.ext
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace (α × s) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  change MeasureTheory.Measure.bind (p σ₀).1 (fun aσ : α × s =>
          (@MeasureTheory.Measure.dirac α ⊤ aσ.1)) A
     = MeasureTheory.Measure.bind (q σ₀).1 (fun aσ : α × s =>
          (@MeasureTheory.Measure.dirac α ⊤ aσ.1)) A
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
      MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  exact ProgramDenotation.transferBy_wp_value h_transfer h_absorb h_mass
    (fun a : α => (@MeasureTheory.Measure.dirac α ⊤ a) A) σ₀

/-- **Marginal at the (value × `c`-invariant projection) level**: instead of
    projecting to just the value, additionally include any state projection
    `h : s → β` that is invariant under running `c` (in the wp sense). -/
theorem ProgramDenotation.transferBy_marginal_invariant {s α β : Type}
    {c : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h_transfer : ProgramDenotation.transferBy c p q)
    (h_absorb : (c >>= fun _ => q) = q)
    (h : s → β)
    (h_inv : ∀ (g : β → ENNReal) (σ : s),
        c.wp (fun uσ : Unit × s => g (h uσ.2)) σ = g (h σ))
    (σ₀ : s) :
    (p σ₀ >>= fun aσ : α × s => (Pure.pure (aσ.1, h aσ.2) : SubProbability (α × β)))
  = (q σ₀ >>= fun aσ : α × s => (Pure.pure (aσ.1, h aσ.2) : SubProbability (α × β))) := by
  apply Subtype.ext
  letI : MeasurableSpace (α × β) := ⊤
  letI : MeasurableSpace (α × s) := ⊤
  apply MeasureTheory.Measure.ext
  intro A hA
  change MeasureTheory.Measure.bind (p σ₀).1 (fun aσ : α × s =>
          (@MeasureTheory.Measure.dirac (α × β) ⊤ (aσ.1, h aσ.2))) A
     = MeasureTheory.Measure.bind (q σ₀).1 (fun aσ : α × s =>
          (@MeasureTheory.Measure.dirac (α × β) ⊤ (aσ.1, h aσ.2))) A
  rw [MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable,
      MeasureTheory.Measure.bind_apply hA measurable_from_top.aemeasurable]
  exact ProgramDenotation.transferBy_wp_invariant h_transfer h_absorb
    (fun aσ : α × s => (@MeasureTheory.Measure.dirac (α × β) ⊤ (aσ.1, h aσ.2)) A)
    (fun a σ => h_inv (fun b => (@MeasureTheory.Measure.dirac (α × β) ⊤ (a, b)) A) σ) σ₀

end GaudisCrypt
