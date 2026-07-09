import GaudisCrypt.Logic.TransferBy
import GaudisCrypt.Logic.PRHL2

namespace GaudisCrypt.Language.Semantics

/-!
# The eager relational judgment (EasyCrypt's `eager` logic)

EasyCrypt's judgment `eager [S₁, c₁ ~ c₂, S₂] : P ==> Q` means
`{P} S₁; c₁ ~ c₂; S₂ {Q}` — **two independent swapped blocks**, leading on the
left program and trailing on the right.  We mirror that literally:

    `eagerR S₁ S₂ P p q Q  :=  {P}  S₁; p  ~  q; S₂  {Q}`   (as a `prhl2` coupling)

so `p` is the "eager" side (the block leads) and `q` the "lazy" side (the block
trails, keeping `q`'s result).  The generality of two blocks is load-bearing:
EC's `eager seq` threads a *middle* block
(`eager[S₁,c₁~c₁',S] → eager[S,c₂~c₂',S₂] → eager[S₁,c₁;c₂~c₁';c₂',S₂]`),
which `eagerR_seq` reproduces.  The judgment **is** a `prhl2` judgment about the
two composite programs, so a derivation built from the rules below is a pRHL
derivation.

## The bridge

At equality invariants the eager judgment is program equality of the composites:

* `prhl2_eq_iff` — **equality couplings are sound and complete** for program
  equality: `prhl2 (=) p q (=) ↔ ∀ σ, p σ = q σ`.  (Soundness is the diagonal
  coupling; completeness reads the marginals off the diagonal support, atom by
  atom.)
* `eagerR_eq_iff_transferBy` — the diagonal (`S₁ = S₂`) equality-invariant
  judgment is the distributional transfer relation, `transferBy S q p`.

The equality-invariant rules (`eagerR_pure`, `eagerR_seq`, `eagerR_while`,
`eagerR_zoom`) are proven through the bridge; `eagerR_conseq` is native.
EasyCrypt's own `eager` workflow runs at `={glob …}` invariants, which in this
shallow embedding are handled by composing the equality-invariant judgment with
invariant self-couplings (see the abstract-call rule in `Logic/EagerProc.lean`).
-/

/-- **The eager judgment** (EasyCrypt's `eager [S₁, p ~ q, S₂] : P ==> Q`):
    `{P} S₁; p ~ q; S₂ {Q}` as a `prhl2` coupling; the trailing block keeps `q`'s
    result. -/
def ProgramDenotation.eagerR {s α : Type} (S₁ S₂ : ProgramDenotation s Unit)
    (P : s → s → Prop) (p q : ProgramDenotation s α)
    (Q : α × s → α × s → Prop) : Prop :=
  ProgramDenotation.prhl2 P (S₁ >>= fun _ => p)
    (q >>= fun a => S₂ >>= fun _ => pure a) Q

/-! ## Equality couplings are sound and complete -/

/-- **Completeness**: a coupling with equality pre/post forces pointwise equal
    distributions — off-diagonal atoms vanish, so the two marginals agree atom
    by atom. -/
theorem ProgramDenotation.eq_of_prhl2_eq {s α : Type} {p q : ProgramDenotation s α}
    (h : ProgramDenotation.prhl2 (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v)) (σ : s) :
    p σ = q σ := by
  obtain ⟨μ, hm1, hm2, hsat⟩ := h σ σ rfl
  rw [← hm1, ← hm2]
  refine SubProbability.ext_of_expected (fun F => ?_)
  rw [SubProbability.expected_map μ (fun x => x.1) F,
      SubProbability.expected_map μ (fun x => x.2) F,
      SubProbability.expected_eq_tsum, SubProbability.expected_eq_tsum]
  refine tsum_congr (fun x => ?_)
  by_cases hx : μ.1 {x} = 0
  · rw [hx, mul_zero, mul_zero]
  · rw [hsat x hx]

/-- **Soundness**: pointwise equal programs couple diagonally. -/
theorem ProgramDenotation.prhl2_of_eq {s α : Type} {p q : ProgramDenotation s α}
    (h : ∀ σ, p σ = q σ) :
    ProgramDenotation.prhl2 (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v) := by
  have hpq : p = q := funext h
  subst hpq
  exact ProgramDenotation.prhl2.refl p

/-- **Equality couplings ↔ program equality.** -/
theorem ProgramDenotation.prhl2_eq_iff {s α : Type} (p q : ProgramDenotation s α) :
    ProgramDenotation.prhl2 (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
        (fun u v : α × s => u = v)
      ↔ ∀ σ, p σ = q σ :=
  ⟨ProgramDenotation.eq_of_prhl2_eq, ProgramDenotation.prhl2_of_eq⟩

/-- Introduce an equality-invariant eager judgment from program equality of the
    two composites (the semantic entry point for per-operation eager lemmas). -/
theorem ProgramDenotation.eagerR_of_eq {s α : Type}
    {S₁ S₂ : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h : (S₁ >>= fun _ => p) = (q >>= fun a => S₂ >>= fun _ => pure a)) :
    ProgramDenotation.eagerR S₁ S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v) :=
  ProgramDenotation.prhl2_of_eq (fun σ => congrFun h σ)

/-- Extract program equality of the composites from an equality-invariant eager
    judgment. -/
theorem ProgramDenotation.eagerR_to_eq {s α : Type}
    {S₁ S₂ : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h : ProgramDenotation.eagerR S₁ S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v)) :
    (S₁ >>= fun _ => p) = (q >>= fun a => S₂ >>= fun _ => pure a) :=
  funext (ProgramDenotation.eq_of_prhl2_eq h)

/-- **The bridge**: the diagonal equality-invariant eager judgment is the
    distributional transfer relation (note the side swap: `q` is the lazy side). -/
theorem ProgramDenotation.eagerR_eq_iff_transferBy {s α : Type}
    (S : ProgramDenotation s Unit) (p q : ProgramDenotation s α) :
    ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
        (fun u v : α × s => u = v)
      ↔ ProgramDenotation.transferBy S q p :=
  ⟨fun h => (ProgramDenotation.eagerR_to_eq h).symm,
   fun h => ProgramDenotation.eagerR_of_eq (Eq.symm h)⟩

/-! ## The eager rule set (equality invariants) -/

/-- Rule of consequence for the eager judgment (native, any invariants). -/
theorem ProgramDenotation.eagerR_conseq {s α : Type}
    {S₁ S₂ : ProgramDenotation s Unit}
    {P P' : s → s → Prop} {p q : ProgramDenotation s α}
    {Q Q' : α × s → α × s → Prop}
    (h : ProgramDenotation.eagerR S₁ S₂ P p q Q)
    (hP : ∀ σ₁ σ₂, P' σ₁ σ₂ → P σ₁ σ₂) (hQ : ∀ u v, Q u v → Q' u v) :
    ProgramDenotation.eagerR S₁ S₂ P' p q Q' :=
  ProgramDenotation.prhl2.conseq h hP hQ

/-- `pure` swaps with any block. -/
theorem ProgramDenotation.eagerR_pure {s α : Type} (S : ProgramDenotation s Unit)
    (a : α) :
    ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂) (pure a) (pure a)
      (fun u v : α × s => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mpr
    (ProgramDenotation.transferBy_pure a)

/-- The composite-equation form of `eager seq` (three blocks). -/
private lemma eager_seq_eq {s α β : Type} {S₁ S S₂ : ProgramDenotation s Unit}
    {p₁ q₁ : ProgramDenotation s α} {p₂ q₂ : α → ProgramDenotation s β}
    (h₁ : (S₁ >>= fun _ => p₁) = (q₁ >>= fun a => S >>= fun _ => pure a))
    (h₂ : ∀ a, (S >>= fun _ => p₂ a) = (q₂ a >>= fun b => S₂ >>= fun _ => pure b)) :
    (S₁ >>= fun _ => p₁ >>= p₂)
      = ((q₁ >>= q₂) >>= fun b => S₂ >>= fun _ => pure b) := by
  calc (S₁ >>= fun _ => p₁ >>= p₂)
      = (S₁ >>= fun _ => p₁) >>= p₂ := (ProgramDenotation.bind_assoc _ _ _).symm
    _ = (q₁ >>= fun a => S >>= fun _ => pure a) >>= p₂ := by rw [h₁]
    _ = q₁ >>= fun a => S >>= fun _ => p₂ a := by
        rw [ProgramDenotation.bind_assoc]
        congr 1; funext a
        rw [ProgramDenotation.bind_assoc]
        congr 1; funext _
        rw [ProgramDenotation.pure_bind]
    _ = q₁ >>= fun a => q₂ a >>= fun b => S₂ >>= fun _ => pure b := by
        congr 1; funext a
        rw [h₂ a]
    _ = (q₁ >>= q₂) >>= fun b => S₂ >>= fun _ => pure b :=
        (ProgramDenotation.bind_assoc _ _ _).symm

/-- **EC's `eager seq`**: eager judgments chain under `>>=` through a *middle*
    block `S` — `eager[S₁,p₁~q₁,S]` then `eager[S,p₂~q₂,S₂]` give
    `eager[S₁, p₁;p₂ ~ q₁;q₂, S₂]`. -/
theorem ProgramDenotation.eagerR_seq {s α β : Type}
    {S₁ S S₂ : ProgramDenotation s Unit}
    {p₁ q₁ : ProgramDenotation s α} {p₂ q₂ : α → ProgramDenotation s β}
    (h₁ : ProgramDenotation.eagerR S₁ S (fun σ₁ σ₂ : s => σ₁ = σ₂) p₁ q₁
      (fun u v : α × s => u = v))
    (h₂ : ∀ a, ProgramDenotation.eagerR S S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) (p₂ a) (q₂ a)
      (fun u v : β × s => u = v)) :
    ProgramDenotation.eagerR S₁ S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) (p₁ >>= p₂) (q₁ >>= q₂)
      (fun u v : β × s => u = v) :=
  ProgramDenotation.eagerR_of_eq
    (eager_seq_eq (ProgramDenotation.eagerR_to_eq h₁)
      (fun a => ProgramDenotation.eagerR_to_eq (h₂ a)))

/-- **EC's `eager while`** (same block at both ends): if the condition swaps with
    `S` and the body is eager, the loops are eager. -/
theorem ProgramDenotation.eagerR_while {s : Type} {S : ProgramDenotation s Unit}
    {cond : ProgramDenotation s Bool}
    (h_cond : ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂) cond cond
      (fun u v : Bool × s => u = v))
    {body_e body_l : ProgramDenotation s Unit}
    (h_body : ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂) body_e body_l
      (fun u v : Unit × s => u = v)) :
    ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂)
      (while_loop cond body_e) (while_loop cond body_l)
      (fun u v : Unit × s => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mpr
    (ProgramDenotation.transferBy_while_loop
      ((ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mp h_cond)
      ((ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mp h_body))

/-- **Zoom-lifting**: an eager judgment on the inner state lifts along a lens
    (the blocks lift with it). -/
theorem ProgramDenotation.eagerR_zoom {s t α : Type}
    (lens : GaudisCrypt.Lens s t)
    {S₁ S₂ : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    (h : ProgramDenotation.eagerR S₁ S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v)) :
    ProgramDenotation.eagerR
      (ProgramDenotation.zoom lens S₁) (ProgramDenotation.zoom lens S₂)
      (fun σ₁ σ₂ : t => σ₁ = σ₂)
      (ProgramDenotation.zoom lens p) (ProgramDenotation.zoom lens q)
      (fun u v : α × t => u = v) := by
  refine ProgramDenotation.eagerR_of_eq ?_
  have he := congrArg (ProgramDenotation.zoom lens) (ProgramDenotation.eagerR_to_eq h)
  rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_bind] at he
  calc (ProgramDenotation.zoom lens S₁ >>= fun _ => ProgramDenotation.zoom lens p)
      = ProgramDenotation.zoom lens S₁ >>= fun a =>
          ProgramDenotation.zoom lens ((fun _ : Unit => p) a) := rfl
    _ = ProgramDenotation.zoom lens q >>= fun a =>
          ProgramDenotation.zoom lens (S₂ >>= fun _ => pure a) := he
    _ = ProgramDenotation.zoom lens q >>= fun a =>
          ProgramDenotation.zoom lens S₂ >>= fun _ => pure a := by
        congr 1; funext a
        rw [ProgramDenotation.zoom_bind]
        congr 1; funext _
        rw [ProgramDenotation.zoom_pure]

/-! ## Invariant introduction

EasyCrypt's invariant-carrying eager rules (`eager seq … : R`, `eager while I`,
`eager proc I`) all decompose the same way, visible in the subgoals their kernel
generates: the **equality-invariant eager judgment** plus **framing
self-couplings** of one composite under the invariant (EC's `c ~ c` / `s ~ s :
I ==> I` side conditions).  The two master rules below are that decomposition as
a theorem: an invariant eager judgment is a self-coupling of either composite
glued to the equality judgment by `prhl2.trans`.  The EC-shaped composite rules
(`eagerR_seq_inv`, `eagerR_while_inv`, `eager_call_inv`) derive from them. -/

/-- **Invariant introduction (left)**: self-couple the eager composite `S₁; p`
    under the invariant, then glue the equality-invariant judgment on the right. -/
theorem ProgramDenotation.eagerR_of_self_left {s α : Type}
    {S₁ S₂ : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    {P : s → s → Prop} {Q : α × s → α × s → Prop}
    (hself : ProgramDenotation.prhl2 P (S₁ >>= fun _ => p) (S₁ >>= fun _ => p) Q)
    (heq : ProgramDenotation.eagerR S₁ S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v)) :
    ProgramDenotation.eagerR S₁ S₂ P p q Q := by
  have h := ProgramDenotation.prhl2.trans hself heq
  refine h.conseq (fun σ₁ σ₂ hp => ⟨σ₂, hp, rfl⟩) ?_
  rintro u v ⟨w, hw1, hw2⟩
  exact hw2 ▸ hw1

/-- **Invariant introduction (right)**: symmetrically, self-couple the lazy
    composite `q; S₂` under the invariant. -/
theorem ProgramDenotation.eagerR_of_self_right {s α : Type}
    {S₁ S₂ : ProgramDenotation s Unit} {p q : ProgramDenotation s α}
    {P : s → s → Prop} {Q : α × s → α × s → Prop}
    (heq : ProgramDenotation.eagerR S₁ S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v))
    (hself : ProgramDenotation.prhl2 P
      (q >>= fun a => S₂ >>= fun _ => pure a)
      (q >>= fun a => S₂ >>= fun _ => pure a) Q) :
    ProgramDenotation.eagerR S₁ S₂ P p q Q := by
  have h := ProgramDenotation.prhl2.trans heq hself
  refine h.conseq (fun σ₁ σ₂ hp => ⟨σ₁, rfl, hp⟩) ?_
  rintro u v ⟨w, hw1, hw2⟩
  exact hw1.symm ▸ hw2

/-- **EC's `eager seq` with invariants** (their four-subgoal form): the two
    equality-level eager judgments plus framing self-couplings of the eager-side
    pieces, threaded through a middle relation `M`. -/
theorem ProgramDenotation.eagerR_seq_inv {s α β : Type}
    {S₁ S S₂ : ProgramDenotation s Unit}
    {p₁ q₁ : ProgramDenotation s α} {p₂ q₂ : α → ProgramDenotation s β}
    {P : s → s → Prop} {M : α × s → α × s → Prop} {Q : β × s → β × s → Prop}
    (h₁ : ProgramDenotation.eagerR S₁ S (fun σ₁ σ₂ : s => σ₁ = σ₂) p₁ q₁
      (fun u v : α × s => u = v))
    (h₂ : ∀ a, ProgramDenotation.eagerR S S₂ (fun σ₁ σ₂ : s => σ₁ = σ₂) (p₂ a) (q₂ a)
      (fun u v : β × s => u = v))
    (hframe₁ : ProgramDenotation.prhl2 P (S₁ >>= fun _ => p₁) (S₁ >>= fun _ => p₁) M)
    (hframe₂ : ∀ a₁ a₂, ProgramDenotation.prhl2 (fun τ₁ τ₂ => M (a₁, τ₁) (a₂, τ₂))
      (p₂ a₁) (p₂ a₂) Q) :
    ProgramDenotation.eagerR S₁ S₂ P (p₁ >>= p₂) (q₁ >>= q₂) Q := by
  refine ProgramDenotation.eagerR_of_self_left ?_ (ProgramDenotation.eagerR_seq h₁ h₂)
  have hb := ProgramDenotation.prhl2.bind hframe₁ hframe₂
  rw [ProgramDenotation.bind_assoc] at hb
  exact hb

/-- **EC's `eager while` with invariants** (their six-subgoal form, coupling
    formulation): the equality-level eager judgments for guard and body, plus
    framing self-couplings — the block establishes the loop invariant `Inv`, the
    guard couples to agree under it, and the body preserves it. -/
theorem ProgramDenotation.eagerR_while_inv {s : Type} {S : ProgramDenotation s Unit}
    {cond : ProgramDenotation s Bool} {body_e body_l : ProgramDenotation s Unit}
    {P : s → s → Prop} {Inv : s → s → Prop} {PostC : Bool → s → s → Prop}
    (h_cond_eq : ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂) cond cond
      (fun u v : Bool × s => u = v))
    (h_body_eq : ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂) body_e body_l
      (fun u v : Unit × s => u = v))
    (hS_self : ProgramDenotation.prhl2 P S S (fun u v : Unit × s => Inv u.2 v.2))
    (h_cond_self : ProgramDenotation.prhl2 Inv cond cond
      (fun u v => u.1 = v.1 ∧ PostC u.1 u.2 v.2))
    (h_body_self : ProgramDenotation.prhl2 (PostC true) body_e body_e
      (fun u v => Inv u.2 v.2)) :
    ProgramDenotation.eagerR S S P (while_loop cond body_e) (while_loop cond body_l)
      (fun u v : Unit × s => PostC false u.2 v.2) := by
  refine ProgramDenotation.eagerR_of_self_left ?_
    (ProgramDenotation.eagerR_while h_cond_eq h_body_eq)
  exact ProgramDenotation.prhl2.bind hS_self
    (fun _ _ => ProgramDenotation.prhl2.while_loop h_cond_self h_body_self)

/-! ## Endpoint conversion -/

/-- **Absorb the trailing block into a direct coupling**: from a diagonal eager
    judgment and losslessness of `S`, couple the lazy side `q` directly against
    the `S`-led eager side, with equal results and any `S`-preserved state
    projection `g` (e.g. `={glob A}`) equal on the final states. -/
theorem ProgramDenotation.eagerR_to_coupling {s α β : Type}
    {S : ProgramDenotation s Unit} {p q : ProgramDenotation s α} (g : s → β)
    (hll : ∀ σ : s, (S σ).1 Set.univ = 1)
    (hkeep : ∀ σ : s, (S σ).satisfies (fun x : Unit × s => g x.2 = g σ))
    (h : ProgramDenotation.eagerR S S (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v)) :
    ProgramDenotation.prhl2 (fun σ₁ σ₂ : s => σ₁ = σ₂) q (S >>= fun _ => p)
      (fun u v => u.1 = v.1 ∧ g u.2 = g v.2) :=
  ProgramDenotation.prhl2_of_lossless_tail_proj g hll hkeep
    ((ProgramDenotation.eagerR_eq_iff_transferBy S p q).mp h)

end GaudisCrypt.Language.Semantics
