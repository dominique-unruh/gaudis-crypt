import GaudisCrypt.Logic.TransferBy
import GaudisCrypt.Logic.PRHL2

namespace GaudisCrypt.Language.Semantics

/-!
# The eager relational judgment (EasyCrypt's `eager` logic)

EasyCrypt's judgment `eager [S, c ~ c', S] : P ==> Q` means `{P} S; c ~ c'; S {Q}`
— the block `S` migrates from before one program to after the other.  Here we
take the mirror-image convention matching `transferBy`:

    `eagerR S P p q Q  :=  {P}  p; S  ~  S; q  {Q}`     (as a `prhl2` coupling)

so `p` is the "lazy" side (the swapped block trails it) and `q` the "eager" side
(the block leads).  The judgment **is** a `prhl2` judgment about the two composite
programs, so a derivation built from the rules below is a pRHL derivation.

## The bridge

At equality invariants the eager judgment coincides with the distributional
transfer calculus:

* `prhl2_eq_iff` — **equality couplings are sound and complete** for program
  equality: `prhl2 (=) p q (=) ↔ ∀ σ, p σ = q σ`.  (Soundness is the diagonal
  coupling; completeness reads the marginals off the diagonal support, atom by
  atom.)
* `eagerR_eq_iff_transferBy` — `eagerR S (=) p q (=) ↔ transferBy S p q`.

The bridge imports the whole `transferBy` rule set (`GaudisCrypt.Logic.TransferBy`)
into eager form: `eagerR_pure`, `eagerR_bind` (EC's `eager seq`), `eagerR_while`
(EC's `eager while`).  Native relational proofs can replace the transports if
invariants other than equality are ever needed mid-derivation — EasyCrypt's own
`eager` workflow runs at `={glob …}`, which in this shallow embedding is exactly
state equality.

`eagerR_to_coupling` converts a finished eager derivation into a direct coupling
of `p` against the `S`-absorbed eager side, recording any state projection that
`S` preserves (e.g. `={glob A}`) — the endpoint step of a `FullEager`-style proof.
-/

/-- **The eager judgment**: `{P} p; S ~ S; q {Q}`, as a `prhl2` coupling (the swapped
    block `S` keeps `p`'s result on the left). -/
def ProgramDenotation.eagerR {s α : Type} (S : ProgramDenotation s Unit)
    (P : s → s → Prop) (p q : ProgramDenotation s α)
    (Q : α × s → α × s → Prop) : Prop :=
  ProgramDenotation.prhl2 P (p >>= fun a => S >>= fun _ => pure a)
    (S >>= fun _ => q) Q

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

/-- **The bridge**: at equality invariants, the eager judgment is the
    distributional transfer relation. -/
theorem ProgramDenotation.eagerR_eq_iff_transferBy {s α : Type}
    (S : ProgramDenotation s Unit) (p q : ProgramDenotation s α) :
    ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
        (fun u v : α × s => u = v)
      ↔ ProgramDenotation.transferBy S p q := by
  constructor
  · intro h
    exact funext (ProgramDenotation.eq_of_prhl2_eq h)
  · intro h
    exact ProgramDenotation.prhl2_of_eq (fun σ => congrFun h σ)

/-! ## The eager rule set (equality invariants, by transport) -/

/-- Rule of consequence for the eager judgment (native). -/
theorem ProgramDenotation.eagerR_conseq {s α : Type} {S : ProgramDenotation s Unit}
    {P P' : s → s → Prop} {p q : ProgramDenotation s α}
    {Q Q' : α × s → α × s → Prop}
    (h : ProgramDenotation.eagerR S P p q Q)
    (hP : ∀ σ₁ σ₂, P' σ₁ σ₂ → P σ₁ σ₂) (hQ : ∀ u v, Q u v → Q' u v) :
    ProgramDenotation.eagerR S P' p q Q' :=
  ProgramDenotation.prhl2.conseq h hP hQ

/-- `pure` is eager-invariant (EC: the empty program swaps with anything). -/
theorem ProgramDenotation.eagerR_pure {s α : Type} (S : ProgramDenotation s Unit)
    (a : α) :
    ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) (pure a) (pure a)
      (fun u v : α × s => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mpr
    (ProgramDenotation.transferBy_pure a)

/-- **EC's `eager seq`**: eager judgments chain under `>>=`. -/
theorem ProgramDenotation.eagerR_bind {s α β : Type} {S : ProgramDenotation s Unit}
    {p q : ProgramDenotation s α} {p' q' : α → ProgramDenotation s β}
    (h : ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v))
    (h' : ∀ a, ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) (p' a) (q' a)
      (fun u v : β × s => u = v)) :
    ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) (p >>= p') (q >>= q')
      (fun u v : β × s => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mpr
    (ProgramDenotation.transferBy_bind
      ((ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mp h)
      (fun a => (ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mp (h' a)))

/-- **EC's `eager while`**: if the condition swaps with `S` (self-eager) and the
    body is eager, the loops are eager. -/
theorem ProgramDenotation.eagerR_while {s : Type} {S : ProgramDenotation s Unit}
    {cond : ProgramDenotation s Bool}
    (h_cond : ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) cond cond
      (fun u v : Bool × s => u = v))
    {body_lazy body_eager : ProgramDenotation s Unit}
    (h_body : ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) body_lazy body_eager
      (fun u v : Unit × s => u = v)) :
    ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂)
      (while_loop cond body_lazy) (while_loop cond body_eager)
      (fun u v : Unit × s => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mpr
    (ProgramDenotation.transferBy_while_loop
      ((ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mp h_cond)
      ((ProgramDenotation.eagerR_eq_iff_transferBy S _ _).mp h_body))

/-! ## Endpoint conversion -/

/-- **Absorb the eager block into a direct coupling**: from an eager derivation and
    losslessness of `S`, couple `p` directly against the `S`-led eager side, with
    equal results and any `S`-preserved state projection `g` (e.g. `={glob A}`)
    equal on the final states. -/
theorem ProgramDenotation.eagerR_to_coupling {s α β : Type}
    {S : ProgramDenotation s Unit} {p q : ProgramDenotation s α} (g : s → β)
    (hll : ∀ σ : s, (S σ).1 Set.univ = 1)
    (hkeep : ∀ σ : s, (S σ).satisfies (fun x : Unit × s => g x.2 = g σ))
    (h : ProgramDenotation.eagerR S (fun σ₁ σ₂ : s => σ₁ = σ₂) p q
      (fun u v : α × s => u = v)) :
    ProgramDenotation.prhl2 (fun σ₁ σ₂ : s => σ₁ = σ₂) p (S >>= fun _ => q)
      (fun u v => u.1 = v.1 ∧ g u.2 = g v.2) :=
  ProgramDenotation.prhl2_of_lossless_tail_proj g hll hkeep
    ((ProgramDenotation.eagerR_eq_iff_transferBy S p q).mp h)

end GaudisCrypt.Language.Semantics
