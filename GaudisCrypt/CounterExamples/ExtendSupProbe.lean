import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.Basic

/-!
# Computational probe: is `extend_sup` true (deterministic `Function.End` model)?

`fvP_extend_sup` (over the kernel monoid) is sorry'd; the question is whether it is even *true*.
The kernel monoid is infinite, but its obstruction is the corner double-commutant identity
`u '' (CC W) = CC (u '' W)`, which already makes sense in the **finite** deterministic model
`Function.End` (the Dirac part). This file brute-forces that model:

* focus `Foc = Fin 2`, state `St = Fin 2 × Fin 2`, lens `fst`,
* `u f = fun p => (f p.1, p.2)` is the lens-corner embedding (`= Lens.update fst`),
* `cen` / `cc` are the centralizer / bicommutant under composition,
* a "range" is a bicommutant-closed set (`cc S = S`); `extend r = cc (u '' r)`.

We then check `extend (r₁ ⊔ r₂) = extend r₁ ⊔ extend r₂` for **every** pair of ranges and report
any counterexample. (A failure here strongly suggests the probabilistic `fvP_extend_sup` is false;
no failure suggests it is true and my earlier pessimism was wrong.)
-/

open Finset

abbrev Foc := Fin 2
abbrev St := Fin 2 × Fin 2
abbrev Ma := Foc → Foc
abbrev Mb := St → St

/-- Centralizer of `S` (under composition) inside the full endomorphism monoid. -/
def cen {α : Type} [DecidableEq α] [Fintype α] (S : Finset (α → α)) : Finset (α → α) :=
  (univ : Finset (α → α)).filter (fun h => ∀ g ∈ S, g ∘ h = h ∘ g)

/-- Bicommutant closure. -/
def cc {α : Type} [DecidableEq α] [Fintype α] (S : Finset (α → α)) : Finset (α → α) :=
  cen (cen S)

/-- The lens-corner embedding `Foc-endo ↦ St-endo` (act on the first coordinate). -/
def u (f : Ma) : Mb := fun p => (f p.1, p.2)

def uimg (S : Finset Ma) : Finset Mb := S.image u

/-- `extend r`'s updates: bicommutant of the localized image. -/
def extendUpd (r : Finset Ma) : Finset Mb := cc (uimg r)

/-- Join of two ranges (= bicommutant of the union of updates). -/
def joinA (r₁ r₂ : Finset Ma) : Finset Ma := cc (r₁ ∪ r₂)
def joinB (s₁ s₂ : Finset Mb) : Finset Mb := cc (s₁ ∪ s₂)

/-- The ranges of `Ma`: bicommutant-closed subsets. -/
def rangesA : Finset (Finset Ma) :=
  ((univ : Finset Ma).powerset).filter (fun S => cc S = S)

/-- `extend_sup` for one pair, as a Bool. -/
def extendSupHolds (r₁ r₂ : Finset Ma) : Bool :=
  decide (extendUpd (joinA r₁ r₂) = joinB (extendUpd r₁) (extendUpd r₂))

/-- All range pairs violating `extend_sup`. -/
def counterexamples : Finset (Finset Ma × Finset Ma) :=
  (rangesA ×ˢ rangesA).filter (fun p => ! extendSupHolds p.1 p.2)

/-- The underlying identity `extend_sup` needs, for an arbitrary set `W`:
    `u '' (CC W) = CC (u '' W)`. -/
def coreIdentityHolds (W : Finset Ma) : Bool := decide (uimg (cc W) = cc (uimg W))

/-- All subsets `W ⊆ Ma` violating the core identity. -/
def coreCounterexamples : Finset (Finset Ma) :=
  ((univ : Finset Ma).powerset).filter (fun W => ! coreIdentityHolds W)

-- RESULTS (see info output on build):
#eval rangesA.card                 -- 5 : bicommutant-closed sets in End(Fin 2)
#eval counterexamples.card         -- 0 : extend_sup holds for EVERY pair of ranges
#eval ((univ : Finset Ma).powerset).card  -- 16 : all subsets of Ma
#eval coreCounterexamples.card     -- 0 : u '' (CC W) = CC (u '' W) holds for EVERY subset W

/-! ### Proof-strategy probe: does `extend` have a right adjoint?

`extend r ≤ R ⟺ r.updates ⊆ u⁻¹'(R.updates)`. So `extend` has a right adjoint (hence preserves
all joins, giving `extend_sup` *and* `reduce_sup` for free) iff `u⁻¹'(R.updates)` is bicommutant-closed
for every range `R`. We test that on the corner ranges that actually arise. -/

/-- Preimage of a set of `Mb`-endos under `u`. -/
def uPre (R : Finset Mb) : Finset Ma := (univ : Finset Ma).filter (fun f => u f ∈ R)

/-- Is `u⁻¹'(R)` bicommutant-closed in `Ma`? -/
def uPreClosed (R : Finset Mb) : Bool := decide (cc (uPre R) = uPre R)

/-- The corner ranges appearing in `extend_sup`: `extend r` and `extend r₁ ⊔ extend r₂`. -/
def cornerRanges : Finset (Finset Mb) :=
  (rangesA.image extendUpd) ∪
  ((rangesA ×ˢ rangesA).image (fun p => joinB (extendUpd p.1) (extendUpd p.2)))

#eval cornerRanges.card                                        -- how many distinct corner ranges
#eval (cornerRanges.filter (fun R => ! uPreClosed R)).card     -- 0 ⟺ u⁻¹'(R) closed for all of them

/-
CONCLUSION (deterministic `Function.End` model, focus = Fin 2, complement = Fin 2):
  `extend_sup` and the underlying corner double-commutant identity hold in ALL cases
  (0 counterexamples over all 16 subsets / all 5×5 range pairs).
This contradicts the earlier "correlating-kernel" pessimism — the commutant of a localized
generator set stays clean. Evidence that `fv_extend_sup` (and plausibly `fvP_extend_sup`) is
TRUE, and the right move is to prove it, not disprove it.
-/
