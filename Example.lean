import Mathlib.Order.OmegaCompletePartialOrder

/-!
Minimal example: `fun_prop` vs `match` on `Bool`.

`fun_prop` handles `Bool.casesOn` once given a `@[fun_prop]` lemma for `Bool.rec`.
It fails on `match b with | true => ... | false => ...` because Lean compiles that
syntax via an auto-generated auxiliary `f.match_1` that `fun_prop` treats as opaque.
-/

-- Register a fun_prop rule for Bool.rec (covers Bool.casesOn too).
@[fun_prop]
theorem Bool.rec_ωScottContinuous
    {X : Type*} [OmegaCompletePartialOrder X]
    {α : Bool → Type*} [∀ b, OmegaCompletePartialOrder (α b)]
    (a : Bool) {g : X → α false} {f : X → α true}
    (hg : OmegaCompletePartialOrder.ωScottContinuous g)
    (hf : OmegaCompletePartialOrder.ωScottContinuous f) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun x => Bool.rec (motive := α) (g x) (f x) a) := by
  cases a <;> [exact hg; exact hf]

-- The return type `α b` is dependent on `b`, so `match` generates a `match_1` auxiliary.

-- Using Bool.casesOn: fun_prop SUCCEEDS.
def dispatch_casesOn {X : Type*} {α : Bool → Type*}
    (f : X → α true) (g : X → α false) (b : Bool) (x : X) : α b :=
  Bool.casesOn b (g x) (f x)

theorem dispatch_casesOn_cont
    {X : Type*} [OmegaCompletePartialOrder X]
    {α : Bool → Type*} [∀ b, OmegaCompletePartialOrder (α b)]
    {f : X → α true} {g : X → α false}
    (hf : OmegaCompletePartialOrder.ωScottContinuous f)
    (hg : OmegaCompletePartialOrder.ωScottContinuous g) (b : Bool) :
    OmegaCompletePartialOrder.ωScottContinuous (dispatch_casesOn f g b) := by
  unfold dispatch_casesOn
  fun_prop  -- OK

-- Using match syntax: Lean generates `dispatch_match.match_1`, which fun_prop cannot
-- see through, even if it is marked @[reducible].
def dispatch_match {X : Type*} {α : Bool → Type*}
    (f : X → α true) (g : X → α false) (b : Bool) (x : X) : α b :=
  match b with
  | true => f x
  | false => g x

-- fun_prop fails: "No theorems found for `dispatch_match.match_1`"
theorem dispatch_match_cont_broken
    {X : Type*} [OmegaCompletePartialOrder X]
    {α : Bool → Type*} [∀ b, OmegaCompletePartialOrder (α b)]
    {f : X → α true} {g : X → α false}
    (hf : OmegaCompletePartialOrder.ωScottContinuous f)
    (hg : OmegaCompletePartialOrder.ωScottContinuous g) (b : Bool) :
    OmegaCompletePartialOrder.ωScottContinuous (dispatch_match f g b) := by
  unfold dispatch_match
  fun_prop  -- ERROR: No theorems found for `dispatch_match.match_1`

-- Workaround: delta-unfold the auxiliary first, then fun_prop can continue.
theorem dispatch_match_cont
    {X : Type*} [OmegaCompletePartialOrder X]
    {α : Bool → Type*} [∀ b, OmegaCompletePartialOrder (α b)]
    {f : X → α true} {g : X → α false}
    (hf : OmegaCompletePartialOrder.ωScottContinuous f)
    (hg : OmegaCompletePartialOrder.ωScottContinuous g) (b : Bool) :
    OmegaCompletePartialOrder.ωScottContinuous (dispatch_match f g b) := by
  unfold dispatch_match
  delta dispatch_match.match_1
  fun_prop  -- OK
