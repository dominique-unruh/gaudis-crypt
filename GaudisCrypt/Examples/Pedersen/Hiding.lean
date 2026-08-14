import GaudisCrypt.Examples.Pedersen.Pedersen
import GaudisCrypt.Logic.PRHL2

/-!
# Perfect hiding of the Pedersen commitment scheme

A port of EasyCrypt's `pedersen_perfect_hiding` (`examples/Pedersen.ec`), keeping its structure:

```
local module FakeCommit(U:Unhider) = {          (* commitment is message-independent *)
  proc main() = { x <$ dt; h <- g^x; (m0,m1) <@ U.choose(h);
                  b <$ {0,1}; d <$ dt; c <- g^d; b' <@ U.guess(c); return (b = b'); } }

local lemma phi_hi           : Pr[HidingExperiment(Pedersen,U).main()] = Pr[FakeCommit(U).main()]
local lemma fakecommit_half  : Pr[FakeCommit(U).main()] = 1/2
lemma pedersen_perfect_hiding: Pr[HidingExperiment(Pedersen,U).main()] = 1/2
```

`phi_hi` is EC's `byequiv … rnd (fun d => d + x*(b?m1:m0)) (fun d => d - x*(b?m1:m0))`: a
relational step coupling the two `d` samplings by a *translation*, under which the real
commitment `g^d * h^m` and the fake one `g^d'` coincide.  Here that is `prhl2.uniform` with
`Equiv.addRight (x * m)` — the same move as `otp_perfect_secrecy` in `Logic/PRHL2Demo.lean`.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt
open PedersenGroup (G F g)

variable [ProgramSpec] [PedersenGroup]

/-! ## Denotation-level procedure lemmas (EC's `inline`)

The pRHL layer works on `ProgramDenotation`s, but the games are written in the procedure DSL.
These lift the existing `wp_gen`/`wp_commit` from the `wp` level to the program level, which is
what lets the relational rules apply at all.  `wp p f st = (p st).expected f` holds definitionally,
so `SubProbability.ext_of_expected` turns a `wp` equation into a program equation directly. -/

theorem gen_denotation :
    procedureDenotation (sig := procsig () -> CommitmentTypes.Value) Pedersen.gen.procedure ()
      = (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun x => pure (g ^ x) := by
  funext st
  refine SubProbability.ext_of_expected fun post => ?_
  change (procedureDenotation (sig := procsig () -> CommitmentTypes.Value)
    Pedersen.gen.procedure ()).wp post st = _
  rw [wp_gen]
  change _ = ((ProgramDenotation.uniform : ProgramDenotation State F) >>=
    fun x => pure (g ^ x)).wp post st
  rw [wp_bind, wp_uniform]
  simp [wp_pure]

theorem commit_denotation (args : G × F) :
    procedureDenotation
        (sig := procsig (CommitmentTypes.Value, CommitmentTypes.Message) ->
          (CommitmentTypes.Commitment × CommitmentTypes.OpeningKey))
        Pedersen.commit.procedure args
      = (ProgramDenotation.uniform : ProgramDenotation State F) >>=
          fun d => pure (g ^ d * args.1 ^ args.2, d) := by
  funext st
  refine SubProbability.ext_of_expected fun post => ?_
  change (procedureDenotation
    (sig := procsig (CommitmentTypes.Value, CommitmentTypes.Message) ->
      (CommitmentTypes.Commitment × CommitmentTypes.OpeningKey))
    Pedersen.commit.procedure args).wp post st = _
  rw [wp_commit]
  change _ = ((ProgramDenotation.uniform : ProgramDenotation State F) >>=
    fun d => pure (g ^ d * args.1 ^ args.2, d)).wp post st
  rw [wp_bind, wp_uniform]
  simp [wp_pure]

/-! ## The two games

Both are written with Pedersen's procedures already inlined (EC's `inline*`), so that the
relational proof below has the two sampling sequences literally side by side. -/

/-- `HidingExperiment(Pedersen, U).main`, inlined. -/
noncomputable def realGame (U : Unhider) : ProgramDenotation State Bool :=
  (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun x =>
  procedureDenotation (Unhider.choose U).procedure (g ^ x) >>= fun mm =>
  (ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
  (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
  procedureDenotation (Unhider.guess U).procedure
      (g ^ d * (g ^ x) ^ (if b then mm.2 else mm.1 : F)) >>= fun bg =>
  pure (b == bg)

/-- EC's `FakeCommit(U)`: identical, except the commitment `g ^ d` does not mention the
    message.  EC keeps the "useless" `h`/`c` lines because the parallel structure is what makes
    the relational proof go through; the same is true here. -/
noncomputable def fakeGame (U : Unhider) : ProgramDenotation State Bool :=
  (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun x =>
  procedureDenotation (Unhider.choose U).procedure (g ^ x) >>= fun mm =>
  (ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
  (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
  procedureDenotation (Unhider.guess U).procedure (g ^ d) >>= fun bg =>
  pure (b == bg)

/-- The algebraic heart of `phi_hi`, EC's `algebra` call: the real commitment at opening key `d`
    is the fake one at `d + x * m`.  `g^d * (g^x)^m = g^d * g^(x*m) = g^(d + x*m)`. -/
theorem commit_shift (x m d : F) :
    g ^ d * (g ^ x) ^ m = g ^ (d + x * m) := by
  rw [PedersenGroup.pow_mul, ← PedersenGroup.pow_add]

/-! ## `phi_hi` — the game hop

EC:
```
byequiv => //. proc; inline*.
call (_:true); wp;
rnd (fun d, (d + x * (b?m1:m0)){2}) (fun d, (d - x * (b?m1:m0)){2});
by wp; rnd; call (_: true); auto => />; progress; algebra.
```
Read bottom-up, that is: couple the `x` draws by the identity, run `U.choose` on both sides
(same program, same argument), couple the coins by the identity, then **couple the two `d`
draws by the translation `d ↦ d + x * m`** — which is where `commit_shift` makes the two
commitments coincide — and finally run `U.guess` on what is now literally the same argument.

Each `call (_:true)` is `prhl2.refl`: the adversary is the *same* program on both sides, started
in equal states.  The `rcases eq_or_ne` steps are bookkeeping Lean needs and EC does not: a
`Mid` of the form `x₀ = x₁ ∧ τ₁ = τ₂` has to be turned into an actual substitution before the two
sides are syntactically the same program. -/
theorem phi_hi (U : Unhider) :
    ProgramDenotation.prhl2 (Eq : State → State → Prop)
      (realGame U) (fakeGame U) (fun u v : Bool × State => u = v) := by
  unfold realGame fakeGame
  -- `x <$ dt` — identity coupling
  refine ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    (ProgramDenotation.prhl2.uniform_id fun _ _ _ h => ⟨rfl, h⟩) ?_
  rintro x₀ x₁
  rcases eq_or_ne x₀ x₁ with rfl | hne
  case inr => intro _ _ h; exact absurd h.1 hne
  refine ProgramDenotation.prhl2.conseq (A := (Eq : State → State → Prop))
    ?_ (fun _ _ h => h.2) (fun _ _ h => h)
  -- `(m0,m1) <@ U.choose(h)` — same program, same argument
  refine ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    ((ProgramDenotation.prhl2.refl _).conseq (fun _ _ h => h)
      (fun _ _ h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)) ?_
  rintro mm₀ mm₁
  rcases eq_or_ne mm₀ mm₁ with rfl | hne
  case inr => intro _ _ h; exact absurd h.1 hne
  refine ProgramDenotation.prhl2.conseq (A := (Eq : State → State → Prop))
    ?_ (fun _ _ h => h.2) (fun _ _ h => h)
  -- `b <$ {0,1}` — identity coupling
  refine ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    (ProgramDenotation.prhl2.uniform_id fun _ _ _ h => ⟨rfl, h⟩) ?_
  rintro b₀ b₁
  rcases eq_or_ne b₀ b₁ with rfl | hne
  case inr => intro _ _ h; exact absurd h.1 hne
  refine ProgramDenotation.prhl2.conseq (A := (Eq : State → State → Prop))
    ?_ (fun _ _ h => h.2) (fun _ _ h => h)
  -- **the hop**: `d` on the left is `d + x * m` on the right, so the commitments agree
  refine ProgramDenotation.prhl2.bind
    (M := fun u v =>
      g ^ u.1 * (g ^ x₀) ^ (if b₀ then mm₀.2 else mm₀.1 : F) = g ^ v.1 ∧ u.2 = v.2)
    (ProgramDenotation.prhl2.uniform
      (Equiv.addRight (x₀ * (if b₀ then mm₀.2 else mm₀.1 : F)))
      (fun d _ _ h => ⟨commit_shift _ _ d, h⟩)) ?_
  rintro d₀ d₁ τ₁ τ₂ ⟨hcomm, rfl⟩
  -- the two `U.guess` calls now have literally the same argument
  rw [hcomm]
  exact (ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    ((ProgramDenotation.prhl2.refl _).conseq (fun _ _ h => h)
      (fun _ _ h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩))
    (fun _ _ => ProgramDenotation.prhl2.pure_pure
      (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; rfl))) τ₁ τ₁ rfl

/-! ## `fakecommit_half` — the fake game returns `true` with probability exactly `1/2`

EC does this with `swap 4 3; rnd (pred1 b')`: move the coin past the adversary (legitimate, they
are independent), then observe that a fresh fair coin matches `b'` with probability `1/2`.

The same content, without needing a `swap` rule: the coin's sum is already outermost, and for
each fixed `d` the *inner* sum over `b` of `⟦b = b'⟧` collapses through the adversary by
`wp_finset_sum` — `∑ b, ⟦b = b'⟧ = 1` whatever `b'` is — leaving the adversary's own mass, which
is `1` by losslessness.  So the coin never has to be commuted past anything.

Losslessness of the adversary is a genuine hypothesis (EC's `islossless U.choose/guess`): with a
sub-probability semantics an adversary that diverges would make this `≤ 1/2`. -/
theorem fakecommit_half (U : Unhider) (σ : State)
    (h_choose : ∀ (x : CommitmentTypes.Value) (τ : State),
      (procedureDenotation (Unhider.choose U).procedure x).wp (fun _ => (1 : ENNReal)) τ = 1)
    (h_guess : ∀ (c : CommitmentTypes.Commitment) (τ : State),
      (procedureDenotation (Unhider.guess U).procedure c).wp (fun _ => (1 : ENNReal)) τ = 1) :
    (fakeGame U).wp (fun r => if r.1 then 1 else 0) σ = 1 / 2 := by
  -- for each fixed `d`, summing the indicator over the coin collapses to the adversary's mass
  -- stated in the shape `wp_bind` leaves behind, so it can be rewritten in place
  have coin : ∀ (d : F) (τ : State),
      ∑ b : Bool, (procedureDenotation (Unhider.guess U).procedure (g ^ d)).wp
        (fun p => (pure (b == p.1) : ProgramDenotation State Bool).wp
          (fun r => if r.1 then 1 else 0) p.2) τ = 1 := by
    intro d τ
    have hsimp : ∀ b : Bool,
        (procedureDenotation (Unhider.guess U).procedure (g ^ d)).wp
          (fun p => (pure (b == p.1) : ProgramDenotation State Bool).wp
            (fun r => if r.1 then 1 else 0) p.2) τ
        = (procedureDenotation (Unhider.guess U).procedure (g ^ d)).wp
            (fun p => if b == p.1 then 1 else 0) τ := by
      intro b; simp [wp_pure]
    rw [Finset.sum_congr rfl (fun b _ => hsimp b), ← ProgramDenotation.wp_finset_sum]
    have hone : (fun p : Bool × State => ∑ b : Bool, if b == p.1 then (1 : ENNReal) else 0)
        = fun _ => 1 := by
      funext p; cases hp : p.1 <;> simp
    rw [hone]
    exact h_guess _ τ
  have hcardF : (Fintype.card F : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hcardF' : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  -- the `b`/`d`/`guess` block is `1/2` from any state
  have inner : ∀ τ : State,
      ((ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
        (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
        procedureDenotation (Unhider.guess U).procedure (g ^ d) >>= fun bg =>
        pure (b == bg)).wp (fun r => if r.1 then 1 else 0) τ = 1 / 2 := by
    intro τ
    simp only [wp_bind, wp_uniform]
    -- pull the scalars outside so the two sums become adjacent and can be swapped.
    -- (`Finset.sum_div` wants a `DivisionSemiring`, which `ENNReal` is not — go via `mul_inv`.)
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun d _ => coin d τ)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [ENNReal.mul_inv_cancel hcardF hcardF']
    simp
  -- `U.choose` cannot change that: its result is not looked at, so only its mass matters
  have afterChoose : ∀ (x : F) (τ : State),
      (procedureDenotation (Unhider.choose U).procedure (g ^ x) >>= fun _ =>
        (ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
        (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
        procedureDenotation (Unhider.guess U).procedure (g ^ d) >>= fun bg =>
        pure (b == bg)).wp (fun r => if r.1 then 1 else 0) τ = 1 / 2 := by
    intro x τ
    rw [wp_bind]
    have hconst : (fun p : (CommitmentTypes.Message × CommitmentTypes.Message) × State =>
        ((ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
          (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
          procedureDenotation (Unhider.guess U).procedure (g ^ d) >>= fun bg =>
          pure (b == bg)).wp (fun r => if r.1 then 1 else 0) p.2)
        = fun _ => (1 / 2 : ENNReal) * (1 : ENNReal) := by
      funext p; rw [mul_one]; exact inner p.2
    rw [hconst, ProgramDenotation.wp_const_mul, h_choose, mul_one]
  -- and the outer `x <$ dt` averages a constant
  unfold fakeGame
  rw [wp_bind, wp_uniform]
  simp only [afterChoose, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.mul_div_cancel' (fun h => absurd h hcardF) (fun h => absurd h hcardF')]

/-! ## Putting the two together

EC: `by move => uc_ll ug_ll; rewrite (phi_hi U &m) (fakecommit_half U &m).`

`phi_hi` is a coupling; `to_relE` turns it into the two-sided wp inequality and `relE.wp_eq`
into the equality of expectations — that is EC's `byequiv`.  The postcondition is literal
equality of `(result, state)`, so *any* observable transfers, the indicator of `res` included. -/

/-- **Perfect hiding**, on the inlined game: for any lossless adversary the hiding game returns
    `true` with probability exactly `1/2`. -/
theorem realGame_half (U : Unhider) (σ : State)
    (h_choose : ∀ (x : CommitmentTypes.Value) (τ : State),
      (procedureDenotation (Unhider.choose U).procedure x).wp (fun _ => (1 : ENNReal)) τ = 1)
    (h_guess : ∀ (c : CommitmentTypes.Commitment) (τ : State),
      (procedureDenotation (Unhider.guess U).procedure c).wp (fun _ => (1 : ENNReal)) τ = 1) :
    (realGame U).wp (fun r => if r.1 then 1 else 0) σ = 1 / 2 := by
  rw [ProgramDenotation.relE.wp_eq (phi_hi U).to_relE (fun _ _ h => by rw [h]) rfl]
  exact fakecommit_half U σ h_choose h_guess

/-- The same, as a probability of an event — the spelling `pedersen_correctness` uses. -/
theorem realGame_hiding (U : Unhider) (σ : State)
    (h_choose : ∀ (x : CommitmentTypes.Value) (τ : State),
      (procedureDenotation (Unhider.choose U).procedure x).wp (fun _ => (1 : ENNReal)) τ = 1)
    (h_guess : ∀ (c : CommitmentTypes.Commitment) (τ : State),
      (procedureDenotation (Unhider.guess U).procedure c).wp (fun _ => (1 : ENNReal)) τ = 1) :
    (realGame U σ).ofEvent {r : Bool × State | r.1 = true} = 1 / 2 := by
  have hi := expectation_indicator (realGame U σ) {r : Bool × State | r.1 = true} 1
  rw [one_mul] at hi
  have hind : ({r : Bool × State | r.1 = true}).indicator (fun _ => (1 : ENNReal))
      = fun r => if r.1 then 1 else 0 := by
    funext r; by_cases h : r.1 = true <;> simp [Set.indicator, h]
  rw [hind] at hi
  have h2 : (↑((realGame U σ).ofEvent {r : Bool × State | r.1 = true}) : ENNReal) = 1 / 2 := by
    rw [← hi]; exact realGame_half U σ h_choose h_guess
  have h3 : ((1 / 2 : NNReal) : ENNReal) = (1 / 2 : ENNReal) := by norm_num
  exact ENNReal.coe_inj.mp (h2.trans h3.symm)

end GaudisCrypt.Examples.Pedersen
