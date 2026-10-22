import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Logic.PRHLWp

/-!
# One-time pad: perfect secrecy against any adversary

The adversary picks a message `m`, sees a ciphertext and guesses a bit.  In the real game the
ciphertext is `m + k` for a fresh uniform key `k`; in the ideal game it is uniform, independent
of `m`.  The two games are *equivalent*: for every adversary, from equal globals, the guesses are
coupled to be equal — so every event about the guess (and the final globals) has the same
probability in both.

The relational proof is EasyCrypt's: `proc; inline`, the calls to the adversary related by
reflexivity (`call (_ : true)`), and the key coupled with the ciphertext along `k ↦ m + k`
(`rnd`), a bijection that pushes the uniform key to the uniform ciphertext.  No assumption on
the adversary at all: its procedures run on their own locals, and the game's state that differs
(`k`, `c`) is local to `main`.
-/

namespace GaudisCrypt.Examples.OTP

open GaudisCrypt

/-- The message (and key and ciphertext) space: a finite group. -/
structure Space where
  G : Type
  [group : AddCommGroup G]
  [fintype : Fintype G]
  [nonempty : Nonempty G]

@[reducible] instance (S : Space) : AddCommGroup S.G := S.group
@[reducible] instance (S : Space) : Fintype S.G := S.fintype
instance (S : Space) : Nonempty S.G := S.nonempty
noncomputable instance (S : Space) : Inhabited S.G := ⟨Classical.arbitrary _⟩

variable (S : Space)

moduletype Adversary {
  proc choose () -> S.G;
  proc guess (c : S.G) -> Bool;
}

module Real using (A : Adversary S) {
  proc main () : Bool {
    var m : S.G, k : S.G, c : S.G, b : Bool;
    m <- call A.choose ();
    k <$ SubProbability.uniform;
    c <- $m + $k;
    b <- call A.guess ($c);
    return $b
  };
}

module Ideal using (A : Adversary S) {
  proc main () : Bool {
    var m : S.G, c : S.G, b : Bool;
    m <- call A.choose ();
    c <$ SubProbability.uniform;
    b <- call A.guess ($c);
    return $b
  };
}

/-- **Perfect secrecy**: the real and the ideal game are equivalent, for every adversary. -/
theorem real_ideal (A : Adversary S) :
    equiv[ (Module.app (Real S) A) ~ (Module.app (Ideal S) A) :
      §allGlobals{1} = §allGlobals{2} ==> ={res, allGlobals} ] := by
  equiv_proc
  stmt_inline 0
  stmt_wp
  equiv_call prhlProc_refl _
  stmt_wp{1}
  equiv_rnd (fun k => §m{1} + k)
  equiv_call prhlProc_refl _
  stmt_wp
  equiv_skip
  exact fun _ _ h => ⟨h, fun _ _ _ _ h' _ => ⟨h'.2, fun _ _ _ _ h'' => h''⟩⟩

/-- **Perfect secrecy, as probabilities**: every event about the guess and the final globals has
the same probability in the two games (EC's `byequiv`). -/
theorem real_ideal_Pr (A : Adversary S) (E : Bool → VariableAssignment → Prop)
    (m : VariableAssignment) :
    Procedure.Pr (Module.Proc.procedure (Module.app (Real S) A)) () m E
      = Procedure.Pr (Module.Proc.procedure (Module.app (Ideal S) A)) () m E :=
  Procedure.Pr_eq_of_prhlProc (real_ideal S A)
    (fun r₁ g₁ r₂ g₂ (h : r₁ = r₂ ∧ g₁ = g₂) => by rw [h.1, h.2]) rfl

end GaudisCrypt.Examples.OTP
