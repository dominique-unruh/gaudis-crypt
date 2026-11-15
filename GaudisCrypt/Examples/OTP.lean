import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECRnd

/-!
# One-time pad: perfect secrecy against any adversary

The adversary picks a message `m`, sees a ciphertext and guesses a bit.  In the real game the
ciphertext is `m + k` for a fresh uniform key `k`; in the ideal game it is uniform, independent
of `m`.  The two games are equivalent for every adversary (`real_ideal`), so the adversary's
guess has the same distribution in both (`real_ideal_Pr`).

Not an EasyCrypt file; written as one would be:

```
type msg.                        (* a finite group, written additively *)

module type Adversary = {
  proc choose() : msg
  proc guess(c : msg) : bool
}.

module Real(A : Adversary) = {
  proc main() : bool = {
    var m, k, c, b;
    m <@ A.choose();
    k <$ dmsg;
    c <- m + k;
    b <@ A.guess(c);
    return b;
  }
}.

module Ideal(A : Adversary) = {
  proc main() : bool = {
    var m, c, b;
    m <@ A.choose();
    c <$ dmsg;
    b <@ A.guess(c);
    return b;
  }
}.

section.
declare module A <: Adversary.

equiv real_ideal : Real(A).main ~ Ideal(A).main : ={glob A} ==> ={res, glob A}.
proof.
proc.
call (_ : true); wp.
rnd (fun k => m{1} + k) (fun c => c - m{1}).
call (_ : true).
by auto.
qed.

lemma real_ideal_Pr &m :
  Pr[Real(A).main() @ &m : res] = Pr[Ideal(A).main() @ &m : res].
proof. by byequiv real_ideal. qed.
end section.
```

No assumption on the adversary: its procedures run on their own locals and globals, and the
games' variables that differ (`k`, `c`) are local to `main`.
-/

set_option ec.strict true
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt.Examples.OTP

open GaudisCrypt GaudisCrypt.EC

/-- The theory's type: the messages (and keys and ciphertexts), a finite group. -/
class Params (msg : outParam Type) [AddCommGroup msg] [Fintype msg] [Inhabited msg] : Prop

variable {msg : Type} [AddCommGroup msg] [Fintype msg] [Inhabited msg] [Params msg]

/-- The uniform distribution on messages. -/
noncomputable abbrev dmsg : SubProbability msg := SubProbability.uniform

moduletype Adversary {
  proc choose () -> msg;
  proc guess (c : msg) -> Bool;
}

module Real using (A : Adversary) {
  proc main () : Bool {
    var m : msg, k : msg, c : msg, b : Bool;
    m <- call A.choose ();
    k <$ dmsg;
    c <- $m + $k;
    b <- call A.guess ($c);
    return $b
  };
}

module Ideal using (A : Adversary) {
  proc main () : Bool {
    var m : msg, c : msg, b : Bool;
    m <- call A.choose ();
    c <$ dmsg;
    b <- call A.guess ($c);
    return $b
  };
}

section

declare module A <: Adversary

/-- **Perfect secrecy**: the real and the ideal game are equivalent, for every adversary. -/
theorem real_ideal :
    equiv[ Real(A).main ~ Ideal(A).main : ={glob A} ==> ={res, glob A} ] := by
  equiv_proc
  equiv_call (_ : True); stmt_wp
  equiv_rnd (fun k => §m{1} + k) (fun c => c - §m{1})
  equiv_call (_ : True)
  equiv_auto

/-- **Perfect secrecy, as probabilities**: the guess has the same distribution in the two
games. -/
theorem real_ideal_Pr (m : VariableAssignment) :
    Pr[ Real(A).main () @ &m : §res ] = Pr[ Ideal(A).main () @ &m : §res ] := by
  byequiv (real_ideal A)

end

end GaudisCrypt.Examples.OTP
