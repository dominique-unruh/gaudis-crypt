import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Lib.EC.Group
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECInlineParams

/-!
# The discrete logarithm assumption (EasyCrypt `theories/crypto/DLog.ec`)

The theory `DLog` over a cyclic group of prime order (`Lib/EC/Group.lean`: EC's
`clone Group.CyclicGroup as G`, `clone G.PowZMod as GP`, `clone GP.FDistr as FD` at the head of
the file): the standard experiment, the one whose adversary may fail, and the reduction of the
second to the first (`StdRedAdversary`, `dlog_standard_reduction`).
-/

set_option ec.strict true
set_option linter.dupNamespace false

namespace GaudisCrypt.EC.DLog

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.CyclicGroup

variable {group exp : Type} [CommGroup group] [Field exp] [Fintype exp] [DecidableEq exp]
  [CyclicGroup.Params group exp]

/-! ## `theory DLog` -/

namespace DLog

-- the standard definition of the discrete logarithm experiment
moduletype StdAdversary {
  proc guess (h : group) -> exp;
}

module DLogStdExperiment using (A : StdAdversary) {
  proc main () : Bool {
    var x : exp, x' : exp;
    x <$ dt;
    x' <- call A.guess (g ^ $x);
    return decide ($x' = $x)
  };
}

-- a modified definition in which the adversary may fail
moduletype Adversary {
  proc guess (h : group) -> (Option exp);
}

module DLogExperiment using (A : Adversary) {
  proc main () : Bool {
    var x : exp, x' : Option exp;
    x <$ dt;
    x' <- call A.guess (g ^ $x);
    return decide ($x' = some $x)
  };
}

end DLog

/-! ## Reduction of the experiment admitting failure to the standard one -/

module StdRedAdversary using (L : DLog.Adversary) {
  proc guess (h : group) : exp {
    var lx : Option exp, x : exp;
    lx <- call L.guess ($h);
    if (decide ($lx = none)) {
      x <$ dt;
    } else {
      x <- oget $lx;
    }
    return $x
  };
}

section DLogSecurity

declare module L <: DLog.Adversary

theorem dlog_standard_reduction (m : VariableAssignment) :
    Pr[ DLog.DLogExperiment(L).main () @ &m : §res ] ≤
      Pr[ DLog.DLogStdExperiment(StdRedAdversary(L)).main () @ &m : §res ] := by
  -- byequiv => //; proc; inline*.
  byequiv
  case hE => exact fun _ _ _ _ h => h
  equiv_proc; stmt_inline*
  -- wp; seq 2 3: (x'{1} = lx{2} /\ x{1} = x{2}).
  stmt_wp; equiv_seq 2 3 : (§x'{1} = §lx{2} ∧ ={x})
  -- + by call (_: true); auto.
  · equiv_call (_ : ={glob L}); equiv_auto
  -- if{2} => //; last by auto.
  stmt_if{2}
  case «else» => equiv_auto; smt_close [oget]
  -- auto => />; apply dt_ll.
  equiv_auto

end DLogSecurity

end GaudisCrypt.EC.DLog
