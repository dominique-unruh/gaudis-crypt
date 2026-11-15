import GaudisCrypt.Lib.EC.DiffieHellman
import GaudisCrypt.Lib.EC.PKE.PKE_CPA
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Syntax.ModuleSubtype
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECAutoStrict
import GaudisCrypt.Logic.ECClose
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Lib.EC.Logic

/-!
# ElGamal is IND-CPA under DDH (EasyCrypt `examples/elgamal.ec`)

EC's file, declaration by declaration and script line by line (the pilot of the examples'
re-port, 2026-11-15; `Examples/EasyCryptBench/ElGamal.lean` is the older version, to be replaced
by this file once the gaps below are closed).  All four lemmas are proven.

Translation:
* `clone DiffieHellman as DH. import DH.DDH DH.G DH.GP DH.FD DH.GP.ZModE.` clones the theory
  without instantiating it: the file stays abstract in the group, which is the section's
  `variable {group exp} … [CyclicGroup.Params group exp]` (`Lib/EC/Group.lean`), and the theory
  `DDH` is opened.  `clone DH.GP.ZModE.ZModpField as ZPF` is Mathlib's `Field exp`.
* EC's type abbreviations `pkey = group`, `skey = exp`, `ptxt = group`, `ctxt = group * group`
  are written out in the clone of `PKE_CPA`.
* `declare axiom Ac_ll`, `Ag_ll` are section hypotheses, `include`d where EC's proofs use them.
* EC's `local module Gb` reads the section's `A`; here `A` is its parameter (`Gb(A).main`), and
  it is declared before the section.

Gap list (what keeps the file from reading as EC's; each is an item of the examples'
infrastructure batch):
* GAP 1: `inline` writes a call's parameters as one tuple assignment, EC as one assignment per
  parameter, so EC's positions are off by the number of parameters less one, and a `swap`
  between two parameters has nothing to move past: `stmt_split_pair` before EC's `swap`s.
* GAP 2: EC's `call (_ : true)` on the adversary is written `equiv_call (_ : ={glob A})`: there
  is no `equiv_call (_ : I)` for a plain invariant.
* GAP 3 (closed 2026-11-15): `Gb_half` is EC's script; pHL `rnd E` and `conseq` on an exact
  bound and the tactic `islossless` are `Logic/PHoareRnd.lean`.
* GAP 4: EC's `module ElGamal : Scheme` has a third procedure, `dec`, which `Scheme` does not
  list.  `module M : T` wants exactly `T`'s procedures: `dec` is left out.
* GAP 5: EC's `rnd f g` takes the bijection and its inverse; `equiv_rnd f` takes `f` and finds
  the push-forward of the uniform distribution by itself (`dt` is an abbreviation for that).
* GAP 6 (goals as shown): `byequiv` states `§allGlobals{1} = §allGlobals{2}` where EC shows
  `={glob A}`; a clone's game prints as `Module.app CPA (Module.pair ElGamal A)`, not
  `CPA(ElGamal, A).main`.
-/

set_option ec.strict true

-- EasyCrypt names the scheme after the file (`ElGamal.ElGamal`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.Examples.ElGamal

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.CyclicGroup
open GaudisCrypt.EC.DiffieHellman.DDH (DDH0 DDH1)

variable {group exp : Type} [CommGroup group] [Field exp] [Fintype exp]
  [CyclicGroup.Params group exp]

clone import GaudisCrypt.EC.PKE_CPA as PKE with
  type pkey <- group, type skey <- exp, type ptxt <- group, type ctxt <- group × group

module ElGamal : Scheme {
  proc kg () : (group × exp) {
    var sk : exp;
    sk <$ dt;
    return (g ^ $sk, $sk)
  };
  proc enc (pk : group, m : group) : (group × group) {
    var y : exp;
    y <$ dt;
    return (g ^ $y, $pk ^ $y * $m)
  };
}

module DDHAdv using (A : Adversary) {
  proc guess (gx : group, gy : group, gz : group) : Bool {
    var m0 : group, m1 : group, b : Bool, b' : Bool;
    m0, m1 <- call A.choose ($gx);
    b <$ dbool;
    b' <- call A.guess (($gy, $gz * (if $b then $m1 else $m0)));
    return decide ($b' = $b)
  };
}

-- EC's `local module Gb` of the section, with the section's `A` as its parameter
module Gb using (A : Adversary) {
  proc main () : Bool {
    var x : exp, y : exp, z : exp, m0 : group, m1 : group, b : Bool, b' : Bool;
    x <$ dt;
    y <$ dt;
    m0, m1 <- call A.choose (g ^ $x);
    z <$ dt;
    b' <- call A.guess ((g ^ $y, g ^ $z));
    b <$ dbool;
    return decide ($b' = $b)
  };
}

section Security

declare module A <: Adversary

variable (Ac_ll : islossless A.choose) (Ag_ll : islossless A.guess)

/-- EC's `local lemma cpa_ddh0 &m: Pr[CPA(ElGamal,A).main() @ &m : res] =
Pr[DDH0(DDHAdv(A)).main() @ &m : res]`. -/
theorem cpa_ddh0 (m : VariableAssignment) :
    Pr[ CPA(ElGamal, A).main () @ &m : §res ] = Pr[ DDH0(DDHAdv(A)).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline *.
  byequiv; equiv_proc; stmt_inline*
  -- EC: swap{1} 7 -5.
  --     (GAP 1: the parameters of `enc`, one assignment each, first)
  stmt_split_pair{1} 6
  stmt_swap{1} 7 -5
  -- EC: auto; call (_:true).
  equiv_auto; equiv_call (_ : ={glob A})
  -- EC: auto; call (_:true).
  equiv_auto; equiv_call (_ : ={glob A})
  -- EC: by auto=> /> sk _ y _ r b _; rewrite expM.
  equiv_auto; smt_close [expM]

/-- EC's `local lemma ddh1_gb &m: Pr[DDH1(DDHAdv(A)).main() @ &m : res] =
Pr[Gb.main() @ &m : res]`. -/
theorem ddh1_gb (m : VariableAssignment) :
    Pr[ DDH1(DDHAdv(A)).main () @ &m : §res ] = Pr[ Gb(A).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline *.
  byequiv; equiv_proc; stmt_inline*
  -- EC: swap{1} 3 2; swap{1} [5..6] 2; swap{2} 6 -2.
  --     (GAP 1: the parameters of `DDHAdv(A).guess`, one assignment each, first)
  stmt_split_pair{1} 4
  stmt_swap{1} 3 2; stmt_swap{1} [5..6] 2; stmt_swap{2} 6 -2
  -- EC: auto; call (_:true); wp.
  equiv_auto; equiv_call (_ : ={glob A}); stmt_wp
  -- EC: rnd (fun z, z + loge (if b then m1 else m0){2})
  --         (fun z, z - loge (if b then m1 else m0){2}).
  equiv_rnd (fun z => z + loge (if §b{2} then §m1{2} else §m0{2}))
  -- EC: auto; call (_:true).
  equiv_auto; equiv_call (_ : ={glob A})
  -- EC: auto; progress.
  --     - by rewrite ZPF.addrAC -ZPF.addrA ZPF.subrr ZPF.addr0.
  --     - by rewrite  -ZPF.addrA ZPF.subrr ZPF.addr0.
  --     - by rewrite expD expgK.
  --     (the two conditions on the bijection are found by `equiv_rnd`, GAP 5)
  equiv_auto; smt_close [expD, expgK]

include Ac_ll Ag_ll in
/-- EC's `local lemma Gb_half &m: Pr[Gb.main()@ &m : res] = 1%r/2%r`. -/
theorem Gb_half (m : VariableAssignment) :
    Pr[ Gb(A).main () @ &m : §res ] = 1 / 2 := by
  -- EC: byphoare=> //; proc.
  byphoare; phoare_proc
  -- EC: rnd  (pred1 b')=> //=.
  phoare_rnd (pred1 §b')
  -- EC: conseq (: _ ==> true).
  --     + by move=> /> b; rewrite dbool1E pred1E.
  phoare_conseq (: _ ==> True)
  · smt_close [mu_pred1, dbool1E_mu1, pred1E]
  -- EC: islossless;[ apply Ag_ll | apply Ac_ll].
  islossless <;> [exact Ag_ll; exact Ac_ll]

include Ac_ll Ag_ll in
/-- EC's `lemma conclusion &m : `| Pr[CPA(ElGamal,A).main() @ &m : res] - 1%r/2%r | =
`| Pr[DDH0(DDHAdv(A)).main() @ &m : res] - Pr[DDH1(DDHAdv(A)).main() @ &m : res] |`. -/
theorem conclusion (m : VariableAssignment) :
    |Pr[ CPA(ElGamal, A).main () @ &m : §res ] - 1 / 2| =
      |Pr[ DDH0(DDHAdv(A)).main () @ &m : §res ] - Pr[ DDH1(DDHAdv(A)).main () @ &m : §res ]| := by
  -- EC: by rewrite (cpa_ddh0 &m) (ddh1_gb &m) (Gb_half &m).
  rw [cpa_ddh0 A m, ddh1_gb A m, Gb_half A Ac_ll Ag_ll m]

end Security

end GaudisCrypt.Examples.ElGamal
