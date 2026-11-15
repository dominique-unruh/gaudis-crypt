import GaudisCrypt.Lib.EC.DiffieHellman
import GaudisCrypt.Lib.EC.PKE.PKE_CPA
import GaudisCrypt.Lib.EC.BitWordRing
import GaudisCrypt.Lib.EC.Logic
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
import GaudisCrypt.Logic.ECInlineParams
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.ECRnd

/-!
# Hashed ElGamal is IND-CPA under DDH and entropy smoothing
(EasyCrypt `examples/hashed_elgamal_std.ec`)

EC's file, declaration by declaration and script line by line; all five lemmas are proven.
(`Examples/EasyCryptBench/HashedElGamal.lean` is the older version, to be replaced by this
file.)

Translation (as `Examples/ElGamal.lean`):
* `op k : { int | 0 < k } as gt0_k` is the class `Params`; `clone import BitWord as Bits with
  op n <- k … rename "word" as "bits" "dunifin" as "dbits"` is the abbreviations `bits`, `dbits`
  of `Lib/EC/BitWord.lean` at `k`.
* The theory `EntropySmoothing` is declared in the file and imported, not cloned: a namespace,
  its `type hkey`, `op dhkey`, `op hash` the class `EntropySmoothing.Params group hkey`.  EC's
  `hint exact random : dhkey_ll` is `attribute [ec_random]`.
* `module type AdvES = { proc guess(_: hkey * bits) : bool }` takes one pair, which EC identifies
  with two parameters (`ESAdv(A).guess (hk, h)` declares two, `A.guess(hk,h)` passes two): two
  parameters here.
* EC's type abbreviations `pkey`, `skey`, `ptxt`, `ctxt` are written out in the clone of
  `PKE_CPA`; `declare axiom`s are section hypotheses; `Gb` takes the section's `A` as its
  parameter.

Gap list (the examples' infrastructure batch; numbers as in `Examples/ElGamal.lean` where the
gap is the same):
* GAP 1: `inline` writes a call's parameters as one tuple assignment, EC as one per parameter:
  `stmt_split_params` after `stmt_inline*`.
* GAP 2: `swap{1} 1 1` moves the first statement of an inlined body later: `inline` leaves a
  `reset_vars` of the callee's locals before it, which EC's count attaches to that statement,
  and the reset does not commute with the next statement (it resets its variable).  Written
  with our position, `stmt_swap_raw{1} 2 1`, which moves the sampling alone.  (Moving earlier
  past a reset works.)
* GAP 3: in `Gb_half` EC calls `Ag_ll` and `Ac_ll` by hand (`call Ag_ll; auto. call Ac_ll;
  auto=> />; rewrite dhkey_ll dt_ll dbits_ll`); `phoare_call` followed by `phoare_auto` computes
  through the code before the call and leaves an expectation, so the lossless part is one
  `islossless`.
* EC's `rnd f` (an involution) is `equiv_rnd f f`.
-/

set_option ec.strict true

-- EasyCrypt names the theory's class like the file's (`EntropySmoothing.Params`); the scheme's
-- name `Hashed_ElGamal` is EC's (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.Examples.HashedElGamal

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.CyclicGroup
open GaudisCrypt.EC.DiffieHellman.DDH (DDH0 DDH1)

/-- EC's `op k : { int | 0 < k } as gt0_k`. -/
class Params where
  k : ℤ
  gt0_k : 0 < k

variable [HashedElGamal.Params]

/-- `op k`: the length of a plaintext. -/
def k : ℤ := Params.k

theorem gt0_k : 0 < k := Params.gt0_k

/-! `clone import BitWord as Bits with op n <- k proof gt0_n by exact/gt0_k rename "word" as
"bits" "dunifin" as "dbits"` -/

/-- EC's `bits`. -/
abbrev bits := BitWord.word k

/-- EC's `dbits`. -/
noncomputable abbrev dbits : SubProbability bits := BitWord.dunifin

variable {group exp : Type} [CommGroup group] [Field exp] [Fintype exp]
  [CyclicGroup.Params group exp]

/-! ## Assumption: entropy smoothing -/

namespace EntropySmoothing

/-- EC's `type hkey`, `op dhkey : { hkey distr | is_lossless dhkey } as dhkey_ll` and
`op hash : hkey -> group -> bits`. -/
class Params (group hkey : outParam Type) [HashedElGamal.Params] where
  dhkey : SubProbability hkey
  dhkey_ll : is_lossless dhkey
  hash : hkey → group → bits

export Params (dhkey dhkey_ll hash)

-- EC's `hint exact random : dhkey_ll.`
attribute [ec_random] Params.dhkey_ll

variable {hkey : Type} [Inhabited hkey] [EntropySmoothing.Params group hkey]

moduletype AdvES {
  proc guess (hk : hkey, h : bits) -> Bool;
}

module ES0 using (A : AdvES) {
  proc main () : Bool {
    var b : Bool, hk : hkey, h : bits;
    hk <$ dhkey;
    h <$ dbits;
    b <- call A.guess ($hk, $h);
    return $b
  };
}

module ES1 using (A : AdvES) {
  proc main () : Bool {
    var b : Bool, hk : hkey, z : exp;
    hk <$ dhkey;
    z <$ dt;
    b <- call A.guess ($hk, hash $hk (g ^ $z));
    return $b
  };
}

end EntropySmoothing

open EntropySmoothing

variable {hkey : Type} [Inhabited hkey] [EntropySmoothing.Params group hkey]

clone import GaudisCrypt.EC.PKE_CPA as PKE_ with
  type pkey <- hkey × group, type skey <- hkey × exp, type ptxt <- bits, type ctxt <- group × bits

module Hashed_ElGamal : Scheme {
  proc kg () : ((hkey × group) × (hkey × exp)) {
    var hk : hkey, sk : exp;
    hk <$ dhkey;
    sk <$ dt;
    return (($hk, g ^ $sk), ($hk, $sk))
  };
  proc enc (pk : hkey × group, m : bits) : (group × bits) {
    var y : exp, h : bits;
    y <$ dt;
    h <- hash ($pk).1 (($pk).2 ^ $y);
    return (g ^ $y, $h +^ $m)
  };
  proc dec (sk : hkey × exp, c : group × bits) : (Option bits) {
    var gy : group, h : bits, hm : bits;
    gy, hm <- $c;
    h <- hash ($sk).1 ($gy ^ ($sk).2);
    return some ($h +^ $hm)
  };
}

module DDHAdv using (A : Adversary) {
  proc guess (gx : group, gy : group, gz : group) : Bool {
    var hk : hkey, m0 : bits, m1 : bits, b : Bool, b' : Bool, h : bits;
    hk <$ dhkey;
    m0, m1 <- call A.choose (($hk, $gx));
    b <$ dbool;
    h <- hash $hk $gz;
    b' <- call A.guess (($gy, $h +^ (if $b then $m1 else $m0)));
    return decide ($b' = $b)
  };
}

module ESAdv using (A : Adversary) {
  proc guess (hk : hkey, h : bits) : Bool {
    var x : exp, y : exp, m0 : bits, m1 : bits, b : Bool, b' : Bool;
    x <$ dt;
    y <$ dt;
    m0, m1 <- call A.choose (($hk, g ^ $x));
    b <$ dbool;
    b' <- call A.guess ((g ^ $y, $h +^ (if $b then $m1 else $m0)));
    return decide ($b' = $b)
  };
}

-- EC's `local module Gb` of the section, with the section's `A` as its parameter
module Gb using (A : Adversary) {
  proc main () : Bool {
    var hk : hkey, x : exp, y : exp, v : bits, m0 : bits, m1 : bits, b : Bool, b' : Bool;
    hk <$ dhkey;
    x <$ dt;
    y <$ dt;
    m0, m1 <- call A.choose (($hk, g ^ $x));
    v <$ dbits;
    b' <- call A.guess ((g ^ $y, $v));
    b <$ dbool;
    return decide ($b' = $b)
  };
}

section Security

declare module A <: Adversary

variable (Ac_ll : islossless A.choose) (Ag_ll : islossless A.guess)

/-- EC's `local lemma cpa_ddh0 &m: Pr[CPA(Hashed_ElGamal,A).main() @ &m : res] =
Pr[DDH0(DDHAdv(A)).main() @ &m : res]`. -/
theorem cpa_ddh0 (m : VariableAssignment) :
    Pr[ CPA(Hashed_ElGamal, A).main () @ &m : §res ] =
      Pr[ DDH0(DDHAdv(A)).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline *.
  byequiv; equiv_proc; stmt_inline*
  -- EC: swap{1} 1 1; swap{1} 8 -6; swap{2} 6 -3.
  --     (GAP 1: the parameters of the inlined calls, one assignment each, first;
  --     GAP 2: the first statement of the inlined `kg` by its position among ours)
  stmt_split_params
  stmt_swap_raw{1} 2 1; stmt_swap{1} 8 -6; stmt_swap{2} 6 -3
  -- EC: auto; call (: true).
  equiv_auto; equiv_call (_ : True)
  -- EC: auto; call (: true).
  equiv_auto; equiv_call (_ : True)
  -- EC: by auto=> /> sk _ y _ hk _ [m0 m1] b _ /=; rewrite -expM.
  equiv_auto; smt_close [expM]

/-- EC's `local lemma ddh1_es1 &m: Pr[DDH1(DDHAdv(A)).main() @ &m : res] =
Pr[ES1(ESAdv(A)).main() @ &m : res]`. -/
theorem ddh1_es1 (m : VariableAssignment) :
    Pr[ DDH1(DDHAdv(A)).main () @ &m : §res ] = Pr[ ES1(ESAdv(A)).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline *.
  byequiv; equiv_proc; stmt_inline*
  -- EC: swap{1} 7 -3; swap{2} [5..6] -4; swap{2} 4 -1.
  --     (GAP 1)
  stmt_split_params
  stmt_swap{1} 7 -3; stmt_swap{2} [5..6] -4; stmt_swap{2} 4 -1
  -- EC: auto; call (: true).
  equiv_auto; equiv_call (_ : True)
  -- EC: auto; call (:true).
  equiv_auto; equiv_call (_ : True)
  -- EC: by auto.
  equiv_auto

/-- EC's `local lemma es0_Gb &m: Pr[ES0(ESAdv(A)).main() @ &m : res] =
Pr[Gb.main()@ &m : res]`. -/
theorem es0_Gb (m : VariableAssignment) :
    Pr[ ES0(ESAdv(A)).main () @ &m : §res ] = Pr[ Gb(A).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline *.
  byequiv; equiv_proc; stmt_inline*
  -- EC: swap{1} 2 1. swap{1} [3..4] 4. swap{2} 7 -2.
  --     (GAP 1)
  stmt_split_params
  stmt_swap{1} 2 1; stmt_swap{1} [3..4] 4; stmt_swap{2} 7 -2
  -- EC: auto; call (: true); wp.
  equiv_auto; equiv_call (_ : True); stmt_wp
  -- EC: rnd (fun w, w +^ (b0{1} ? m1{1} : m0{1})).
  --     (EC's `rnd f` is `rnd f f`: `f` is its own inverse)
  equiv_rnd (fun w => w +^ (if §b0{1} then §m1{1} else §m0{1}))
    (fun w => w +^ (if §b0{1} then §m1{1} else §m0{1}))
  -- EC: auto; call (: true).
  equiv_auto; equiv_call (_ : True)
  -- EC: by auto=> /> *; split => *; algebra.
  equiv_auto

include Ac_ll Ag_ll in
/-- EC's `local lemma Gb_half &m: Pr[Gb.main()@ &m : res] = 1%r/2%r`. -/
theorem Gb_half (m : VariableAssignment) :
    Pr[ Gb(A).main () @ &m : §res ] = 1 / 2 := by
  -- EC: byphoare=> //; proc.
  byphoare; phoare_proc
  -- EC: rnd (pred1 b')=> /=; conseq (_:_ ==> true).
  --     + by move=> /> b; rewrite dbool1E.
  phoare_rnd (pred1 §b'); phoare_conseq (: _ ==> True)
  · smt_close [mu_pred1, dbool1E_mu1, pred1E]
  -- EC: call Ag_ll; auto.
  --     by call Ac_ll; auto=> />; rewrite dhkey_ll dt_ll dbits_ll.
  --     (EC's two calls and the samplings' losslessness are `islossless`: GAP 3)
  islossless <;> [exact Ag_ll; exact Ac_ll]

include Ac_ll Ag_ll in
/-- EC's `lemma conclusion &m : `| Pr[CPA(Hashed_ElGamal,A).main() @ &m : res] - 1%r/2%r | <=
`| Pr[DDH0(DDHAdv(A)).main() @ &m : res] - Pr[DDH1(DDHAdv(A)).main() @ &m : res] | +
`| Pr[ES0(ESAdv(A)).main() @ &m : res] - Pr[ES1(ESAdv(A)).main() @ &m : res]|`. -/
theorem conclusion (m : VariableAssignment) :
    |Pr[ CPA(Hashed_ElGamal, A).main () @ &m : §res ] - 1 / 2| ≤
      |Pr[ DDH0(DDHAdv(A)).main () @ &m : §res ] - Pr[ DDH1(DDHAdv(A)).main () @ &m : §res ]| +
        |Pr[ ES0(ESAdv(A)).main () @ &m : §res ] - Pr[ ES1(ESAdv(A)).main () @ &m : §res ]| := by
  -- EC: rewrite (cpa_ddh0 &m) (ddh1_es1 &m) (es0_Gb &m) (Gb_half &m).
  rw [cpa_ddh0 A m, ddh1_es1 A m, es0_Gb A m, Gb_half A Ac_ll Ag_ll m]
  -- EC: smt(StdOrder.RealOrder.ler_dist_add).
  rw [abs_sub_comm (1 / 2 : ℝ)]
  exact abs_sub_le _ _ _

end Security

end GaudisCrypt.Examples.HashedElGamal
