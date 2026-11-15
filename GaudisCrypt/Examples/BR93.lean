import GaudisCrypt.Lib.EC.ROM
import GaudisCrypt.Lib.EC.OW
import GaudisCrypt.Lib.EC.IsUniform
import GaudisCrypt.Lib.EC.Logic
import GaudisCrypt.Lib.EC.ListFind
import GaudisCrypt.Syntax.Clone
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Syntax.ModuleVar
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
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.StmtSwap
import GaudisCrypt.Logic.ECInlineParams
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.ECRnd

/-!
# Bellare and Rogaway's encryption scheme is IND-CPA (EasyCrypt `examples/br93.ec`)

Bellare and Rogaway, "Random oracles are practical: a paradigm for designing efficient
protocols" (1993): `enc pk m = (f pk r, H r +^ m)` for a one-way trapdoor permutation `f` and a
random oracle `H`.  EC's `abstract theory BR93` (lines 1–422 of `br93.ec`), declaration by
declaration and script line by line: correctness, and the reduction
`Pr[BR93_CPA(A).main : res] - 1/2 ≤ Pr[OW(I(A)).main : res]` by three games (the oracle call of
the challenge replaced by a sampling, up to the adversary querying `r`; the one-time pad
`h +^ m` replaced by `h`; the inverter).  All of the theory's lemmas are proven.

The second half of EC's file (lines 425–659, the instance on bitstrings and its `Reduction` in
the textbook's notation) is not ported: see GAP 9.

Translation:
* `abstract theory BR93` with its types and operators is `class Params (ptxt rand pkey skey)`;
  the theory's `clone import ROM as H`, `clone import OW as OW_rand` are clones
  (`Lib/EC/ROM.lean`, `Lib/EC/OW.lean`).
* `module type Adv (ARO : POracle) = { proc a1 …  proc a2 … }` is
  `abbrev Adv := POracle →ₘ AdvProcs`; `declare module A <: Adv {…}`,
  `declare axiom A_a1_ll (O <: POracle {-A}) : islossless O.o => islossless A(O).a1` are
  `declare module` and a section `variable` with the same binder.
* A module's `var x` is `module_var M.x : T` before the module.
* `x \in LRO.m` is `FMap.dom §LRO.m x`; `witness` is `default`.

Gap list (what keeps the file from reading as EC's):
* GAP 1: `local module Game1 = BR93_CPA(A) with { … }` and `Game2 = Game1 with { … }` (EC's
  module update) are written out as full modules `Game1`, `Game2` with the parameter `A`.
* GAP 2: `={glob Log, glob LRO}` in an invariant is `={glob A, Log.qs, LRO.m}` (`glob M` of a
  concrete module is not a variable list here; `glob A` is stated, where EC adds it).  In
  `pr_Game0_Game1`'s `seq`, `glob LRO, glob Log` is `LRO.m, Log.qs`.
* GAP 3: the restriction is `{-LRO, -Log, -Game1, -Game2, -OWr}`: EC's `{-LRO, -Log}`, and the
  section's local modules, which EC keeps apart from `A` by declaring them after it.
* GAP 4: `1: by sim` on the oracle's judgment is `equiv_proc; stmt_inline*; equiv_auto;
  auto_progress` (`sim` finds no equality set for the cloned oracle), and `OW_OWr`'s
  `by byequiv=> //=; sim` is the inverter's call by hand.
* GAP 5: `call (LRO_o_ll _); auto; apply: dptxt_ll` for the logged oracle's losslessness is
  `islossless` (applying `LRO_o_ll` does not unify through the clone's accessor).
* GAP 6: the pure goals after `auto=> />` are closed by hand where EC names the pieces with an
  intro pattern (`rename_i`, `rintro`), and EC's `smt(@FMap)` is `smt_close [FMap.mem_set]`.
* GAP 7: `rewrite (OW_OWr &m (I(A)))` needs `I(A)`'s restriction `{-OWr}` as an instance,
  stated by hand (`haveI : Module.Declared (Module.app I A) …`); EC checks it itself.
* GAP 8: `Reduction`'s `smt(…)` is `linarith` on the five lemmas (`smt_close` with lemmas
  applied to the section's hypotheses fails with an internal error); three lemmas need more
  than the default heartbeats.
* GAP 9 (blocked): the instance clones `ROM` a second time at the types of the clone inside
  `BR93` and relates the two clones' maps (`H.Lazy.LRO.m{1} = LRO.m{2}`): two clones of one
  theory with distinct module variables — the per-clone variables of
  `notes/SHA3/TacticReview.md` (last section, limit 4).
* `[Countable rand]` is an assumption EC does not state (the samplings into `rand`).
-/

set_option ec.strict true
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace GaudisCrypt.Examples.BR93

open GaudisCrypt GaudisCrypt.EC

/-- The abstract scenario of EC's `abstract theory BR93`. -/
class Params (ptxt rand pkey skey : outParam Type) where
  add : ptxt → ptxt → ptxt
  addA : ∀ p1 p2 p3, add (add p1 p2) p3 = add p1 (add p2 p3)
  addC : ∀ p1 p2, add p1 p2 = add p2 p1
  addKp : ∀ p1 p2, add (add p1 p1) p2 = p2
  dptxt : SubProbability ptxt
  dptxt_llfuuni : is_lossless dptxt ∧ is_full dptxt ∧ is_uniform dptxt
  drand : SubProbability rand
  drand_lluni : is_lossless drand ∧ is_uniform drand
  dkeys : SubProbability (pkey × skey)
  dkeys_llfuni : is_lossless dkeys ∧ is_funiform dkeys
  f : pkey → rand → rand
  fi : skey → rand → rand
  fK : ∀ pk sk x, (pk, sk) ∈ dkeys.support → fi sk (f pk x) = x

export Params (addA addC addKp dptxt dptxt_llfuuni drand drand_lluni dkeys dkeys_llfuni f fi fK)

/-- EC's `op (+^): ptxt -> ptxt -> ptxt`. -/
infixl:65 " +^ " => Params.add

variable {ptxt rand pkey skey : Type} [Inhabited ptxt] [Inhabited rand] [Inhabited pkey]
  [Inhabited skey] [Params ptxt rand pkey skey]

theorem addpK (p1 p2 : ptxt) : p1 +^ p2 +^ p2 = p1 := by
  -- EC: by rewrite addC -addA addC -addA addKp.
  rw [addC, ← addA, addC, ← addA, addKp]

theorem dptxt_ll : is_lossless (dptxt : SubProbability ptxt) := dptxt_llfuuni.1
theorem dptxt_uni : is_uniform (dptxt : SubProbability ptxt) := dptxt_llfuuni.2.2
theorem dptxt_fu : is_full (dptxt : SubProbability ptxt) := dptxt_llfuuni.2.1
theorem dptxt_funi : is_funiform (dptxt : SubProbability ptxt) :=
  is_full_funiform dptxt_fu dptxt_uni

theorem drand_ll : is_lossless (drand : SubProbability rand) := drand_lluni.1
theorem drand_uni : is_uniform (drand : SubProbability rand) := drand_lluni.2

theorem dkeys_ll : is_lossless (dkeys : SubProbability (pkey × skey)) := dkeys_llfuni.1
theorem dkeys_funi : is_funiform (dkeys : SubProbability (pkey × skey)) := dkeys_llfuni.2

-- EC's `islossless` closes the samplings by these (its hint database `random`)
attribute [ec_random] dptxt_ll drand_ll dkeys_ll

theorem fI (pk : pkey) (x y : rand) : (∃ sk : skey, (pk, sk) ∈ dkeys.support) →
    f pk x = f pk y → x = y := by
  -- EC: by move=> [sk] + fx_eq_fy - /fK ^ /(_ x) <- /(_ y) <-; congr.
  rintro ⟨sk, hsk⟩ fx_eq_fy
  rw [← fK pk sk x hsk, ← fK pk sk y hsk, fx_eq_fy]

-- (for the programs: equality tests on `ptxt`, `rand`, and the samplings into `rand`)
variable [DecidableEq ptxt] [DecidableEq rand] [Countable rand]

clone import GaudisCrypt.EC.ROM as H with
  type in_t <- rand, type out_t <- ptxt, type d_in_t <- Unit, type d_out_t <- Bool,
  op dout <- fun _ => dptxt

open H.Lazy

module BR93 using (H : Oracle) {
  proc keygen () : (pkey × skey) {
    var kp : pkey × skey;
    kp <$ dkeys;
    return $kp
  };
  proc enc (pk : pkey, m : ptxt) : (rand × ptxt) {
    var r : rand, h : ptxt;
    r <$ drand;
    h <- call H.o ($r);
    return (f $pk $r, $h +^ $m)
  };
  proc dec (sk : skey, c : rand × ptxt) : ptxt {
    var r : rand, h : ptxt, m : ptxt;
    r, m <- $c;
    r <- fi $sk $r;
    h <- call H.o ($r);
    return $h +^ $m
  };
}

/-! We can quickly prove it correct as a sanity check. -/

section Correctness

module Correctness {
  proc main (m : ptxt) : Bool {
    var pk : pkey, sk : skey, c : rand × ptxt, m' : ptxt;
    pk, sk <- call BR93(LRO).keygen ();
    c <- call BR93(LRO).enc ($pk, $m);
    m' <- call BR93(LRO).dec ($sk, $c);
    return decide ($m = $m')
  };
}

theorem BR93_correct (m : VariableAssignment) (m₀ : ptxt) :
    Pr[ Correctness.main (m₀) @ &m : §res ] = 1 := by
  -- EC: byphoare=> //; conseq (: _ ==> true) (: _ ==> res)=> //.
  --     (`proc` first: the two judgments are about the body)
  byphoare; phoare_proc; phoare_conseq (: _ ==> True) (: _ ==> _)
  · -- EC: + proc; inline *.
    hoare_inline*; stmt_split_params
    -- EC: rcondf 17.
    stmt_rcondf 17
    · -- EC: + auto=> /> &hr [pk sk] kp_in_dkeys r _ y _ /=.
      --       rewrite fK //; split=> [_ _ _|-> //].
      --       by rewrite mem_set.
      hoare_auto
      rintro σ m1 M ⟨rfl, -⟩ ⟨pk, sk⟩ kp_in_dkeys r _ y _ _ _
      simp only [ite_self, fK pk sk r kp_in_dkeys]
      by_cases h : M.dom r <;> simp [h, FMap.mem_set]
    -- EC: auto=> /> &hr [pk sk] kp_in_dkeys r _ y _ /=.
    --     rewrite fK //; split=> [_ y' _|].
    --     + by rewrite get_set_sameE -addA addKp.
    --     rewrite domE; case: (LRO.m{hr}.[r])=> [|p] //= _ _.
    --     by rewrite -addA addKp.
    hoare_auto
    rintro σ m1 M ⟨rfl, -⟩ ⟨pk, sk⟩ kp_in_dkeys r _ y _ _ _
    simp only [ite_self, fK pk sk r kp_in_dkeys, ← addA, addKp, decide_true]
  -- EC: by proc; inline *; auto=> />; rewrite dkeys_ll drand_ll dptxt_ll.
  phoare_inline*; phoare_auto
  exact fun _ _ _ _ =>
    ⟨dkeys_ll, fun _ _ => ⟨drand_ll, fun _ _ => ⟨dptxt_ll, fun _ _ => dptxt_ll⟩⟩⟩

end Correctness

/-! We use cloning to get definitions for OWTP security -/

clone import GaudisCrypt.EC.OW as OW_rand with
  type D <- rand, type R <- rand, type pkey <- pkey, type skey <- skey,
  op dkeys <- dkeys, op challenge <- fun _ => drand, op f <- f, op finv <- fi
  proof * by first
    | exact dkeys_ll
    | exact fun _ _ => drand_ll
    | exact fun _ _ => drand_uni
    | exact fun pk sk x h _ => fK pk sk x h
    | (intro pk sk y h hr hp
       obtain ⟨x, hx, rfl⟩ := hr hp
       rw [fK pk sk x h]; exact hx hp)
    | (intro pk sk x h hr
       obtain ⟨y, _, rfl⟩ := hr ⟨sk, h⟩
       rw [fK pk sk y h])

/-! But we can't do it (yet) for IND-CPA because of the random oracle.  Instead, we define CPA
for BR93 with that particular RO. -/

moduletype AdvProcs {
  proc a1 (p : pkey) -> (ptxt × ptxt);
  proc a2 (c : rand × ptxt) -> Bool;
}

/-- EC's `module type Adv (ARO : POracle) = { proc a1(p:pkey): (ptxt * ptxt)
proc a2(c:ctxt): bool }`. -/
abbrev Adv := POracle →ₘ AdvProcs

/-! We need to log the random oracle queries made to the adversary in order to express the
final theorem. -/

module_var Log.qs : List rand

module Log using (H : Oracle) : Oracle {
  proc init () : Unit {
    Log.qs <- [];
    _ <- call H.init ();
    return ()
  };
  proc o (x : rand) : ptxt {
    var r : ptxt;
    Log.qs <- $x :: $Log.qs;
    r <- call H.o ($x);
    return $r
  };
}

/-- `glob Log`: its list `Log.qs` (read off the code; for the footprint tactics). -/
@[fp_bound] theorem fvP_Log :
    FVP.fvP (Log (ptxt := ptxt) (rand := rand) (pkey := pkey) (skey := skey)) ≤
      (Log.qs (ptxt := ptxt) (rand := rand) (pkey := pkey) (skey := skey)).footprint := by
  fp_module Log.qs

module BR93_CPA using (A : Adv) {
  proc main () : Bool {
    var pk : pkey, sk : skey, m0 : ptxt, m1 : ptxt, c : rand × ptxt, b : Bool, b' : Bool;
    _ <- call Log(LRO).init ();
    pk, sk <- call BR93(LRO).keygen ();
    m0, m1 <- call A(Log(LRO)).a1 ($pk);
    b <$ dbool;
    c <- call BR93(LRO).enc ($pk, if $b then $m0 else $m1);
    b' <- call A(Log(LRO)).a2 ($c);
    return decide ($b' = $b)
  };
}

/-! We construct I as follows, using A.a1 and A.a2 as black boxes -/

module_var I.x : rand

module I using (A : Adv) : Inverter {
  proc invert (pk : pkey, y : rand) : rand {
    var m0 : ptxt, m1 : ptxt, h : ptxt, b : Bool;
    _ <- call Log(LRO).init ();
    m0, m1 <- call A(Log(LRO)).a1 ($pk);
    h <$ dptxt;
    b <- call A(Log(LRO)).a2 (($y, $h));
    I.x <- nth default $Log.qs (find (fun p => decide (f $pk p = $y)) $Log.qs);
    return $I.x
  };
}

/-! We now prove the result using a sequence of games -/

-- Step 1: replace RO call with random sampling
module_var Game1.r : rand

module Game1 using (A : Adv) {
  proc main () : Bool {
    var pk : pkey, sk : skey, m0 : ptxt, m1 : ptxt, c : rand × ptxt, b : Bool, b' : Bool,
      h : ptxt;
    _ <- call Log(LRO).init ();
    pk, sk <$ dkeys;
    m0, m1 <- call A(Log(LRO)).a1 ($pk);
    b <$ dbool;
    Game1.r <$ drand;
    h <$ dptxt;
    c <- (f $pk $Game1.r, $h +^ (if $b then $m0 else $m1));
    b' <- call A(Log(LRO)).a2 ($c);
    return decide ($b' = $b)
  };
}

-- Step 2: replace h ^ m with h in the challenge encryption
module_var Game2.r : rand

module Game2 using (A : Adv) {
  proc main () : Bool {
    var pk : pkey, sk : skey, m0 : ptxt, m1 : ptxt, c : rand × ptxt, b : Bool, b' : Bool,
      h : ptxt;
    _ <- call Log(LRO).init ();
    pk, sk <$ dkeys;
    m0, m1 <- call A(Log(LRO)).a1 ($pk);
    b <$ dbool;
    Game2.r <$ drand;
    h <$ dptxt;
    c <- (f $pk $Game2.r, $h);
    b' <- call A(Log(LRO)).a2 ($c);
    return decide ($b' = $b)
  };
}

-- Step 3: we need a version of the one-way game where the challenge is a global
module_var OWr.x : rand

module OWr using (I : Inverter) {
  proc main () : Bool {
    var x' : rand, pk : pkey, sk : skey;
    pk, sk <$ dkeys;
    OWr.x <$ drand;
    x' <- call I.invert ($pk, f $pk $OWr.x);
    return decide ($OWr.x = $x')
  };
}

section

-- All lemmas in this section hold for all (valid) CPA adversary A
-- (GAP 3: `Game1`, `Game2`, `OWr` are EC's local modules, declared after `A`)
declare module A <: Adv {-LRO, -Log, -Game1, -Game2, -OWr}

variable (A_a1_ll : ∀ (O <: POracle {-A}), islossless O.o → islossless A(O).a1)
  (A_a2_ll : ∀ (O <: POracle {-A}), islossless O.o → islossless A(O).a2)

set_option maxHeartbeats 4000000 in
-- (GAP 8: the script needs more than the default heartbeats)
include A_a1_ll A_a2_ll in
theorem pr_Game0_Game1 (m : VariableAssignment) :
    Pr[ BR93_CPA(A).main () @ &m : §res ] ≤
      Pr[ Game1(A).main () @ &m : §res ] +
        Pr[ Game1(A).main () @ &m : §Game1.r ∈ §Log.qs ] := by
  -- EC: byequiv=> //; proc.
  byequiv; equiv_proc
  -- EC: inline BR93(LRO).enc BR93(LRO).keygen.
  stmt_inline (BR93(LRO).enc) (BR93(LRO).keygen)
  stmt_split_params
  -- EC: seq  8  5: (   ={glob A, glob LRO, glob Log, pk, sk, b}
  --                 /\ pk0{1} = pk{2}
  --                 /\ m{1} = (b?m0:m1){2}
  --                 /\ r{1} = Game1.r{2}
  --                 /\ (forall x, x \in Log.qs{1} <=> x \in LRO.m{1})).
  equiv_seq 8 5 : (={glob A, LRO.m, Log.qs, pk, sk, b} ∧ §pk0{1} = §pk{2} ∧
    §m{1} = (if §b{2} then §m0{2} else §m1{2}) ∧ §r{1} = §Game1.r{2} ∧
    ∀ x, x ∈ §Log.qs{1} ↔ FMap.dom §LRO.m{1} x)
  · -- EC: + auto; call (:   ={glob Log, glob LRO}
    --                    /\ (forall x, x \in Log.qs{1} <=> x \in LRO.m{1})).
    equiv_auto
    equiv_call (_ : ={Log.qs, LRO.m} ∧ ∀ x, x ∈ §Log.qs{1} ↔ FMap.dom §LRO.m{1} x)
    · -- EC: + proc; inline LRO.o.
      --       by auto=> /> &2 log_is_dom y _; smt(@FMap).
      equiv_proc; stmt_inline*; equiv_auto; auto_progress
      smt_close [FMap.mem_set]
    -- EC: by inline *; auto=> /> _ _ x; rewrite mem_empty.
    stmt_inline*; equiv_auto; auto_progress
  -- EC: call (_: Game1.r \in Log.qs,
  --          eq_except (pred1 Game1.r{2}) LRO.m{1} LRO.m{2}).
  equiv_call (_ : §Game1.r ∈ §Log.qs, FMap.eq_except (pred1 §Game1.r{2}) §LRO.m{1} §LRO.m{2})
  -- EC: + exact/A_a2_ll.
  · exact A_a2_ll
  -- EC: + proc; inline LRO.o.
  --       auto=> /> &1 &2 _ m1_eqe_m2 yL y_in_dptxt; split. …
  · equiv_proc; stmt_inline*; equiv_auto; auto_progress
    all_goals
      simp only [FMap.eq_except, pred1, FMap.domE, List.mem_cons, not_or, FMap.get_setE] at *
    all_goals solve
      | simp_all
      | grind
  -- EC: + by move=> &2 _; proc; call (LRO_o_ll _); auto=> /=; apply: dptxt_ll.
  · islossless
  -- EC: + move=> _ /=; proc; inline *.
  --       conseq (: true ==> true: =1%r) (: Game1.r \in Log.qs ==> Game1.r \in Log.qs)=> //=.
  --       + by auto=> />.
  --       by auto=> />; exact/dptxt_ll.
  · phoare_proc; phoare_inline*; phoare_auto
    intro qs r x LRO_m hr
    exact ⟨dptxt_ll, fun v _ => by split_ifs <;> exact List.mem_cons_of_mem _ hr⟩
  · islossless
  -- EC: inline LRO.o; case: ((r \in LRO.m){1}).
  stmt_inline (LRO.o); equiv_case (FMap.dom §LRO.m{1} §r{1})
  · -- EC: + conseq (: _ ==> ={b} /\ Game1.r{2} \in Log.qs{2})=> //=.
    --       + by move=> /> &1 &2 _ _ rR _ _ _ _ _ h /h [] -> //.
    --       by auto=> /> &2 <- ->.
    equiv_conseq (: _ ==> ={b} ∧ §Game1.r{2} ∈ §Log.qs{2})
    · auto_progress
    equiv_auto; auto_progress
  -- EC: rcondt{1} 3; 1:by auto.
  stmt_rcondt{1} 3
  · hoare_auto
  -- EC: auto=> /> &2 log_is_dom r_notin_m y _; rewrite !get_set_sameE oget_some /=.
  --     split.
  --     + by move=> _; rewrite eq_exceptP /pred1=> x; rewrite get_setE eq_sym=> ->.
  --     by move=> _ rR aL mL aR qsR mR h /h [] ->.
  equiv_auto; auto_progress
  all_goals
    refine Or.inr ⟨by simp [oget], fun y hy => ?_, by simp_all⟩
    simp [FMap.get_setE, show y ≠ _ from hy]

set_option maxHeartbeats 4000000 in
-- (GAP 8: the script needs more than the default heartbeats)
theorem eq_Game1_Game2 :
    equiv[ Game1(A).main ~ Game2(A).main : ={glob A} ==>
      ={glob Log, res} ∧ §Game1.r{1} = §Game2.r{2} ] := by
  -- EC: proc.
  equiv_proc
  -- EC: call (: ={glob Log, glob LRO}); 1: by sim.
  equiv_call (_ : ={glob A, Log.qs, LRO.m})
  · equiv_proc; stmt_inline*; equiv_auto; auto_progress
  -- EC: wp; rnd (fun x=> x +^ (b?m0:m1){2}).
  stmt_wp
  equiv_rnd (fun x => x +^ (if §b{2} then §m0{2} else §m1{2}))
    (fun x => x +^ (if §b{2} then §m0{2} else §m1{2}))
  -- EC: auto; call (: ={glob Log, glob LRO}); 1: by sim.
  equiv_auto; equiv_call (_ : ={glob A, Log.qs, LRO.m})
  · equiv_proc; stmt_inline*; equiv_auto; auto_progress
  -- EC: inline *; auto=> /> _ _ rR b _ rL _; split=> [|_].
  --     + by move=> hR _; rewrite addpK.
  --     split=> [|_].
  --     + by move=> hR _; exact/dptxt_funi.
  --     by move=> hL _; rewrite dptxt_fu /= addpK.
  stmt_inline*; equiv_auto; auto_progress
  all_goals first
    | exact (addpK _ _).symm
    | exact congrArg ENNReal.toReal (dptxt_funi _ _)
    | exact absurd ‹_› ((SubProbability.mem_support_iff _ _).mp (dptxt_fu.mem_support _))

theorem pr_Game1_Game2 (m : VariableAssignment) :
    Pr[ Game1(A).main () @ &m : §res ] = Pr[ Game2(A).main () @ &m : §res ] := by
  -- EC: by byequiv eq_Game1_Game2.
  byequiv (eq_Game1_Game2 A)

theorem pr_bad_Game1_Game2 (m : VariableAssignment) :
    Pr[ Game1(A).main () @ &m : §Game1.r ∈ §Log.qs ] =
      Pr[ Game2(A).main () @ &m : §Game2.r ∈ §Log.qs ] := by
  -- EC: by byequiv eq_Game1_Game2.
  --     (the events agree: `={glob Log}` is `={Log.qs}`)
  byequiv (eq_Game1_Game2 A)
  auto_progress; glob_reads; simp_all

include A_a1_ll A_a2_ll in
theorem pr_Game2 (m : VariableAssignment) : Pr[ Game2(A).main () @ &m : §res ] = 1 / 2 := by
  -- EC: byphoare=> //=; proc.
  byphoare; phoare_proc
  -- EC: swap 4 4.
  stmt_swap 4 4
  -- EC: wp; rnd (pred1 b')=> //=.
  phoare_rnd (pred1 §b')
  -- EC: inline *; call (_: true).
  --     + exact A_a2_ll. (* adversary *)
  --     + by proc; call (LRO_o_ll _); auto=> /=; apply: dptxt_ll. (* oracle *)
  phoare_inline*; phoare_call (@A_a2_ll _ ?_ ?_)
  · islossless
  -- EC: auto; call (_: true).
  --     + exact A_a1_ll. (* adversary *)
  --     + by proc; call (LRO_o_ll _); auto=> /=; apply: dptxt_ll. (* oracle *)
  phoare_auto; phoare_call (@A_a1_ll _ ?_ ?_)
  · islossless
  -- EC: auto=> />; rewrite dkeys_ll drand_ll dptxt_ll /predT /=.
  --     by move=> _ _ _ _ _ _ r; rewrite dbool1E.
  phoare_auto
  smt_close [dkeys_ll, drand_ll, dptxt_ll, mu_pred1, dbool1E_mu1, pred1E]

theorem OW_OWr (m : VariableAssignment) : ∀ (I <: Inverter {-OWr}),
    Pr[ OW(I).main () @ &m : §res ] = Pr[ OWr(I).main () @ &m : §res ] := by
  -- EC: by byequiv=> //=; sim.
  --     (`sim` would keep all globals equal, and `OWr.x` is written on the right only: the
  --     inverter's call by hand)
  intro I _; byequiv; equiv_proc
  equiv_call (_ : True); equiv_auto; auto_progress

set_option maxHeartbeats 2000000 in
-- (GAP 8: the script needs more than the default heartbeats)
theorem pr_Game2_OW (m : VariableAssignment) :
    Pr[ Game2(A).main () @ &m : §Game2.r ∈ §Log.qs ] ≤
      Pr[ OW(I(A)).main () @ &m : §res ] := by
  -- EC: rewrite (OW_OWr &m (I(A))). (* Note: we proved it forall (abstract) I *)
  --     (EC checks `I(A)` against `{-OWr}` itself)
  haveI : Module.Declared (Module.app I A) OWr.x.footprint := ⟨by fp_finite, by fp_disjoint⟩
  rw [OW_OWr m (Module.app I A)]
  -- EC: byequiv => //=; proc; inline *; wp.
  byequiv; equiv_proc; stmt_inline*; stmt_wp
  -- EC: conseq (_ : _ ==> support dkeys (pk0{2}, sk{2}) /\ Game2.r{1} = OWr.x{2} /\
  --       Log.qs{1} = Log.qs{2} /\ y{2} = f pk0{2} Game2.r{1}).
  equiv_conseq (: _ ==> (§pk0{2}, §sk{2}) ∈ dkeys.support ∧ §Game2.r{1} = §OWr.x{2} ∧
    §Log.qs{1} = §Log.qs{2} ∧ §y{2} = f §pk0{2} §Game2.r{1})
  -- EC: + move=> /> qs x pk sk vk x_in_qs; pose P := fun p => f _ p = _.
  --       have h := nth_find witness P qs _.
  --       + by rewrite hasP; exists x.
  --       apply/(fI pk).
  --       + by exists sk.
  --       by rewrite h.
  · auto_progress
    rename_i x_in_qs _ _ _ vk _ hr _ _ _ hy
    have h := nth_find default (fun p => decide (f _ p = _)) _
      ⟨_, x_in_qs, decide_eq_true hy.symm⟩
    rw [← hr]
    exact (fI _ _ _ ⟨_, vk⟩ ((of_decide_eq_true h).trans hy)).symm
  -- EC: call (: ={glob Log, glob LRO}); 1: by sim.
  equiv_call (_ : ={glob A, Log.qs, LRO.m})
  · equiv_proc; stmt_inline*; equiv_auto; auto_progress
  -- EC: swap{1} 6 -2.
  stmt_swap{1} 6 -2
  -- EC: auto; call (: ={glob Log, glob LRO}); 1: by sim.
  equiv_auto; equiv_call (_ : ={glob A, Log.qs, LRO.m})
  · equiv_proc; stmt_inline*; equiv_auto; auto_progress
  -- EC: by auto=> /> [pk sk] ->.
  equiv_auto; auto_progress
  exact (is_lossless_iff_expected _).mp dbool_ll

include A_a1_ll A_a2_ll in
theorem Reduction (m : VariableAssignment) :
    Pr[ BR93_CPA(A).main () @ &m : §res ] - 1 / 2 ≤ Pr[ OW(I(A)).main () @ &m : §res ] := by
  -- EC: smt(pr_Game0_Game1 pr_Game1_Game2 pr_bad_Game1_Game2 pr_Game2 pr_Game2_OW).
  -- GAP 8: `smt_close [pr_Game0_Game1 A A_a1_ll A_a2_ll m, …]` fails (unknown free variable)
  have h0 := pr_Game0_Game1 A A_a1_ll A_a2_ll m
  have h1 := pr_Game1_Game2 A m
  have h2 := pr_bad_Game1_Game2 A m
  have h3 := pr_Game2 A A_a1_ll A_a2_ll m
  have h4 := pr_Game2_OW A m
  linarith

end

end GaudisCrypt.Examples.BR93
