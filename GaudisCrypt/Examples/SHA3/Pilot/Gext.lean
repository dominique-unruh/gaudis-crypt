import GaudisCrypt.Examples.SHA3.Pilot.Gcol
import GaudisCrypt.Examples.SHA3.SmartCounter.Gext
import GaudisCrypt.Logic.FelInner
import GaudisCrypt.Logic.CallSpec

/-!
# The extension event (EasyCrypt `proof/smart_counter/Gext.eca`) — EC-fidelity port

`Real_G2` bounds the real game by the eager `G2` plus the switching bound and the probabilities of
collisions (`Pr_G1col`) and extensions (`Pr_ext`, through the resampling game `Gext`).  Over the
old port's declarations of `G2`, `Eager`, `RRO` (`SmartCounter/Gext.lean`), as `Pilot/Handle.lean`
and `Pilot/Gcol.lean`.

Translation:
* the local modules `ReSample`, `Gext` are declared here as in EC, `ReSample`'s variable `count` a
  `global_var` (`ReSample.count`); `Gext.resample`, `Gext.M`, `Gext.S` are modules of their own
  (EC's inner modules), `Gext D` the game with `D` a Lean parameter;
* `declare module D <: DISTINGUISHER {-C, -PF, -G1, -G2, -Perm, -ROhandle.RO.m, -Redo, -ReSample.count}`:
  EC's freshness of the local module for `D` in `D`'s restriction.
-/

-- EasyCrypt names the local module after the file (`Gext.Gext`); kept (exception E1)
set_option linter.dupNamespace false

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: as Gcol's: our abstract `call (_: ={…} /\ inv)` keeps `={glob D}` in the oracles'
  judgments: `glob D` added to EC's intermediate conditions.
* GAP 2: as Gcol's: inline by name vs the old declarations' accessors: by index.
* GAP 3: `sp` through an inlined call (`G1_G2`'s `M.f`): the start state as nested existentials
  with whole-state equations through the inliner's renaming (`ProgramState.mapLocal`); the
  closers do not use them (EC's `sp` keeps reads, `exists` only for overwritten values).
* EC's `x` (the wrapper `DRestr`'s parameter) is not a program variable after our `sp`
  (it is substituted): `x{1} = x0{1}` dropped, `x` read as `x0`.
-/

namespace GaudisCrypt.SHA3.Pilot.Gext

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle
open GaudisCrypt.SHA3.Gext (bad_ext hinvc HFRO G2 G2.M G2.S Eager Eager.main1 Eager.main2 RRO
  RRO.resample inv_ext inv_ext1 inv_lt inv_le)

variable [SLCommon.Params]

/-- EC's `state` (`SLCommonCore`'s, named here: a root `state` exists). -/
abbrev state := GaudisCrypt.SHA3.SLCommon.state

/-! ## The first section: `G1` and the lazy `G2` -/

section

declare module D <: DISTINGUISHER {-G1, -G2, -FRO.m, -C.c, -C.queries}

set_option maxHeartbeats 8000000 in
-- one declaration: EC's call over three oracles, the eleven-variable invariant
/-- EC's `equiv G1_G2 : G1(DRestr(D)).main ~ Eager(G2(DRestr(D))).main1 : ={glob D} ==> ={res} /\
inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2}`. -/
theorem G1_G2 : equiv[ G1(DRestr(D)).main ~ Eager(G2(DRestr(D))).main1 :
    ={glob D} ==> ={res} ∧ inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ] := by
  -- EC: proc;inline{2} FRO.init G2(D, FRO).distinguish;wp.
  --     inline*;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: call (_: ={F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.paths,G1.chandle,FRO.m,C.queries,C.c} /\
  --          inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2} /\
  --          (forall h, h \in FRO.m => h < G1.chandle){1}).
  equiv_call (_ : ={F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.paths, G1.chandle, FRO.m, C.queries,
      C.c} ∧ inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
      ∀ h, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
  -- EC: + proc.
  --       sp;if;auto;inline G1(DRestr(D)).S.f G2(DRestr(D), FRO).S.f;sp;wp.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    --     (GAP 2: the only call on each side, by index)
    · stmt_inline 0; stmt_sp; stmt_wp
      -- EC: if=>//;last by auto.
      stmt_if
      · auto_close
      on_goals -1 => (equiv_auto; auto_close)
      -- EC: seq 2 2: (={F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.paths,G1.chandle,FRO.m,x,x0,y0,
      --                 C.queries,C.c} /\
      --               inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2} /\ x{1} = x0{1} /\
      --               (forall h, h \in FRO.m => h < G1.chandle){1} /\
      --               x0{1} \notin G1.m{1}).
      --     + by if=>//;auto;call (_: ={F.RO.m});[sim |auto].
      --     (GAP 1: `glob D` added; `x`, the wrapper's parameter, is not a variable after our
      --     `sp`: `x{1} = x0{1}` dropped)
      equiv_seq 2 2 : (={glob D, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.paths, G1.chandle, FRO.m,
          x0, y0, C.queries, C.c} ∧
          inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
          (∀ h, FMap.dom §FRO.m{1} h → h < §G1.chandle{1}) ∧ ¬ FMap.dom §G1.m{1} §x0{1})
      · stmt_if
        · auto_close
        · equiv_auto; equiv_call (_ : ={F.RO.m}); equiv_auto
        · equiv_auto
      -- EC: seq 3 5:
      --       (={F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.paths,G1.chandle,FRO.m,hx2,x,x0,y0,hx2,C.queries,
      --          C.c} /\
      --        t{2} = (in_dom_with FRO.m (oget G1.mh.[(x.`1, hx2)]).`2 Unknown){1} /\ x{1} = x0{1} /\
      --        (G1.bext{1} => (G1.bext{2} \/ (rng FRO.m (x.`2, Unknown)){2} \/
      --                        inv_ext G1.m{2} G1.mi{2} FRO.m{2})) /\
      --       (forall h, h \in FRO.m => h < G1.chandle){1} /\
      --       x0{1} \notin G1.m{1}).
      equiv_seq 3 5 : (={glob D, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.paths, G1.chandle, FRO.m,
          hx2, x0, y0, C.queries, C.c} ∧
          §t{2} = decide (FMap.in_dom_with §FRO.m{1}
            (oget (FMap.get §G1.mh{1} ((§x0{1}).1, §hx2{1}))).2 Unknown) ∧
          (§G1.bext{1} → §G1.bext{2} ∨ FMap.rng §FRO.m{2} ((§x0{2}).2, Unknown) ∨
            inv_ext §G1.m{2} §G1.mi{2} §FRO.m{2}) ∧
          (∀ h, FMap.dom §FRO.m{1} h → h < §G1.chandle{1}) ∧ ¬ FMap.dom §G1.m{1} §x0{1})
      -- EC: + inline *; auto=> |> &ml &mr Hi Hhand.
      --       rewrite -dom_restr rng_restr !rngE /= negb_exists=> /= |> x_notin_G1.
      --       … (the cases of `rng FRO.m (x0.`2, Known)`)
      · stmt_inline*; equiv_auto; auto_prep
        simp only [GaudisCrypt.SHA3.Gext.rng_restr] at *
        split_ifs
        · exact ⟨⟨rfl, trivial, trivial, rfl⟩, decide_eq_decide.mpr Iff.rfl,
            GaudisCrypt.SHA3.Gext.bext_pre ‹_› (fun _ _ h => h), ‹_›, ‹_›⟩
        · exact ⟨⟨rfl, trivial, trivial, rfl⟩, decide_eq_decide.mpr Iff.rfl,
            GaudisCrypt.SHA3.Gext.bext_pre ‹_› (GaudisCrypt.SHA3.Gext.get_set_fresh ‹_› _),
            GaudisCrypt.SHA3.Gext.fresh_set ‹_› _, ‹_›⟩
      -- EC: seq 1 1: (={x0,y0,x,F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.paths,G1.chandle,FRO.m,
      --                 C.queries,C.c} /\
      --               inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2} /\ x{1} = x0{1} /\
      --               forall (h : handle), h \in FRO.m{1} => h < G1.chandle{1});2:by auto.
      equiv_seq 1 1 : (={glob D, x0, y0, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.paths, G1.chandle,
          FRO.m, C.queries, C.c} ∧
          inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
          ∀ h, FMap.dom §FRO.m{1} h → h < §G1.chandle{1})
      on_goals 2 => (equiv_auto; auto_close)
      -- EC: if=>//.
      stmt_if
      · auto_close
      -- EC: + inline *;rcondt{2} 4.
      --       + by move=> &m;auto;rewrite /in_dom_with.
      · stmt_inline*; stmt_rcondt{2} 4
        · hoare_auto; auto_prep
          exact ‹FMap.in_dom_with _ _ _›.1
        -- EC: auto;progress.
        --     + rewrite /inv_ext1=>/H{H}[->//|[|[[x1 x2] h [Hx Hh]]]]. … (the witness at `hy2`
        --       hits `G1.bext`'s update, any other stays)
        --     by move:H5 H2;rewrite /in_dom_with mem_set /#.
        --     (the old port's `inv_ext1_hit`, `cdistr_expected_one`)
        equiv_auto; auto_prep
        refine ⟨GaudisCrypt.SHA3.Gext.cdistr_expected_one, fun a _ => ⟨rfl,
          GaudisCrypt.SHA3.Gext.inv_ext1_hit ‹_› (by simp [FMap.fdom_set]) (fun z hz => ?_) _,
          fun h hd => ?_⟩⟩
        · simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
          tauto
        · rcases (FMap.mem_set _ _ _ _).mp hd with hd | rfl
          · exact ‹∀ (h : handle), (FRO.m.get _).dom h → h < _› h hd
          · exact ‹∀ (h : handle), (FRO.m.get _).dom h → h < _› _ ‹FMap.in_dom_with _ _ _›.1
      -- EC: inline *;auto;progress;last by move:H3;rewrite mem_set /#.
      --     rewrite /inv_ext1=> /H [->//|[|[x' h [Hx Hh]]]]. …
      --     (the old port's `inv_ext1_of_weak`, `get_set_fresh`, `fresh_set`)
      · stmt_inline*; equiv_auto; auto_prep
        refine ⟨rfl, GaudisCrypt.SHA3.Gext.inv_ext1_of_weak ‹_› (by simp [FMap.fdom_set])
          (fun z hz => ?_) (GaudisCrypt.SHA3.Gext.get_set_fresh ‹_› _),
          GaudisCrypt.SHA3.Gext.fresh_set ‹_› _⟩
        simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
        tauto
    · equiv_auto
  -- EC: + proc;sp;if;auto;inline G1(DRestr(D)).S.fi G2(DRestr(D), FRO).S.fi;sp;wp.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    --     (GAP 2: the only call on each side, by index)
    · stmt_inline 0; stmt_sp; stmt_wp
      -- EC: if=>//;last by auto.
      stmt_if
      · auto_close
      on_goals -1 => (equiv_auto; auto_close)
      -- EC: seq 6 8:
      --       (={F.RO.m,G1.m,G1.mi,G1.mh,G1.mhi,G1.paths,G1.chandle,FRO.m,hx2,x,x0,y0,hx2,C.queries,
      --          C.c} /\
      --        t{2} = (in_dom_with FRO.m (oget G1.mhi.[(x.`1, hx2)]).`2 Unknown){1} /\ x{1} = x0{1} /\
      --        (G1.bext{1} => (G1.bext{2} \/ (rng FRO.m (x.`2, Unknown)){2} \/
      --                         inv_ext G1.m{2} G1.mi{2} FRO.m{2})) /\
      --       (forall h, h \in FRO.m => h < G1.chandle){1} /\
      --       x{1} \notin G1.mi{1}).
      --     (GAP 1: `glob D` added; `x`, the wrapper's parameter: `x0`)
      equiv_seq 6 8 : (={glob D, F.RO.m, G1.m, G1.mi, G1.mh, G1.mhi, G1.paths, G1.chandle, FRO.m,
          hx2, x0, y0, C.queries, C.c} ∧
          §t{2} = decide (FMap.in_dom_with §FRO.m{1}
            (oget (FMap.get §G1.mhi{1} ((§x0{1}).1, §hx2{1}))).2 Unknown) ∧
          (§G1.bext{1} → §G1.bext{2} ∨ FMap.rng §FRO.m{2} ((§x0{2}).2, Unknown) ∨
            inv_ext §G1.m{2} §G1.mi{2} §FRO.m{2}) ∧
          (∀ h, FMap.dom §FRO.m{1} h → h < §G1.chandle{1}) ∧ ¬ FMap.dom §G1.mi{1} §x0{1})
      -- EC: + inline *; auto=> |> &ml &mr Hi Hhand.
      --       rewrite -dom_restr rng_restr !rngE /= negb_exists=> /= |> c_le_msize x_notin_G1.
      --       … (the cases of `rng FRO.m (x.`2, Known)`)
      · stmt_inline*; equiv_auto; auto_prep
        simp only [GaudisCrypt.SHA3.Gext.rng_restr] at *
        split_ifs
        · exact ⟨⟨rfl, trivial, trivial, rfl⟩, decide_eq_decide.mpr Iff.rfl,
            GaudisCrypt.SHA3.Gext.bext_pre ‹_› (fun _ _ h => h), ‹_›, ‹_›⟩
        · exact ⟨⟨rfl, trivial, trivial, rfl⟩, decide_eq_decide.mpr Iff.rfl,
            GaudisCrypt.SHA3.Gext.bext_pre ‹_› (GaudisCrypt.SHA3.Gext.get_set_fresh ‹_› _),
            GaudisCrypt.SHA3.Gext.fresh_set ‹_› _, ‹_›⟩
      -- EC: if=>//.
      stmt_if
      · auto_close
      -- EC: + inline *;rcondt{2} 4.
      --       + by move=> &m;auto;rewrite /in_dom_with.
      · stmt_inline*; stmt_rcondt{2} 4
        · hoare_auto; auto_prep
          exact ‹FMap.in_dom_with _ _ _›.1
        -- EC: auto;progress.
        --     + rewrite /inv_ext1=>/H{H}[->//|[|[[x1 x2] h [Hx Hh]]]]. …
        --     by move:H5 H1;rewrite /in_dom_with mem_set /#.
        equiv_auto; auto_prep
        refine ⟨GaudisCrypt.SHA3.Gext.cdistr_expected_one, fun a _ => ⟨rfl,
          GaudisCrypt.SHA3.Gext.inv_ext1_hit ‹_› (by simp [FMap.fdom_set]) (fun z hz => ?_) _,
          fun h hd => ?_⟩⟩
        · simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
          tauto
        · rcases (FMap.mem_set _ _ _ _).mp hd with hd | rfl
          · exact ‹∀ (h : handle), (FRO.m.get _).dom h → h < _› h hd
          · exact ‹∀ (h : handle), (FRO.m.get _).dom h → h < _› _ ‹FMap.in_dom_with _ _ _›.1
      -- EC: inline *;auto;progress;last by move:H3;rewrite mem_set /#.
      --     rewrite /inv_ext1=> /H [->//|[|[x' h [Hx Hh]]]]. …
      · stmt_inline*; equiv_auto; auto_prep
        refine ⟨rfl, GaudisCrypt.SHA3.Gext.inv_ext1_of_weak ‹_› (by simp [FMap.fdom_set])
          (fun z hz => ?_) (GaudisCrypt.SHA3.Gext.get_set_fresh ‹_› _),
          GaudisCrypt.SHA3.Gext.fresh_set ‹_› _⟩
        simp only [FMap.fdom_set, Finset.mem_union, Finset.mem_insert] at hz ⊢
        tauto
    · equiv_auto
  -- EC: + proc;sp;if;auto;sp;if;auto;sp.
  --       inline G1(DRestr(D)).M.f G2(DRestr(D), FRO).M.f;sp;wp.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    --     (EC's third `sp` has nothing to do here)
    --     (GAP 2: the only call on each side, by index)
    stmt_inline 0; stmt_sp; stmt_wp
    -- EC: conseq (_: ={sa,G1.mh,G1.mhi,F.RO.m, G1.chandle, FRO.m,C.queries,C.c} /\
    --                inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2} /\
    --                forall (h0 : handle), h0 \in FRO.m{1} => h0 < G1.chandle{1})=>//.
    --     (GAP 1: `glob D` added)
    equiv_conseq (: _ ==> ={glob D, sa, G1.mh, G1.mhi, F.RO.m, G1.chandle, FRO.m, C.queries, C.c} ∧
        inv_ext1 §G1.bext{1} §G1.bext{2} §G1.m{2} §G1.mi{2} §FRO.m{2} ∧
        ∀ h0, FMap.dom §FRO.m{1} h0 → h0 < §G1.chandle{1})
    --     (GAP 3: `conseq`'s frame goal: our `sp`s through the inlined call leave the start state
    --     as nested existentials with whole-state equations through the inliner's renaming
    --     (`ProgramState.mapLocal`), which the closers do not use; EC's `sp` keeps reads)
    case post => sorry
    -- EC: sp;call (_: ={F.RO.m});1:by sim.
    --     while (={sa,G1.mh,G1.mhi,F.RO.m,G1.chandle,FRO.m,i,h,sa,p,C.queries,counter,bs} /\
    --            inv_ext1 G1.bext{1} G1.bext{2} G1.m{2} G1.mi{2} FRO.m{2} /\ p{2} = bs{2} /\
    --            forall (h0 : handle), h0 \in FRO.m{1} => h0 < G1.chandle{1})=>//.
    --     if=>//;inline *;1:by auto.
    --     if;1,3:auto;progress.
    --     rcondt{2} 3;1:by auto=>/#.
    --     auto;progress. …
    sorry
  -- EC: inline *;auto;progress.
  --     smt(mem_set mem_empty).
  · equiv_auto; auto_prep
    refine ⟨⟨rfl, fun h => absurd h Bool.false_ne_true, fun h hd => ?_⟩, ?_⟩
    · rcases (FMap.mem_set _ _ _ _).mp hd with hd | rfl
      · exact absurd hd (FMap.mem_empty _)
      · exact (by decide : (0 : ℤ) < 1)
    · auto_close

end

/-! ## The section `EXT` -/

/-- EC's `ReSample.count`. -/
global_var ReSample.count : ℤ

module ReSample {
  proc f (h : handle) : Unit {
    var c : capacity;
    c <$ cdistr;
    if (decide (((FMap.fdom ($G1.m : smap)).card : ℤ) ≤ max_size ∧
        ((FMap.fdom ($G1.mi : smap)).card : ℤ) ≤ max_size ∧ $ReSample.count < max_size)) {
      G1.bext <- $G1.bext || decide ($c ∈ Finset.image Prod.snd
        (FMap.fdom ($G1.m : smap) ∪ FMap.fdom ($G1.mi : smap)));
      FRO.m <- FMap.set $FRO.m $h ($c, Unknown);
      ReSample.count <- $ReSample.count + 1;
    }
    return ()
  };
  proc f1 (x : capacity, h : handle) : Unit {
    var c : capacity;
    c <$ cdistr;
    if (decide (((FMap.fdom ($G1.m : smap)).card : ℤ) < max_size ∧
        ((FMap.fdom ($G1.mi : smap)).card : ℤ) < max_size ∧ $ReSample.count < max_size)) {
      G1.bext <- $G1.bext || decide ($c ∈ Finset.image Prod.snd
        (FMap.fdom ($G1.m : smap) ∪ FMap.fdom ($G1.mi : smap)) ∪ fset1 $x);
      FRO.m <- FMap.set $FRO.m $h ($c, Unknown);
      ReSample.count <- $ReSample.count + 1;
    }
    return ()
  };
}

-- EC's `Gext.resample`
module Gext.resample {
  proc resample () : Unit {
    _ <- call (Module.app (IterProc.Iter handle)
        (IterProc.Orcl.mk handle { f := ReSample.f }))
      ((FMap.fdom (FMap.restr Unknown ($FRO.m : FMap handle (capacity × flag)))).toList);
    return ()
  };
}

-- EC's `Gext.M`
module Gext.M : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, sa' : block, h : handle, i : ℤ, counter : ℤ;
    h <- 0;
    i <- 0;
    counter <- 0;
    sa <- b0;
    while ($i < size $p) {
      if (decide (FMap.dom ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h))) {
        sa, h <- oget (FMap.get ($G1.mh : hsmap) ($sa +^ nth default $p $i, $h));
      } else {
        if (decide ($counter < size $p - «prefix» $p (get_max_prefix $p
            (elems (FMap.fdom ($C.queries : FMap (List block) block)))))) {
          _ <- call (PROM.FullRO.FRO_T.sample handle capacity RRO) ($G1.chandle);
          sa' <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (take ($i + 1) $p);
          sa <- $sa +^ nth default $p $i;
          G1.mh <- FMap.set $G1.mh ($sa, $h) ($sa', $G1.chandle);
          G1.mhi <- FMap.set $G1.mhi ($sa', $G1.chandle) ($sa, $h);
          sa, h <- ($sa', $G1.chandle);
          G1.chandle <- $G1.chandle + 1;
          counter <- $counter + 1;
        }
      }
      i <- $i + 1;
    }
    sa <- call (PROM.FullRO.ROmap.get (List block) block F.RO) ($p);
    return $sa
  };
}

-- EC's `Gext.S`
module Gext.S : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity, hy2 : handle,
      hx2 : handle, handles_ : FMap handle capacity, t : Bool;
    if (!(decide (FMap.dom ($G1.m : smap) $x))) {
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (rcons $p ($v +^ ($x).1));
      } else {
        y1 <$ bdistr;
      }
      y2 <$ cdistr;
      y <- ($y1, $y2);
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      if (!(decide (FMap.rng $handles_ ($x).2))) {
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($G1.chandle, ($x).2);
        G1.chandle <- $G1.chandle + 1;
      }
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      hx2 <- oget (hinvc $handles_ ($x).2);
      t <- call (PROM.FullRO.FRO_T.queried handle capacity RRO)
        ((oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2, Unknown);
      if (decide (FMap.dom ($G1.mh : hsmap) (($x).1, $hx2)) && $t) {
        hy2 <- (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2;
        _ <- call ReSample.f1 (($x).2, $hy2);
        y2 <- call (PROM.FullRO.FRO_T.get handle capacity ROhandle.FRO) ($hy2);
        y <- (($y).1, $y2);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mi <- FMap.set $G1.mi $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($hy2, ($y).2);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mh <- FMap.set $G1.mh (($x).1, $hx2) (($y).1, $hy2);
        G1.mi <- FMap.set $G1.mi $y $x;
        G1.mhi <- FMap.set $G1.mhi (($y).1, $hy2) (($x).1, $hx2);
      }
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        G1.paths <- FMap.set $G1.paths ($y).2 (rcons $p ($v +^ ($x).1), ($y).1);
      }
    } else {
      y <- oget (FMap.get ($G1.m : smap) $x);
    }
    return $y
  };
  proc fi (x : state) : state {
    var y : state, y1 : block, y2 : capacity, hx2 : handle, hy2 : handle,
      handles_ : FMap handle capacity, t : Bool;
    if (!(decide (FMap.dom ($G1.mi : smap) $x))) {
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      if (!(decide (FMap.rng $handles_ ($x).2))) {
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($G1.chandle, ($x).2);
        G1.chandle <- $G1.chandle + 1;
      }
      handles_ <- call (PROM.FullRO.FRO_T.allKnown handle capacity RRO) ();
      hx2 <- oget (hinvc $handles_ ($x).2);
      y1 <$ bdistr;
      y2 <$ cdistr;
      y <- ($y1, $y2);
      t <- call (PROM.FullRO.FRO_T.queried handle capacity RRO)
        ((oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2))).2, Unknown);
      if (decide (FMap.dom ($G1.mhi : hsmap) (($x).1, $hx2)) && $t) {
        y1, hy2 <- oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2));
        _ <- call ReSample.f1 (($x).2, $hy2);
        y2 <- call (PROM.FullRO.FRO_T.get handle capacity ROhandle.FRO) ($hy2);
        y <- (($y).1, $y2);
        G1.mi <- FMap.set $G1.mi $x $y;
        G1.m <- FMap.set $G1.m $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) ($hy2, ($y).2);
        G1.mi <- FMap.set $G1.mi $x $y;
        G1.mhi <- FMap.set $G1.mhi (($x).1, $hx2) (($y).1, $hy2);
        G1.m <- FMap.set $G1.m $y $x;
        G1.mh <- FMap.set $G1.mh (($y).1, $hy2) (($x).1, $hx2);
      }
    } else {
      y <- oget (FMap.get ($G1.mi : smap) $x);
    }
    return $y
  };
}

-- EC's `Gext.distinguish`, with `D` a Lean parameter (on purpose: `Gext D` is the game)
set_option linter.gaudisCrypt.using false in
module Gext (D : DISTINGUISHER) {
  proc distinguish () : Bool {
    var b : Bool;
    C.c <- 0;
    F.RO.m <- (FMap.empty : FMap (List block) block);
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    G1.mh <- (FMap.empty : hsmap);
    G1.mhi <- (FMap.empty : hsmap);
    G1.bext <- false;
    ReSample.count <- 0;
    FRO.m <- (FMap.empty : FMap handle (capacity × flag));
    -- the empty path is initially known by the adversary to lead to capacity 0^c
    _ <- call (PROM.FullRO.FRO_T.set handle capacity RRO) (0, c0);
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    G1.chandle <- 1;
    b <- call (Module.app (DRestr D) (Module.pair Gext.M Gext.S)) ();
    _ <- call Gext.resample ();
    return $b
  };
}


section EXT

declare module D <: DISTINGUISHER {-C.c, -C.queries, -PF, -G1, -G2, -Perm, -ROhandle.RO.m, -Redo,
  -ReSample.count}

/-- EC's `case (l)=>//=; smt w=List.size_ge0`: a list that is not empty has a positive size. -/
theorem size_pos_of_isEmpty {α : Type} {l : List α} (h : l.isEmpty = false) : 0 < size l := by
  cases l with
  | nil => simp at h
  | cons a t => simp only [size, List.length_cons]; omega

/-- EC's closer of the resampling loops' body in `EG2_Gext` (`case(l{mr})=>[//|h1 l1/=Hle Hext c
?/=];split. + smt w=(drop0 size_ge0). rewrite drop0=>-[H|[x h][#]];1:by rewrite Hext // H.
rewrite get_setE;case (h=h1)=> [/=->Hin->_ | Hneq ???]. + by right;apply (mem_image snd _ x).
by rewrite Hext 2://;right;exists x h;rewrite Hneq.`): one handle `head l` resampled. -/
theorem resample_step {b1 b2 : Bool} {m mi : smap} {F : handles} {l : List handle} {c : capacity}
    {count : ℤ} (hl : l.isEmpty = false) (hcount : count + size l ≤ max_size)
    (hext : (b1 = true ∨ ∃ (x : state) (h : handle), x ∈ FMap.fdom m ∪ FMap.fdom mi ∧
      FMap.get F h = some (x.2, Unknown) ∧ h ∉ l) → b2 = true) :
    count + 1 + size (drop 1 l) ≤ max_size ∧
      ((b1 = true ∨ ∃ (x : state) (h : handle), x ∈ FMap.fdom m ∪ FMap.fdom mi ∧
        FMap.get (FMap.set F (head default l) (c, Unknown)) h = some (x.2, Unknown) ∧
          h ∉ drop 1 l) →
        (b2 || decide (c ∈ Finset.image Prod.snd (FMap.fdom m ∪ FMap.fdom mi))) = true) := by
  cases l with
  | nil => simp at hl
  | cons h1 l1 =>
    simp only [drop, head, List.headD_cons, size, List.length_cons] at hcount ⊢
    refine ⟨by simp; omega, ?_⟩
    rintro (H | ⟨x, h, hx, hh, hn⟩)
    · simp [hext (Or.inl H)]
    · by_cases he : h = h1
      · subst he
        rw [FMap.get_set_sameE] at hh
        cases hh
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      · rw [FMap.get_set_neqE _ _ _ _ he] at hh
        have : h ∉ h1 :: l1 := by
          simp only [List.mem_cons, not_or]; exact ⟨he, by simpa using hn⟩
        simp [hext (Or.inr ⟨x, h, hx, hh, this⟩)]

set_option maxHeartbeats 4000000 in
-- the oracles' syntactic check (`exp_decr`) over `Gext`'s oracles and the resampling
/-- EC's `local lemma Pr_ext &m : Pr[Gext.distinguish()@&m : G1.bext /\ ReSample.count <= max_size]
<= max_size%r * ((2*max_size)%r / (2^c)%r)`. -/
theorem Pr_ext (m : VariableAssignment) :
    Pr[ Gext(D).distinguish () @ &m : §G1.bext ∧ §ReSample.count ≤ max_size ] ≤
      (max_size : ℝ) * (((2 * max_size : ℤ) : ℝ) / ((2 ^ c.toNat : ℤ) : ℝ)) := by
  -- EC: fel 8 ReSample.count (fun x=> (2*max_size)%r / (2^c)%r)
  --       max_size G1.bext
  --       [ReSample.f :
  --         (card (fdom G1.m) <= max_size /\ card (fdom G1.mi) <= max_size /\ ReSample.count < max_size);
  --        ReSample.f1 :
  --         (card (fdom G1.m) < max_size /\ card (fdom G1.mi) < max_size /\ ReSample.count < max_size)
  --       ]=> //; 2:by auto.
  --     (our `fel` works on the procedure's body: `byphoare`, `proc`, and `DRestr(D)`'s call
  --     inlined, so that the adversary `D` is the callee; the resampling stays a call)
  byphoare (: True ==> _)
  · phoare_proc
    phoare_inline 1
    fel §ReSample.count (fun _ => ((2 * max_size).toNat : ENNReal) / (2 ^ c.toNat : ENNReal))
      max_size (§G1.bext)
      [ReSample.f : (((FMap.fdom §G1.m).card : ℤ) ≤ max_size ∧ ((FMap.fdom §G1.mi).card : ℤ) ≤ max_size ∧
          §ReSample.count < max_size),
       ReSample.f1 : (((FMap.fdom §G1.m).card : ℤ) < max_size ∧ ((FMap.fdom §G1.mi).card : ℤ) < max_size ∧
          §ReSample.count < max_size)]
    -- EC: + rewrite /felsum Bigreal.sumr_const count_predT size_range.
    --       apply ler_wpmul2r;1:by apply eps_ge0.
    --       by rewrite le_fromint;smt ml=0 w=max_ge0.
    · have hm := max_ge0
      rw [Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul,
        ENNReal.ofReal_mul (by exact_mod_cast hm), ENNReal.ofReal_div_of_pos (by positivity)]
      have e1 : ((max_size : ℤ) : ℝ) = ((max_size.toNat : ℕ) : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hm).symm
      have e2 : ((2 * max_size : ℤ) : ℝ) = (((2 * max_size).toNat : ℕ) : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg (by omega)).symm
      have e3 : ((2 ^ c.toNat : ℤ) : ℝ) = ((2 ^ c.toNat : ℕ) : ℝ) := by push_cast; rfl
      rw [e1, e2, e3, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      push_cast; rfl
    -- (EC's `2:by auto`)
    · stmt_inline*; hoare_auto
    -- EC: + proc;rcondt 2;1:by auto.
    --       wp; rnd (mem (image snd (fdom G1.m `|` fdom G1.mi))); skip=> /> &hr h1 h2 h3 h4 h5.
    --       rewrite (Mu_mem.mu_mem (image snd (fdom G1.m{hr} `|` fdom G1.mi{hr}))
    --                cdistr (1%r/(2^c)%r))//.
    --       + by move=>x _;rewrite DCapacity.dunifin1E capacity_card.
    --       rewrite ler_wpmul2r;1:by apply divr_ge0=>//;apply /c_ge0r.
    --       rewrite imageU fcardU le_fromint.
    --       move:(fcard_image_leq snd (fdom G1.m{hr}))(fcard_image_leq snd (fdom G1.mi{hr})).
    --       smt(fcard_ge0).
    --     (`Mu_mem.mu_mem` for `cdistr`: the old port's `cdistr_expected_mem`)
    · phoare_proc; phoare_auto
      rintro σ ⟨-, hb, hg⟩
      simp only [Bool.not_eq_true] at hb
      simp only [decide_eq_true_eq, hg, and_self, if_true, hb, Bool.false_or]
      set S := Finset.image Prod.snd (FMap.fdom (G1.m.get σ.globals) ∪ FMap.fdom (G1.mi.get σ.globals))
      show _ ≤ ((2 * max_size).toNat : ENNReal) / 2 ^ c.toNat
      calc cdistr.expected (fun a => indicatorE (a ∈ S))
          = cdistr.expected (fun a => if a ∈ S then (1 : ENNReal) else 0) := by
            congr 1; funext a; by_cases h : a ∈ S <;> simp [h]
        _ = (S.card : ENNReal) * (1 / 2 ^ c.toNat) := GaudisCrypt.SHA3.Gcol.cdistr_expected_mem S
        _ ≤ ((2 * max_size).toNat : ENNReal) / 2 ^ c.toNat := by
            rw [mul_one_div]
            have h1 : S.card ≤ (FMap.fdom (G1.m.get σ.globals)).card +
                (FMap.fdom (G1.mi.get σ.globals)).card :=
              Finset.card_image_le.trans (Finset.card_union_le _ _)
            exact ENNReal.div_le_div_right (by exact_mod_cast (show S.card ≤ (2 * max_size).toNat
              by have := hg.1; have := hg.2.1; omega)) _
    -- EC: + by move=>c1;proc;auto=> &hr [^H 2->]/#.
    · intro c1; hoare_proc; hoare_auto
    -- EC: + by move=> b1 c1;proc;auto=> /#.
    · intro c1; hoare_proc; hoare_auto; auto_close
    -- (`keep`: `bad` persists)
    · hoare_proc; hoare_auto
    -- EC: + proc;rcondt 2;1:by auto.
    --       wp;rnd (mem (image snd (fdom G1.m `|` fdom G1.mi) `|` fset1 x));skip=> /> &hr ?????. …
    --     (as for `ReSample.f`, the set one larger)
    · phoare_proc; phoare_auto
      rintro σ ⟨-, hb, hg⟩
      simp only [Bool.not_eq_true] at hb
      simp only [decide_eq_true_eq, hg, and_self, if_true, hb, Bool.false_or]
      set S := Finset.image Prod.snd (FMap.fdom (G1.m.get σ.globals) ∪
        FMap.fdom (G1.mi.get σ.globals)) ∪ fset1 ((localVarLens "x" capacity).get σ)
      show _ ≤ ((2 * max_size).toNat : ENNReal) / 2 ^ c.toNat
      calc cdistr.expected (fun a => indicatorE (a ∈ S))
          = cdistr.expected (fun a => if a ∈ S then (1 : ENNReal) else 0) := by
            congr 1; funext a; by_cases h : a ∈ S <;> simp [h]
        _ = (S.card : ENNReal) * (1 / 2 ^ c.toNat) := GaudisCrypt.SHA3.Gcol.cdistr_expected_mem S
        _ ≤ ((2 * max_size).toNat : ENNReal) / 2 ^ c.toNat := by
            rw [mul_one_div]
            have h1 : S.card ≤ (FMap.fdom (G1.m.get σ.globals)).card +
                (FMap.fdom (G1.mi.get σ.globals)).card + 1 :=
              (Finset.card_union_le _ _).trans (Nat.add_le_add
                (Finset.card_image_le.trans (Finset.card_union_le _ _))
                (by simp [fset1]))
            exact ENNReal.div_le_div_right (by exact_mod_cast (show S.card ≤ (2 * max_size).toNat
              by have := hg.1; have := hg.2.1; omega)) _
    -- EC: + by move=>c1;proc;auto=> &hr [^H 2->]/#.
    · intro c1; hoare_proc; hoare_auto
    -- EC: by move=> b1 c1;proc;auto=> /#.
    · intro c1; hoare_proc; hoare_auto; auto_close
    -- (`keep`)
    · hoare_proc; hoare_auto
  · exact mul_nonneg (by exact_mod_cast max_ge0)
      (div_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ 2 * max_size by have := max_ge0; omega))
        (by positivity))

set_option maxHeartbeats 8000000 in
-- one declaration: EC's call over three oracles, the resampling loops
/-- EC's `local equiv EG2_Gext : Eager(G2(DRestr(D))).main2 ~ Gext.distinguish : ={glob D} ==>
ReSample.count{2} <= max_size /\ ((G1.bext{1} \/ inv_ext G1.m{1} G1.mi{1} FRO.m{1}) =>
G1.bext{2})`. -/
theorem EG2_Gext : equiv[ Eager(G2(DRestr(D))).main2 ~ Gext(D).distinguish :
    ={glob D} ==> §ReSample.count{2} ≤ max_size ∧
      ((§G1.bext{1} ∨ inv_ext §G1.m{1} §G1.mi{1} §FRO.m{1}) → §G1.bext{2}) ] := by
  -- EC: proc;inline *;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: while (={l,FRO.m,G1.m,G1.mi} /\ card (fdom G1.m{2}) <= max_size /\
  --          card (fdom G1.mi{2}) <= max_size /\
  --         ReSample.count{2} + size l{2} <= max_size /\
  --         ((G1.bext{1} \/
  --          exists (x : state) (h : handle),
  --            mem (fdom G1.m{1} `|` fdom G1.mi{1}) x /\
  --            FRO.m{1}.[h] = Some (x.`2, Unknown) /\ !mem l{1} h) =>
  --          G1.bext{2})).
  equiv_while (={l, FRO.m, G1.m, G1.mi} ∧ ((FMap.fdom §G1.m{2}).card : ℤ) ≤ max_size ∧
      ((FMap.fdom §G1.mi{2}).card : ℤ) ≤ max_size ∧ §ReSample.count{2} + size §l{2} ≤ max_size ∧
      ((§G1.bext{1} ∨ ∃ (x : state) (h : handle), x ∈ FMap.fdom §G1.m{1} ∪ FMap.fdom §G1.mi{1} ∧
          FMap.get §FRO.m{1} h = some (x.2, Unknown) ∧ h ∉ §l{1}) → §G1.bext{2}))
  -- EC: + rcondt{2} 3.
  --       + move=> &m;auto=> &m'[#] 6!-> /= + _ _;case (l{m'})=>//=; smt w=List.size_ge0.
  · stmt_rcondt{2} 3
    · hoare_auto; auto_prep
      exact ⟨‹_›, ‹_›, by have := size_pos_of_isEmpty ‹_›; omega⟩
    -- EC: auto=> &ml&mr[#]6!->;case(l{mr})=>[//|h1 l1/=Hle Hext c ?/=];split.
    --     + smt w=(drop0 size_ge0).
    --     rewrite drop0=>-[H|[x h][#]];1:by rewrite Hext // H.
    --     rewrite get_setE;case (h=h1)=> [/=->Hin->_ | Hneq ???].
    --     + by right;apply (mem_image snd _ x).
    --     by rewrite Hext 2://;right;exists x h;rewrite Hneq.
    equiv_auto; auto_prep
    exact ⟨‹_›, ‹_›, resample_step ‹_› ‹_› ‹_›⟩
  -- EC: wp; call (_: ={F.RO.m,FRO.m,G1.paths,G1.mh,G1.mhi,G1.m,G1.mi,G1.chandle,G1.bext,
  --                    C.c,C.queries} /\
  --                 inv_le G1.m{2} G1.mi{2} C.c{1} FRO.m{2}  ReSample.count{2}).
  · stmt_wp
    equiv_call (_ : ={F.RO.m, FRO.m, G1.paths, G1.mh, G1.mhi, G1.m, G1.mi, G1.chandle, G1.bext,
        C.c, C.queries} ∧ inv_le §G1.m{2} §G1.mi{2} §C.c{1} §FRO.m{2} §ReSample.count{2})
    · sorry
    · sorry
    · sorry
    -- EC: auto;progress[delta];rewrite ?(size0,restr0,restr_set,rem0,max_ge0,-sizeE,-cardE) //=.
    --     + smt(size_rem_le size0).
    --     + smt(). + smt(). + smt().
    --     + by elim H7=>// [[x h] [#]];rewrite -memE mem_fdom dom_restr /in_dom_with domE=> _ ->.
    --     by apply H10.
    · equiv_auto; auto_prep
      refine ⟨⟨rfl, ?_⟩, ?_⟩
      · simp [inv_le, FMap.restr_set, FMap.restr0, max_ge0]
      · intro r₁ g₁ r₂ g₂ h; auto_prep
        obtain ⟨h1, h2, h3, h4⟩ := ‹inv_le _ _ _ _ _›
        have hs : size (FMap.fdom (FMap.restr Unknown (FRO.m.get g₁))).toList =
            ((FMap.fdom (FMap.restr Unknown (FRO.m.get g₁))).card : ℤ) := by simp [size]
        refine ⟨⟨⟨by omega, by omega, by omega, ?_⟩, by simp⟩, ?_⟩
        -- EC: + by elim H7=>// [[x h] [#]];rewrite -memE mem_fdom dom_restr /in_dom_with domE=> _ ->.
        · rintro (hb | ⟨x, h, -, hh, hn⟩)
          · exact hb
          · refine absurd (Finset.mem_toList.mpr ((FMap.mem_fdom _ _).mpr
              ((FMap.dom_restr _ _ _).mpr ⟨(FMap.domE _ _).mpr ?_, ?_⟩))) hn
            · rw [hh]; simp
            · show ((FMap.get (FRO.m.get g₁) h).getD default).2 = Unknown
              rw [hh]; rfl
        -- EC: by apply H10.  (the loops' exit: `l` empty)
        · rintro τ₁ τ₂ - - ⟨-, -, -, hcnt, hI⟩ hl₁ -
          have hl : (localVarLens "l" (List handle)).get τ₁ = [] :=
            List.isEmpty_iff.mp (by simpa using hl₁)
          exact ⟨(le_add_of_nonneg_right (size_ge0 _)).trans hcnt,
            fun hb => hI (hb.imp_right fun ⟨x, h, hx, hh⟩ => ⟨x, h, hx, hh, by simp [hl]⟩)⟩

end EXT

end GaudisCrypt.SHA3.Pilot.Gext
