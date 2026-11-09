import GaudisCrypt.Examples.SHA3.Pilot.Handle
import GaudisCrypt.Examples.SHA3.SmartCounter.Gcol

/-!
# The collision event of `G1` (EasyCrypt `proof/smart_counter/Gcol.eca`) — EC-fidelity port

`Pr_G1col` bounds the probability of `G1.bcol` by `max_size · (2 max_size / 2^c)`, through the
local game `Gcol` that counts the capacity samples.  Over the old port's `Handle` declarations
(as `Pilot/Handle.lean`).

Translation:
* the local module `Gcol` is declared here as in EC, its variable `count` a `global_var`
  (`Gcol.count`); its procedures `Gcol.sample_c`, `Gcol.M`, `Gcol.S` are modules of their own (EC's
  inner modules), `Gcol D` the game with `D` a Lean parameter;
* `declare module D <: DISTINGUISHER {-C, -PF, -G1, -Gcol.sample_c}`: EC's freshness of the local
  module for `D` in `D`'s restriction (as `SecureRO`'s local modules).
-/

set_option linter.dupNamespace false

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: EC's abstract `call (_: ={…} /\ inv)` asks the oracles `={arg} /\ inv ==> ={res} /\ inv`;
  our rule (`equiv_call (_ : ={…} ∧ I)`) also `={glob D}` (the up-to-bad variant frames it from
  the oracles' writes, `WritesKeep`): `glob D` added to EC's intermediate conditions.
* GAP 2: inline by name: EC's paths `G1(DRestr(D)).S.fi`, `Gcol.S.fi` do not match the old
  declarations' call sites `DPRIMITIVE.fi G1.S` (not definitionally equal at default transparency
  either): the only call on each side inlined by index.
* GAP 4: `swap` past a call that reads (but does not write) what the moved assignment reads:
  our frame needs the read variables outside the callee's whole footprint (reads and writes
  together); EC's `swap` uses read/write sets.
* GAP 3: `→` between booleans in conditions (EC's `G1.bcol{1} => G1.bcol{2}`) needs `= true`.
* GAP 6: EC `while`'s exit goal: after `auto_prep` the frames are equations `x τ₂ = x τ₁` between
  reads of the final states (not substituted; `simp_all` cycles on them).
* GAP 7: `equiv_call (_ : ={x})` on a concrete callee (`prhlProc_glob_module`) has no frame; EC's
  `call (_: ={x})` keeps what the callee does not write: `equiv_call (_ : ={arg, x} ==> ={res, x})`
  (framed) and its callee goal by `equiv_proc; equiv_auto` (EC's `1:by sim`).
* GAP 5: `glob D` read through an `if` (the conditional write of `RO.get`): `glob_simp` rewrites
  only writes it sees directly under the getter; the getter should be pushed into the `if`.
-/

namespace GaudisCrypt.SHA3.Pilot.Gcol

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle
open GaudisCrypt.SHA3.Gcol (card_rng_set hinv_image)

variable [SLCommon.Params]

/-- EC's `state` (`SLCommonCore`'s, named here: a root `state` exists). -/
abbrev state := GaudisCrypt.SHA3.SLCommon.state

-- `grind` on `card_rng_set` by the map written, not its normalized inequality (EC's
-- `smt(card_rng_set)` as `smt_close [card_rng_set]`)
grind_pattern card_rng_set => FMap.frng (FMap.set m x y)

/-- EC's `Gcol.count`. -/
global_var Gcol.count : ℤ

module Gcol.sample_c {
  proc sample_c () : capacity {
    var c : capacity;
    c <- c0;
    if (decide (((Finset.image Prod.fst
          (FMap.frng ($FRO.m : FMap handle (capacity × flag)))).card : ℤ) ≤ 2 * max_size ∧
        $Gcol.count < max_size)) {
      c <$ cdistr;
      G1.bcol <- $G1.bcol || decide ($c ∈ Finset.image Prod.fst
        (FMap.frng ($FRO.m : FMap handle (capacity × flag))));
      Gcol.count <- $Gcol.count + 1;
    }
    return $c
  };
}

-- EC's `Gcol.M`
module Gcol.M : DFUNCTIONALITY {
  proc f (p : List block) : block {
    var sa : block, sa' : block, sc : capacity, h : handle, i : ℤ, counter : ℤ;
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
          sc <- call Gcol.sample_c ();
          sa' <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (take ($i + 1) $p);
          sa <- $sa +^ nth default $p $i;
          G1.mh <- FMap.set $G1.mh ($sa, $h) ($sa', $G1.chandle);
          G1.mhi <- FMap.set $G1.mhi ($sa', $G1.chandle) ($sa, $h);
          sa, h <- ($sa', $G1.chandle);
          FRO.m <- FMap.set $FRO.m $G1.chandle ($sc, Unknown);
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

-- EC's `Gcol.S`
module Gcol.S : DPRIMITIVE {
  proc f (x : state) : state {
    var p : List block, v : block, y : state, y1 : block, y2 : capacity, hy2 : handle,
      hx2 : handle;
    if (!(decide (FMap.dom ($G1.m : smap) $x))) {
      y <- (b0, c0);
      if (!(decide (FMap.rng ($FRO.m : FMap handle (capacity × flag)) (($x).2, Known)))) {
        FRO.m <- FMap.set $FRO.m $G1.chandle (($x).2, Known);
        G1.chandle <- $G1.chandle + 1;
      }
      hx2 <- oget (hinvK $FRO.m ($x).2);
      if (decide (FMap.dom ($G1.paths : FMap capacity (List block × block)) ($x).2)) {
        p, v <- oget (FMap.get ($G1.paths : FMap capacity (List block × block)) ($x).2);
        y1 <- call (PROM.FullRO.ROmap.get (List block) block F.RO) (rcons $p ($v +^ ($x).1));
        y2 <- call Gcol.sample_c ();
      } else {
        y1 <$ bdistr;
        y2 <- call Gcol.sample_c ();
      }
      y <- ($y1, $y2);
      if (decide (FMap.dom ($G1.mh : hsmap) (($x).1, $hx2) ∧
          FMap.in_dom_with ($FRO.m : FMap handle (capacity × flag))
            (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2 Unknown)) {
        hy2 <- (oget (FMap.get ($G1.mh : hsmap) (($x).1, $hx2))).2;
        y <- (($y).1, (oget (FMap.get ($FRO.m : FMap handle (capacity × flag)) $hy2)).1);
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
        G1.m <- FMap.set $G1.m $x $y;
        G1.mi <- FMap.set $G1.mi $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
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
    var y : state, y1 : block, y2 : capacity, hx2 : handle, hy2 : handle;
    if (!(decide (FMap.dom ($G1.mi : smap) $x))) {
      y <- (b0, c0);
      if (!(decide (FMap.rng ($FRO.m : FMap handle (capacity × flag)) (($x).2, Known)))) {
        FRO.m <- FMap.set $FRO.m $G1.chandle (($x).2, Known);
        G1.chandle <- $G1.chandle + 1;
      }
      hx2 <- oget (hinvK $FRO.m ($x).2);
      y1 <$ bdistr;
      y2 <- call Gcol.sample_c ();
      y <- ($y1, $y2);
      if (decide (FMap.dom ($G1.mhi : hsmap) (($x).1, $hx2) ∧
          FMap.in_dom_with ($FRO.m : FMap handle (capacity × flag))
            (oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2))).2 Unknown)) {
        y1, hy2 <- oget (FMap.get ($G1.mhi : hsmap) (($x).1, $hx2));
        y <- (($y).1, (oget (FMap.get ($FRO.m : FMap handle (capacity × flag)) $hy2)).1);
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
        G1.mi <- FMap.set $G1.mi $x $y;
        G1.m <- FMap.set $G1.m $y $x;
      } else {
        hy2 <- $G1.chandle;
        G1.chandle <- $G1.chandle + 1;
        FRO.m <- FMap.set $FRO.m $hy2 (($y).2, Known);
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

-- EC's local module `Gcol`'s `main`, with `D` a Lean parameter (on purpose: `Gcol D` is the game)
set_option linter.gaudisCrypt.using false in
module Gcol (D : DISTINGUISHER) {
  proc main () : Bool {
    var b : Bool;
    F.RO.m <- (FMap.empty : FMap (List block) block);
    G1.m <- (FMap.empty : smap);
    G1.mi <- (FMap.empty : smap);
    G1.mh <- (FMap.empty : hsmap);
    G1.mhi <- (FMap.empty : hsmap);
    G1.bcol <- false;
    FRO.m <- FMap.set (FMap.empty : FMap handle (capacity × flag)) 0 (c0, Known);
    G1.paths <- FMap.set (FMap.empty : FMap capacity (List block × block)) c0 ([], b0);
    G1.chandle <- 1;
    Gcol.count <- 0;
    b <- call (Module.app (DRestr D) (Module.pair Gcol.M Gcol.S)) ();
    return $b
  };
}

/-- The footprint of `Gcol.sample_c` (for the solver, which reads concrete modules off their code
but not a procedure called as a module, `Module.proc`). -/
@[fp_bound] theorem fvP_sample_c :
    FVP.fvP (Module.proc Gcol.sample_c.sample_c.procedure) ≤
      FRO.m.footprint ⊔ (G1.bcol.footprint ⊔ Gcol.count.footprint) := by
  fp_module (Lens.pair FRO.m (Lens.pair G1.bcol Gcol.count))

section PROOF

declare module D <: DISTINGUISHER {-C, -PF, -G1, -Gcol.sample_c}

-- EC's `declare axiom D_ll`
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 8000000 in
-- one declaration: EC's call over three oracles, the twelve-variable invariant
/-- EC's `local equiv G1_col : G1(DRestr(D)).main ~ Gcol.main : ={glob D} ==>
(G1.bcol{1} => G1.bcol{2}) /\ Gcol.count{2} <= max_size`. -/
theorem G1_col : equiv[ G1(DRestr(D)).main ~ Gcol(D).main :
    ={glob D} ==> (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧ §Gcol.count{2} ≤ max_size ] := by
  -- EC: proc;inline*;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: call (_: ={F.RO.m,G1.mi,G1.paths,G1.m,G1.mhi,G1.chandle,G1.mh,FRO.m,C.c,C.queries}/\
  --          (G1.bcol{1} => G1.bcol{2}) /\
  --          (card (frng FRO.m) <= 2*C.c + 1 /\
  --           Gcol.count <= C.c <= max_size){2}).
  equiv_call (_ : ={F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh, FRO.m, C.c,
      C.queries} ∧ (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
      ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 1 ∧ §Gcol.count{2} ≤ §C.c{2} ∧
      §C.c{2} ≤ max_size)
  -- EC: + proc;sp 1 1;if=>//;inline G1(DRestr(D)).S.f Gcol.S.f;swap -3.
  · equiv_proc; stmt_sp 1 1; stmt_if
    · auto_close
    --     (GAP 2: the only call on each side, by index)
    · stmt_inline 0; stmt_swap -3
      -- EC: sp;if;1,3:auto=>/#;swap{1}[1..2]3;sp 1 1.
      stmt_sp; stmt_if
      on_goals 1, 3 => (equiv_auto; auto_close)
      stmt_swap{1} [1..2] 3; stmt_sp 1 1
      -- EC: seq 5 5 : (={x0, y0, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle,
      --                 G1.mh, FRO.m, C.c, C.queries}
      --       /\ (G1.bcol{1} => G1.bcol{2})
      --       /\ card (frng FRO.m{2}) <= 2 * C.c{2} + 1
      --       /\ Gcol.count{2} <= C.c{2} <= max_size );last by if;auto.
      --     (GAP 1: `glob D` added)
      equiv_seq 5 5 : (={glob D, x0, y0, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh,
          FRO.m, C.c, C.queries} ∧ (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
          ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} + 1 ∧
          §Gcol.count{2} ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
      on_goals 2 => (stmt_if <;> equiv_auto; auto_close)
      -- EC: seq 2 2 : (={x0, hx2, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle,
      --                 G1.mh, FRO.m, C.c, C.queries}
      --       /\ (G1.bcol{1} => G1.bcol{2})
      --       /\ card (frng FRO.m{2}) <= 2 * C.c{2}
      --       /\ Gcol.count{2} + 1 <= C.c{2} <= max_size).
      --     + by if; auto=> /> &1 &2; smt(card_rng_set).
      equiv_seq 2 2 : (={glob D, x0, hx2, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh,
          FRO.m, C.c, C.queries} ∧ (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
          ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} ∧
          §Gcol.count{2} + 1 ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
      · stmt_if <;> equiv_auto
        all_goals smt_close [card_rng_set]
      -- EC: if;1:auto.
      stmt_if
      · auto_close
      -- EC: - inline Gcol.sample_c;rcondt{2}4.
      --       * auto;inline*;auto;progress.
      --         + by have/#:=fcard_image_leq (fun (p : capacity * flag) => p.`1) (frng FRO.m{hr}).
      --         rewrite/#.
      · stmt_inline (Gcol.sample_c)
        stmt_rcondt{2} 4
        · hoare_auto; stmt_inline*; hoare_auto; auto_prep
          exact ⟨(Nat.cast_le.2 Finset.card_image_le).trans (by omega), by omega⟩
        -- EC: seq 3 4 : (={x0, p, v, y1, hx2, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi,
        --                 G1.chandle, G1.mh, FRO.m, C.c, C.queries}
        --       /\ (G1.bcol{1} => G1.bcol{2})
        --       /\ card (frng FRO.m{2}) <= 2 * C.c{2}
        --       /\ Gcol.count{2} + 1 <= C.c{2} <= max_size
        --       /\ (x0{1}.`2 \in G1.paths{1})
        --       /\ y2{1} = c{2});1: by inline*;auto.
        equiv_seq 3 4 : (={glob D, x0, p, v, y1, hx2, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi,
            G1.chandle, G1.mh, FRO.m, C.c, C.queries} ∧ (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
            ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} ∧
            §Gcol.count{2} + 1 ≤ §C.c{2} ∧ §C.c{2} ≤ max_size ∧
            FMap.dom §G1.paths{1} (§x0{1}).2 ∧ §y2{1} = §(localVarLens "c" capacity){2})
        · stmt_inline*; equiv_auto; auto_close
        -- EC: sp 1 4;if;auto;progress.
        --     + by have->:=(H H6).
        --     + smt(card_rng_set).
        --     + case:H5=>/=[h|H_hinv];1: by have->:=H h.
        --       have:=hinvP FRO.m{2} c{2};rewrite H_hinv/=imageP/==>[][]f H_f.
        --       by right; exists (c{2}, f)=> //=; rewrite mem_frng rngE/= /#.
        --     smt(card_rng_set).
        stmt_sp 1 4; stmt_if <;> equiv_auto
        · auto_close
        all_goals smt_close [hinv_image, card_rng_set]
      -- EC: inline Gcol.sample_c;rcondt{2}3.
      --     * auto;progress.
      --       + by have/#:=fcard_image_leq (fun (p : capacity * flag) => p.`1) (frng FRO.m{hr}).
      --       rewrite/#.
      · stmt_inline (Gcol.sample_c)
        stmt_rcondt{2} 3
        · hoare_auto; auto_prep
          exact ⟨(Nat.cast_le.2 Finset.card_image_le).trans (by omega), by omega⟩
        -- EC: seq 2 3 : (={x0, y1, hx2, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi,
        --                 G1.chandle, G1.mh, FRO.m, C.c, C.queries}
        --       /\ (G1.bcol{1} => G1.bcol{2})
        --       /\ card (frng FRO.m{2}) <= 2 * C.c{2}
        --       /\ Gcol.count{2} + 1 <= C.c{2} <= max_size
        --       /\ ! (x0{1}.`2 \in G1.paths{1})
        --       /\ y2{1} = c{2});1: by auto.
        equiv_seq 2 3 : (={glob D, x0, y1, hx2, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi,
            G1.chandle, G1.mh, FRO.m, C.c, C.queries} ∧ (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
            ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * §C.c{2} ∧
            §Gcol.count{2} + 1 ≤ §C.c{2} ∧ §C.c{2} ≤ max_size ∧
            ¬ FMap.dom §G1.paths{1} (§x0{1}).2 ∧ §y2{1} = §(localVarLens "c" capacity){2})
        · equiv_auto
        -- EC: sp 1 4;if;auto;progress.  (the four bullets as above)
        stmt_sp 1 4; stmt_if <;> equiv_auto
        · auto_close
        all_goals smt_close [hinv_image, card_rng_set]
    · equiv_auto
  -- EC: + proc;sp 1 1;if=>//.
  --       inline G1(DRestr(D)).S.fi Gcol.S.fi;swap-3.
  · equiv_proc; stmt_sp 1 1; stmt_if
    · auto_close
      --     (GAP 2: the only call on each side, by index)
    · stmt_inline 0; stmt_swap -3
      -- EC: seq 2 2 : (={F.RO.m,G1.mi,G1.paths,G1.m,G1.mhi,G1.chandle,G1.mh,FRO.m,
      --                 C.c,C.queries,x0} /\
      --               (G1.bcol{1} => G1.bcol{2}) /\
      --               (card (frng FRO.m) + 2 <= 2*C.c + 1 /\
      --                Gcol.count + 1 <= C.c <= max_size){2});1:by auto=>/#.
      --     (GAP 1: `glob D` added: our call rule keeps `={glob D}` in the oracles' judgments)
      equiv_seq 2 2 : (={glob D, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh, FRO.m,
          C.c, C.queries, x0} ∧ (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
          ((FMap.frng §FRO.m{2}).card : ℤ) + 2 ≤ 2 * §C.c{2} + 1 ∧
          §Gcol.count{2} + 1 ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
      · equiv_auto; auto_close
      -- EC: if=>//;last by auto=>/#.
      stmt_if
      · auto_close
      on_goals -1 => (equiv_auto; auto_close)
      -- EC: seq 3 3:(={F.RO.m,G1.mi,G1.paths,G1.m,G1.mhi,G1.chandle,G1.mh,FRO.m,
      --               C.c,C.queries,x0,hx2} /\
      --             (G1.bcol{1} => G1.bcol{2}) /\
      --             (card (frng FRO.m) + 1 <= 2 * C.c + 1 /\
      --              Gcol.count + 1 <= C.c <= max_size){2}).
      --     + sp 1 1;if;auto;smt ml=0 w=card_rng_set.
      equiv_seq 3 3 : (={glob D, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh, FRO.m,
          C.c, C.queries, x0, hx2} ∧ (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
          ((FMap.frng §FRO.m{2}).card : ℤ) + 1 ≤ 2 * §C.c{2} + 1 ∧
          §Gcol.count{2} + 1 ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
      · stmt_sp 1 1; stmt_if <;> equiv_auto
        all_goals smt_close [card_rng_set]
      -- EC: seq 3 3: (={F.RO.m,G1.mi,G1.paths,G1.m,G1.mhi,G1.chandle,G1.mh,FRO.m,
      --                C.c,C.queries,x0,hx2,y0,y1,y2} /\ y0{1} = (y1,y2){1} /\
      --              ((G1.bcol\/hinv FRO.m y0.`2 <> None){1} => G1.bcol{2}) /\
      --              (card (frng FRO.m) + 1 <= 2 * C.c + 1 /\
      --              Gcol.count <= C.c <= max_size){2});2:by auto;smt w=card_rng_set.
      equiv_seq 3 3 : (={glob D, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh, FRO.m,
          C.c, C.queries, x0, hx2, y0, y1, y2} ∧ §y0{1} = (§y1{1}, §y2{1}) ∧
          ((§G1.bcol{1} = true ∨ hinv §FRO.m{1} (§y0{1}).2 ≠ none) → §G1.bcol{2} = true) ∧
          ((FMap.frng §FRO.m{2}).card : ℤ) + 1 ≤ 2 * §C.c{2} + 1 ∧
          §Gcol.count{2} ≤ §C.c{2} ∧ §C.c{2} ≤ max_size)
      on_goals 2 => (equiv_auto; smt_close [card_rng_set])
      -- EC: inline Gcol.sample_c.
      stmt_inline (Gcol.sample_c)
      -- EC: rcondt{2}3.
      --     + by auto;progress;have /#:= fcard_image_leq fst (frng FRO.m{hr}).
      stmt_rcondt{2} 3
      · hoare_auto; smt_close [Finset.card_image_le]
      -- EC: auto=> /> ?? Himp _ _ _ ?_?_ [/Himp->// | X];right;apply hinv_image=> //.
      equiv_auto; smt_close [hinv_image]
    · equiv_auto
  -- EC: + proc;sp 1 1;if=>//;2:auto;sp;if=>//;swap 1;wp.
  · equiv_proc; stmt_sp 1 1; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    --     (GAP 4: EC's `swap 1` moves `C.c <- …` past the call, which reads `C.queries` (our frame
    --     wants it outside the callee's footprint): inlined first, then moved past the inlined code
    --     (whose calls do not touch `C`), the same order as EC's)
    -- EC: inline G1(DRestr(D)).M.f Gcol.M.f;sp;wp.
    --     (GAP 2: the only call on each side, by index)
    stmt_inline 0
    --     (EC's `wp` before the inlining, ours after it: then the second `wp` has nothing to do)
    stmt_swap{1} 1 8; stmt_swap{2} 1 7; stmt_wp
    stmt_sp
    -- EC: seq 1 1:
    --      (={F.RO.m,G1.mi,G1.paths,G1.m,G1.mhi,G1.chandle,G1.mh,FRO.m,C.c,
    --        C.queries,b,p,h,i,sa,bs,counter} /\ i{1}=size p{2} /\ p{2} = bs{2} /\
    --       (G1.bcol{1} => G1.bcol{2}) /\
    --       (0 <= counter{2} <= size p{2} -
    --         prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{1})))) /\
    --       card (frng FRO.m{2}) <= 2 * (C.c{2} + counter{2}) + 1 /\
    --       Gcol.count{2} + size p{2} -
    --         prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{1})))
    --         - counter{2} <= C.c{2} + size p{2} -
    --         prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{1})))
    --         <= max_size);
    --         last by inline*;auto;smt(size_ge0 prefix_sizel).
    --     (`b` is assigned after: not in the condition; GAP 1: `glob D` added)
    equiv_seq 1 1 : (={glob D, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh, FRO.m,
        C.c, C.queries, p, h, i, sa, bs, counter} ∧ §i{1} = size §p{2} ∧ §p{2} = §bs{2} ∧
        (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
        0 ≤ §counter{2} ∧
        §counter{2} ≤ size §p{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) ∧
        ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * (§C.c{2} + §counter{2}) + 1 ∧
        §Gcol.count{2} + size §p{2} -
          «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) - §counter{2} ≤
          §C.c{2} + size §p{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) ∧
        §C.c{2} + size §p{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) ≤
          max_size)
    on_goals 2 =>
      stmt_inline*; equiv_auto; auto_prep
      --   (GAP 5: `glob D` read through the `if` of `RO.get`'s write: split by hand)
      refine ⟨by split_ifs <;> glob_simp <;> assumption, ‹_›, by omega, by omega, ‹_›⟩
    -- EC: while
    --      (={F.RO.m,G1.mi,G1.paths,G1.m,G1.mhi,G1.chandle,G1.mh,FRO.m,C.c,b,
    --         p,h,i,sa,counter,C.queries} /\ (0 <= i <= size p){1} /\
    --       (G1.bcol{1} => G1.bcol{2}) /\
    --       (0 <= counter{2} <= size p{2} -
    --         prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{1})))) /\
    --       card (frng FRO.m{2}) <= 2 * (C.c{2} + counter{2}) + 1 /\
    --       Gcol.count{2} + size p{2} -
    --         prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{1})))
    --         - counter{2} <= C.c{2} + size p{2} -
    --         prefix p{2} (get_max_prefix p{2} (elems (fdom C.queries{1})))
    --         <= max_size);last first.
    equiv_while (={glob D, F.RO.m, G1.mi, G1.paths, G1.m, G1.mhi, G1.chandle, G1.mh, FRO.m, C.c,
        p, h, i, sa, counter, C.queries} ∧ (0 ≤ §i{1} ∧ §i{1} ≤ size §p{1}) ∧
        (§G1.bcol{1} = true → §G1.bcol{2} = true) ∧
        0 ≤ §counter{2} ∧
        §counter{2} ≤ size §p{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) ∧
        ((FMap.frng §FRO.m{2}).card : ℤ) ≤ 2 * (§C.c{2} + §counter{2}) + 1 ∧
        §Gcol.count{2} + size §p{2} -
          «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) - §counter{2} ≤
          §C.c{2} + size §p{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) ∧
        §C.c{2} + size §p{2} - «prefix» §p{2} (get_max_prefix §p{2} (elems (FMap.fdom §C.queries{1}))) ≤
          max_size)
    -- EC: + by auto=> />; smt(size_ge0 prefix_sizel prefix_ge0).
    case hpre =>
      equiv_auto; auto_prep
      refine ⟨⟨size_ge0 _, ‹_›, sub_nonneg.2 (prefix_sizel _ _), by omega, by omega, ‹_›⟩, ?_⟩
      --   (GAP 6: the exit's frames `x τ₂ = x τ₁` are left as hypotheses (a cycle for `simp_all`))
      auto_prep
      exact ⟨Eq.trans ‹_› (Eq.symm ‹_›), by omega, Eq.symm ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    -- EC: if=>//;auto;1:smt ml=0 w=size_ge0.
    stmt_if
    · auto_close
    on_goals 1 => (equiv_auto; auto_close)
    equiv_auto
    -- EC: if=>//;2:auto;2:smt(size_ge0 prefix_sizel).
    stmt_if
    · auto_close
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: auto;call (_: ={F.RO.m})=>/=;1:by sim.
    equiv_auto
    --     (GAP 7: our `equiv_call (_ : ={F.RO.m})` on a concrete callee has no frame: the
    --     `P ==> Q` form, whose frame keeps what the callee does not write)
    equiv_call (_ : ={arg, F.RO.m} ==> ={res, F.RO.m})
    · equiv_proc; equiv_auto
    -- EC: inline *;rcondt{2} 2.
    --     + auto;progress.
    --       - apply(StdOrder.IntOrder.ler_trans _ _ _ (fcard_image_leq fst (frng FRO.m{hr})))=>/#.
    --       smt(size_ge0 prefix_sizel).
    stmt_inline*
    stmt_rcondt{2} 2
    · hoare_auto; auto_prep
      exact ⟨(Nat.cast_le.2 Finset.card_image_le).trans (by omega), by omega⟩
    -- EC: auto;smt ml=0 w=(hinv_image card_rng_set).
    equiv_auto; auto_prep
    smt_close [hinv_image, card_rng_set]
  -- EC: auto;progress;3:by smt ml=0.
  --     + rewrite -(add0z 1) -{2}fcards0<:capacity*flag> -(frng0<:int,_>).
  --       exact/card_rng_set/max_ge0.
  --     by apply max_ge0.
  · equiv_auto; auto_prep
    refine ⟨⟨rfl, (card_rng_set _ _ _).trans (by simp), max_ge0⟩, ?_⟩
    auto_close

end PROOF

end GaudisCrypt.SHA3.Pilot.Gcol

