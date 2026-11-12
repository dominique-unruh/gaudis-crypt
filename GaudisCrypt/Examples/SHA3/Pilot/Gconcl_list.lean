import GaudisCrypt.Examples.SHA3.Pilot.Gconcl
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl_list

/-!
# From the squeezeless sponge to the block sponge (EasyCrypt `proof/smart_counter/Gconcl_list.ec`)
— EC-fidelity port

EC's judgments in EC's scripts, over the old port's declarations
(`SmartCounter/Gconcl_list.lean`), as `Pilot/Gconcl.lean`.  The plain lemmas (`leq_add_nin`, …)
are the old port's.

Translation:
* EC's `local equiv E (D <: DISTINGUISHER {-…}) : …` is a theorem `∀ (D <: DISTINGUISHER {-…}),
  equiv[ … ]`.
-/

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: `ideal_equiv`'s F.f guard `valid p{1} = valid p{2}` after `sp` over `p, n <- x0` and
  `x0 <- (bl, nb)`: our closer does not chain the two tuple equations (EC's `auto`):
  `simp_reads_all; smt_close []`.
* GAP 2: EC's `auto` takes a one-sided sampling of a lossless distribution (`r <$ dout`) as
  lossless; ours leaves `bdistr`'s mass (`bdistr_expected_one`), and `smt_close` with it as a hint
  fails on an unknown free variable (an `ec_instances` bug): `simp only [bdistr_expected_one]`.
* GAP 3: after `sp` over an unrolled round's head (`i <- i + 1`), `rcondt`'s test reads
  (`Evaluatable.eval σ i`) and the state's (`i.get σ`) are generalized apart: the side goal is
  `i < n` about fresh `i`, `n`.  `sorry` until fixed.
* EC's `smt` selects its lemmas (`domE`, `mem_set`, `valid_spec`, the definition of `<=`) itself:
  our `smt_close` lists them (deviation, not a gap).
-/

namespace GaudisCrypt.SHA3.Pilot.Gconcl_list

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.BlockSponge GaudisCrypt.SHA3.Gconcl_list
open GaudisCrypt.SHA3.Gconcl (IF S)

variable [SLCommon.Params] [BlockSponge.Params] [Gconcl_list.Params]

/-! ## Section `Ideal` -/

set_option maxHeartbeats 4000000 in
/-- EC's `local equiv ideal_equiv (D <: DISTINGUISHER{-SLCommon.C, -C, -IF, -S}) :
SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main ~ SLCommon.IdealIndif(IF, S, A(D)).main :
={glob D} ==> ={glob D, res}`. -/
theorem ideal_equiv : ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S}),
    equiv[ SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main ~
      SLCommon.IdealIndif(IF, S, A(D)).main : ={glob D} ==> ={glob D, res} ] := by
  intro D _
  -- EC: proc;inline*;auto;sp.
  equiv_proc; stmt_inline*; equiv_auto; stmt_sp
  -- EC: call(: ={glob IF, glob S, glob A} /\ SLCommon.C.c{1} <= C.c{1}
  --     /\ SLCommon.C.queries{1} <= F.RO.m{2});auto;last first.
  equiv_call (_ : ={glob IF, glob S, glob A} ∧ §SLCommon.C.c{1} ≤ §C.c{1} ∧
    «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2})
  --     (EC's `last first`: the precondition is our last goal)
  -- EC: + proc;inline*;sp;if;auto;sp;rcondt{1}1;1:auto=>/#;sp;if=>//=;2:auto=>/#.
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    equiv_auto; stmt_sp; stmt_rcondt{1} 1
    · hoare_auto; auto_close
    stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    -- EC: wp 7 6;conseq(:_==> ={y} /\ ={F.RO.m} /\ ={S.paths, S.mi, S.m}
    --     /\ SLCommon.C.queries{1} <= F.RO.m{2});1:smt().
    stmt_wp 7 6
    equiv_conseq (: _ ==> ={y} ∧ ={SLCommon.F.RO.m} ∧ ={S.paths, S.mi, S.m} ∧
      «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2})
    case post => auto_close
    -- EC: if;auto;smt(leq_add_nin).
    stmt_if
    · auto_close
    all_goals equiv_auto
    smt_close [leq_add_nin]
  -- EC: + by proc;inline*;sp;if;auto;sp;rcondt{1}1;1:auto=>/#;sp;if;auto;smt().
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    equiv_auto; stmt_sp; stmt_rcondt{1} 1
    · hoare_auto; auto_close
    stmt_sp; stmt_if
    · auto_close
    --     (EC's `smt()`: nothing left after `auto`)
    all_goals equiv_auto
  -- EC: proc;inline*;sp;if;auto;swap 6;auto;sp;if;auto;2:smt(size_ge0).
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · auto_close
    on_goals 2 => equiv_auto
    equiv_auto; stmt_swap 6; equiv_auto; stmt_sp; stmt_if
    --     (GAP 1: EC's `auto` on the guard; our closer loses `(p, n) = x0`, `x0 = (bl, nb)`)
    · intro σ₁ σ₂ h; simp_reads_all; smt_close []
    on_goals 2 => (equiv_auto; smt_close [size_ge0])
    --     (EC's `auto` on the branch: nothing to do here)
    -- EC: case(0 < n{1});last first.
    equiv_case (0 < §n{1})
    on_goals 2 =>
      -- EC: + sp;rcondf{1}3;2:rcondf{2}4;1,2:auto.
      --        - by if;auto;if;auto.
      stmt_sp; stmt_rcondf{1} 3
      on_goals 2 => stmt_rcondf{2} 4
      --     (EC's `by if;auto;if;auto` on the first: closed by `auto` already)
      · hoare_auto
      · hoare_auto
      -- EC: if {1}; first last.
      --     + by auto=> |> &1 &2; smt(size_ge0).
      stmt_if{1}; rotate_left
      --     (GAP 2: EC's `auto` knows `r <$ dout` lossless; ours leaves `bdistr`'s mass, and
      --     `smt_close` with it as a hint fails on an unknown free variable: `simp` first.  EC's
      --     `smt` selects `domE`, `valid_spec` and `<=`'s definition itself)
      · equiv_auto; simp only [bdistr_expected_one] at *
        smt_close [size_ge0, «<=», FMap.domE, valid_spec]
      -- EC: if {1}; first last.
      --     + by auto=> |> &1 &2; smt(prefix_ge0).
      stmt_if{1}; rotate_left
      · equiv_auto; smt_close [SLCommon.Prefix.prefix_ge0]
      -- EC: by auto=> |> &1 &2; smt(prefix_ge0 get_setE).
      --     (EC's `smt` selects `<=`'s definition, `mem_set`, `domE`, `valid_spec`, the `oget` of a
      --     known key itself)
      equiv_auto
      smt_close [SLCommon.Prefix.prefix_ge0, FMap.get_setE, «<=», FMap.mem_set, FMap.domE,
        valid_spec, get_eq_some_oget]
    -- EC: splitwhile{1}5: i + 1 < n;splitwhile{2}5: i + 1 < n.
    stmt_splitwhile{1} 5 : §i + 1 < §n
    stmt_splitwhile{2} 5 : §i + 1 < §n
    -- EC: rcondt{1}6;2:rcondt{2}6;auto.
    stmt_rcondt{1} 6
    on_goals 2 => stmt_rcondt{2} 6
    --     (EC's `auto` on the judgment: nothing to do here)
    -- EC: * by while(i < n);auto;sp;if;auto;sp;if;auto;if;auto.
    --     * by while(i < n);auto;sp;if;auto;sp;if;auto;if;auto.
    · intro σ; hoare_while (§i < §n)
      · hoare_auto
      · auto_close
      · hoare_auto
    · intro σ; hoare_while (§i < §n)
      · hoare_auto
      · auto_close
      · hoare_auto
    -- EC: rcondf{1}8;2:rcondf{2}8;auto.
    stmt_rcondf{1} 8
    on_goals 2 => stmt_rcondf{2} 8
    --     (EC's `auto` on the judgment: nothing to do here)
    -- EC: * while(i < n);auto.
    --         by sp;if;auto;sp;if;auto;if;auto.
    --       sp;if;auto;2:smt();if;auto;smt().
    --     * while(i < n);auto;2:smt();sp;if;auto;sp;if;auto;if;auto.
    --     (our `while` needs the loop last: `wp` over the unrolled round's head first)
    · intro σ; stmt_wp; hoare_while (§i < §n)
      · hoare_auto
      · auto_close
      · hoare_auto
    · intro σ; stmt_wp; hoare_while (§i < §n)
      · hoare_auto
      · auto_close
      · hoare_auto
    -- EC: rcondf{1}8;2:rcondf{2}8;auto.
    --     * while(i < n);auto.
    --         by sp;if;auto;sp;if;auto;if;auto.
    --       sp;if;auto;2:smt();if;auto;smt().
    --     * by while(i < n);auto;2:smt();sp;if;auto;sp;if;auto;if;auto.
    stmt_rcondf{1} 8
    on_goals 2 => stmt_rcondf{2} 8
    · intro σ; stmt_wp; hoare_while (§i < §n)
      · hoare_auto
      · auto_close
      · hoare_auto
    · intro σ; stmt_wp; hoare_while (§i < §n)
      · hoare_auto
      · auto_close
      · hoare_auto
    --     (EC's `auto` on the judgment: the unrolled round's head, after the loops)
    equiv_auto
    -- EC: conseq(:_==> ={b,lres,F.RO.m,S.paths,S.mi,S.m}
    --       /\ i{1} = n{1} - 1
    --       /\ SLCommon.C.c{1} <= C.c{1} + size bl{1} + i{1}
    --       /\ SLCommon.C.queries{1} <= F.RO.m{2});1:smt().
    equiv_conseq (: _ ==> ={b, lres, SLCommon.F.RO.m, S.paths, S.mi, S.m} ∧
      §i{1} = §n{1} - 1 ∧ §SLCommon.C.c{1} ≤ §C.c{1} + size §bl{1} + §i{1} ∧
      «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2})
    case post => auto_close
    -- EC: while(={lres,F.RO.m,S.paths,S.mi,S.m,i,n,p,nb,b,bl}
    --       /\ 0 <= i{1} <= n{1} - 1
    --       /\ SLCommon.C.queries.[format p (i+1)]{1} = Some b{1}
    --       /\ p{1} = bs{1} /\ valid p{1} /\ p{1} = bl{1}
    --       /\ C.c{1} + size p{1} + n{1} - 1 <= max_size
    --       /\ SLCommon.C.c{1} <= C.c{1} + size bl{1} + i{1}
    --       /\ SLCommon.C.queries{1} <= F.RO.m{2});progress.
    equiv_while (={lres, SLCommon.F.RO.m, S.paths, S.mi, S.m, i, n, p, nb, b, bl} ∧
      0 ≤ §i{1} ∧ §i{1} ≤ §n{1} - 1 ∧
      (§SLCommon.C.queries{1}).get (format §p{1} (§i{1} + 1)) = some §b{1} ∧
      §p{1} = §bs{1} ∧ valid §p{1} ∧ §p{1} = §bl{1} ∧
      §C.c{1} + size §p{1} + §n{1} - 1 ≤ max_size ∧
      §SLCommon.C.c{1} ≤ §C.c{1} + size §bl{1} + §i{1} ∧
      «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2})
    -- EC: sp;rcondt{1}1;2:rcondt{2}1;1,2:auto;sp.
    · stmt_sp; stmt_rcondt{1} 1
      on_goals 2 => stmt_rcondt{2} 1
      --     (GAP 3: EC's `auto`; after `sp` over the round's head, the test's reads
      --     (`Evaluatable.eval`) and the state's (`.get`) are generalized apart: `i < n` with
      --     nothing about `i`, `n`)
      · sorry
      · sorry
      stmt_sp
      -- EC: case((x0 \in F.RO.m){2});last first. … (the rest of the body)
      sorry
    -- EC: the code before the loop: sp;conseq(:_==> ={F.RO.m,b} … );progress. …
    sorry
  -- EC (the precondition, EC's `last first`): + progress.
  --   by move=>x;rewrite get_setE/=mem_set-mem_fdom fdom0 in_fset0//==>->.
  equiv_auto; auto_progress
  smt_close [FMap.get_setE, FMap.mem_set, FMap.mem_empty]

end GaudisCrypt.SHA3.Pilot.Gconcl_list
