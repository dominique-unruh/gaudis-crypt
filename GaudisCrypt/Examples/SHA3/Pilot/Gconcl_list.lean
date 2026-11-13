import GaudisCrypt.Examples.SHA3.Pilot.Gconcl
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl_list
import GaudisCrypt.Logic.ECProgress
import GaudisCrypt.Lib.EC.ListLemmas

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

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
* (GAP 3, fixed: after `sp`, `hoare_auto`'s `skip` simplifies the reads through writes before it
  generalizes the reads, so a test's reads and the precondition's are the same values.)
* EC's `have := prefix_le1 …` side goals (`move=> /> &hr …`): by hand, the hypotheses by
  `rename_i` on the context's tail or by type (`‹(0:ℤ) ≤ _›`); a hypothesis picked by a typed
  pattern of a read (`‹(localVarLens "p" _).get _ = _›`) may be spelled differently from the
  context's, and `omega` then sees two atoms: name it instead.
* EC's `smt` selects its lemmas (`domE`, `mem_set`, `valid_spec`, the definition of `<=`) itself:
  our `smt_close` lists them (deviation, not a gap).
* GAP 3: `glob M` of a concrete module in the `={…}` of `equiv_while`'s invariant stays a region
  (`FVP.fvP IF`), where EC reads the module's variables: the variables are written out.
* GAP 4: `equiv_conseq`'s frame takes a call of a procedure that writes nothing (`F.LRO.sample`,
  EC's `proc sample(x) = {}`) as writing its module's variables, and loses `F.RO.m` on that side:
  EC's following `inline*` is done first.
* GAP 5: EC's `call (: I)` on two different concrete procedures (`S(IF').f ~ S(Valid2).f`) has no
  one-condition form: `equiv_call (_ : ={arg, …} ==> ={res, …})` with the invariant's variables,
  then `equiv_proc` (EC's form opens the callees).  `equiv_call (_ : ={glob IF})` on the same
  concrete callee falls back to the frameless rule (no footprint bound for `IF`'s `init`):
  `={F.RO.m}`.
* GAP 6: the frame of `equiv_call (_ : P ==> Q)` is the callee module's (`S(F)`), not the
  procedure's: `S(F).fi` does not call `F`, but the call loses the oracles' maps, and the
  invariant on them is carried in `P` and `Q` (the callee by `sim (_ : inv)`).
* GAP 7: `hoare_conseq (: _ ==> Q)` and the Hoare `while` have no frame: their side goals know
  nothing of what the code keeps (EC's `conseq` quantifies over the modified variables only), so
  a fact about unmodified variables (`(p, n) = parse x`) is carried in `Q` and in the invariant.

* GAP 8: after `sp` over `sa, sc <- (sa +^ b, sc); x <- (sa, sc)` on both sides, the two `x` are
  known equal by their components only (`x{1}.1 = …`, `x{2}.1 = …`), and the closer does not put
  them together: the guard `x{1} \in Perm.m <=> x{2} \in Perm.m` and the goals after it start
  with `have hx : x₁ = x₂ := Prod.ext …`.
* GAP 9: the closer leaves the guard of a split loop, `(a && b) = true` or `= false`, as it is
  (also `decide p = !false`): `simp only [Bool.and_eq_true, …] at *; omega`.  No `seq` on a Hoare
  triple: in the `rcond` side goals our `auto` takes the code after the loop first.
* GAP 10: `splitwhile`'s condition reads the variables of the code left only: `p`, which is in
  the conditions alone, is written with its lens.
* GAP 11: `inline*` does not open a call of `Perm` behind the first port's `PRIMITIVE.view`
  (`RealIndif(Sponge, Perm, D)` applies `Sponge` to that view; a compatibility choice of
  `Flatten.moduleStep?` for the first port's proofs): `simp only [P_view]`, then `inline*`.
* GAP 12: `phoare_call` on an abstract module has the rule for lossless oracles (EC's
  `call (: true)`), not the one with an invariant (`call (: invm Perm.m Perm.mi)`,
  `Real_lossless`).
* GAP 13: in a `phoare … = 1` goal the tactics have no step for code after a loop (EC's `auto`
  passes samplings of lossless distributions and conditionals behind it; `Ideal_lossless`).
* After `sp`, a goal prints as the plain `prhlStmt` term until the next tactic (the conditions
  `x = e` it adds are not in read form); display only.
* EC's `List` lemmas the scripts cite (`take0`, `size_take`, `nth_take`, `size_cat`, `last_nseq`,
  …) were missing or in the first port's files under other names: `Lib/EC/ListLemmas.lean`.

From `Ideal_equiv_valid` on, the proofs are written on the strict tactics (`ec_auto`, `ec_close`,
`ec_progress`, `ec_prep`: `Logic/ECAutoStrict.lean`, `Logic/ECProgress.lean`); `ideal_equiv` is
on the older ones.
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
    --     (GAP 1: EC's `auto` on the guard; our closer does not use `(bl, nb) = x`)
    · intro σ₁ σ₂ h; simp_reads_all; smt_close []
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
    case post => smt_close []
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
      · hoare_auto; auto_close
      · hoare_auto; auto_close
      stmt_sp
      -- EC: case((x0 \in F.RO.m){2});last first.
      --     (EC's `x0` of the right's inlined `F.RO.get` is our `x2`)
      equiv_case (FMap.dom §SLCommon.F.RO.m{2} §x2{2})
      rotate_left
      -- EC: * rcondt{2}2;1:auto;rcondt{1}1.
      · stmt_rcondt{2} 2
        · hoare_auto
        stmt_rcondt{1} 1
        -- EC: + auto => /> &hr iR 9?; apply leq_nin_dom => //.
        --       by rewrite -size_eq0 size_cat size_nseq; smt(size_ge0).
        · hoare_auto; auto_prep
          refine leq_nin_dom _ _ _ ‹«<=» _ _› (format_ne_nil (valid_spec _ ‹_›) _) ?_
          simp_all
        -- EC: rcondt{1}1;1:auto.
        --     - move=> /> &hr i [#] h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
        --       have//= /#:= prefix_le1 bl{m} SLCommon.C.queries{hr} i h1 _.
        --       by rewrite domE h3.
        stmt_rcondt{1} 1
        · hoare_auto; auto_prep
          rename_i hw _ _ _ _ _ _ hq hbl
          have h := prefix_le1 _ _ _ hw
            ((FMap.domE _ _).mpr (by rw [hq]; exact Option.some_ne_none _))
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          have hsz := congrArg size hbl
          omega
        -- EC: sp;rcondt{1}2;auto;progress.
        stmt_sp; stmt_rcondt{1} 2
        · hoare_auto; auto_close
        --     - smt().
        --     - smt().
        --     - by rewrite!get_setE/=.
        --     (closed by `progress` already)
        equiv_auto; auto_progress
        --     - have//= /#:= prefix_le1 bl{2} SLCommon.C.queries{1} i_R H _.
        --       by rewrite domE H1.
        · rename_i hw _ _ _ _ _ _ _ hq _ _
          have h := prefix_le1 _ _ _ hw
            ((FMap.domE _ _).mpr (by rw [hq]; exact Option.some_ne_none _))
          omega
        --     - by rewrite!get_setE/= leq_add2//=.
        · smt_close [«<=», FMap.get_setE, FMap.mem_set, FMap.domE]
      -- EC: if{1}.
      stmt_if{1}
      -- EC: * rcondt{1}1;1:auto.
      --       - move=> /> &hr i [#] h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
      --         have//= /#:= prefix_le1 bl{m} SLCommon.C.queries{hr} i h1 _.
      --         by rewrite domE h3.
      · stmt_rcondt{1} 1
        · hoare_auto; auto_prep
          have h := prefix_le1 _ _ _ ‹(0:ℤ) ≤ _›
            ((FMap.domE _ _).mpr (by rw [‹FMap.get _ _ = some _›]; exact Option.some_ne_none _))
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          rename_i hbl _ _ _
          have hsz := congrArg size hbl
          omega
        -- EC: sp;rcondf{1}2;2:rcondf{2}2;auto;progress.
        stmt_sp; stmt_rcondf{1} 2
        on_goals 2 => stmt_rcondf{2} 2
        · hoare_auto; auto_close
        · hoare_auto; auto_close
        --     - smt().
        --     - smt().
        --     - by rewrite!get_setE/=.
        --     (closed by `progress` already)
        equiv_auto; auto_progress
        --     - have//= /#:= prefix_le1 bl{2} SLCommon.C.queries{1} i_R H _.
        --       by rewrite domE H1.
        · have h := prefix_le1 _ _ _ ‹(0:ℤ) ≤ _›
            ((FMap.domE _ _).mpr (by rw [‹FMap.get _ _ = some _›]; exact Option.some_ne_none _))
          omega
        --     - smt(leq_add_in domE).
        · exact leq_add_in _ _ _ ‹_› ‹_› _ ‹_› ‹_›
      -- EC: rcondf{2}2;auto;progress.
      stmt_rcondf{2} 2
      · hoare_auto
      --     - smt(size_cat size_nseq size_eq0 size_ge0).
      --     - smt().
      --     - smt().
      --     - by move: H11; rewrite domE; case: (SLCommon.C.queries{1}.[format bl{2} (i_R + 2)]).
      --     - smt().
      --     (two left after `progress`: the known entry's value, and its `oget`)
      equiv_auto; auto_progress
      · rename_i _ hqd _ _
        simp only [Bool.not_false, decide_eq_true_eq] at hqd
        rw [‹«<=» _ _› _ (format_ne_nil (valid_spec _ ‹_›) _) hqd]
      · rename_i _ hqd _ _
        simp only [Bool.not_false, decide_eq_true_eq] at hqd
        exact get_eq_some_oget hqd
    -- EC: sp;conseq(:_==> ={F.RO.m,b}
    --       /\ SLCommon.C.queries.[p]{1} = Some b{1}
    --       /\ SLCommon.C.c{1} <= C.c{1} + size bl{1}
    --       /\ SLCommon.C.queries{1} <= F.RO.m{2});progress.
    stmt_sp
    equiv_conseq (: _ ==> ={SLCommon.F.RO.m, b} ∧
      (§SLCommon.C.queries{1}).get §p{1} = some §b{1} ∧
      §SLCommon.C.c{1} ≤ §C.c{1} + size §bl{1} ∧
      «<=» §SLCommon.C.queries{1} §SLCommon.F.RO.m{2})
    --     - smt().
    --     - smt(nseq0 cats0).
    --     - smt(size_ge0).
    --     - smt().
    case post =>
      auto_progress
      all_goals smt_close [format_one, size_ge0]
    -- EC: case(p{2} \in F.RO.m{2}).
    equiv_case (FMap.dom §SLCommon.F.RO.m{2} §p{2})
    -- EC: + rcondf{2}2;1:auto.
    --       sp;if{1}.
    · stmt_rcondf{2} 2
      · hoare_auto
      --     (EC's `sp`: nothing to do here)
      stmt_if{1}
      -- EC: - rcondt{1}1;1:auto;1:smt(prefix_ge0).
      --       sp;rcondf{1}2;auto;progress.
      --       * by rewrite!get_setE/=.
      --       * smt(prefix_ge0).
      --       * smt(leq_add_in domE).
      · stmt_rcondt{1} 1
        · hoare_auto; smt_close [SLCommon.Prefix.prefix_ge0]
        stmt_sp; stmt_rcondf{1} 2
        · hoare_auto; smt_close []
        equiv_auto; auto_progress
        all_goals smt_close [FMap.get_setE, SLCommon.Prefix.prefix_ge0, leq_add_in, FMap.domE,
          «<=», FMap.mem_set, get_eq_some_oget, size_ge0, valid_spec]
      -- EC: auto;progress.
      --     - smt(domE).
      --     - smt(domE).
      --     - smt(size_ge0).
      equiv_auto; auto_progress
      all_goals smt_close [FMap.domE, size_ge0, «<=», valid_spec, get_eq_some_oget]
    -- EC: rcondt {1} 1.
    --     + by auto=> |> &0 /#.
    stmt_rcondt{1} 1
    · hoare_auto; smt_close [«<=», FMap.domE, valid_spec]
    -- EC: rcondt {1} 1.
    --     + by auto=> |> &0; smt(prefix_ge0).
    stmt_rcondt{1} 1
    · hoare_auto; smt_close [SLCommon.Prefix.prefix_ge0]
    -- EC: sp;auto;progress.
    --     + by rewrite!get_setE/=.
    --     + smt(prefix_ge0).
    --     + rewrite get_setE/= leq_add2//=.
    --     + by rewrite!get_setE/=.
    --     + smt(prefix_ge0).
    --     + exact leq_add_in.
    stmt_sp; equiv_auto; auto_progress
    all_goals smt_close [FMap.get_setE, SLCommon.Prefix.prefix_ge0, leq_add2, leq_add_in, «<=»,
      FMap.mem_set, FMap.domE, get_eq_some_oget, size_ge0, valid_spec]
  -- EC (the precondition, EC's `last first`): + progress.
  --   by move=>x;rewrite get_setE/=mem_set-mem_fdom fdom0 in_fset0//==>->.
  equiv_auto; auto_progress
  smt_close [FMap.get_setE, FMap.mem_set, FMap.mem_empty]

/-- EC's `local module (L (D : DISTINGUISHER) : F.RO_Distinguisher) (F : F.RO)`:
`proc distinguish = SLCommon.IdealIndif(IF'(F), S, A(D)).main` (an alias, so that `proc` opens
it; the old port's `L` is a `def`). -/
noncomputable abbrev L (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  SLCommon.IdealIndif (IF' F) S (A D)

/-- EC's `local module (L2 (D : DISTINGUISHER) : F.RO_Distinguisher) (F : F.RO)`:
`proc distinguish = SLCommon.IdealIndif(Valid2(F), S, A(D)).main`. -/
noncomputable abbrev L2 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  SLCommon.IdealIndif (Valid2 F) S (A D)

-- the oracles' three judgments, each through the inlined simulator and squeezing loop
set_option maxHeartbeats 4000000 in
/-- EC's `local equiv Ideal_equiv_valid (D <: DISTINGUISHER{-SLCommon.C, -C, -IF, -S}) :
L(D,F.LRO).distinguish ~ L2(D,F.LRO).distinguish : ={glob D} ==> ={glob D, res}`.

Deviations: EC's `call (: I)` on two different concrete procedures is `equiv_call (_ : ={arg, …}
==> ={res, …})` followed by `equiv_proc` (EC's form opens the callees itself); GAPs 3 and 4 of
the file header. -/
theorem Ideal_equiv_valid : ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S}),
    equiv[ L(D, SLCommon.F.LRO).distinguish ~ L2(D, SLCommon.F.LRO).distinguish :
      ={glob D} ==> ={glob D, res} ] := by
  intro D _
  -- EC: proc;inline*;sp;wp.
  equiv_proc; stmt_inline*; stmt_sp; stmt_wp
  -- EC: call(: ={glob S, glob C, glob F.RO});auto.
  equiv_call (_ : ={glob S, glob C, glob SLCommon.F.RO.asRO})
  on_goals 4 => ec_auto
  -- EC: + proc;sp;if;auto.
  · equiv_proc; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto
    -- EC: call(: ={glob S,glob F.RO});auto.
    equiv_call (_ : ={arg, S.m, S.mi, S.paths, SLCommon.F.RO.m} ==>
      ={res, S.m, S.mi, S.paths, SLCommon.F.RO.m})
    on_goals 2 => ec_auto
    --     (EC's `call (: I)` opens the callees)
    equiv_proc
    -- EC: sp;if;auto;if;auto;sp.
    --     (EC's first `sp`: nothing to do here)
    stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    --     (EC's `auto` on the branch: nothing to do here)
    stmt_sp
    -- EC: call(: ={glob F.RO});2:auto;2:smt().
    equiv_call (_ : ={arg, SLCommon.F.RO.m} ==> ={res, SLCommon.F.RO.m})
    on_goals 2 => (ec_auto; ec_close)
    --     (EC's `call (: I)` opens the callees)
    equiv_proc
    -- EC: inline F.LRO.sample;call(: ={glob IF});auto;progress.
    stmt_inline (SLCommon.F.LRO.sample)
    equiv_call (_ : ={SLCommon.F.RO.m})
    ec_auto
    -- EC: by while{1}(true)(n{1}-i{1});auto;smt().
    equiv_while{1} (True) ((§n{1} - §i{1}).toNat)
    · while_ll_phoare
      intro σ₂
      ec_auto
    · intro σ₂ k
      ec_auto
    ec_auto
  -- EC: + by proc;sim.
  · equiv_proc; sim
  -- EC: proc;sp;if;auto;sp;call(: ={glob IF,glob S});auto.
  equiv_proc; stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (EC's `auto` on the branch: nothing to do here)
  stmt_sp
  equiv_call (_ : ={arg, SLCommon.F.RO.m, S.m, S.mi, S.paths} ==>
    ={res, SLCommon.F.RO.m, S.m, S.mi, S.paths})
  on_goals 2 => (ec_auto; ec_close)
  --     (EC's `call (: I)` opens the callees)
  equiv_proc
  -- EC: sp;if;auto.
  stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (EC's `auto` on the branch: nothing to do here)
  -- EC: while(={glob S,glob IF,lres,i,n,p,b}).
  --     (GAP 3: `glob S`, `glob IF` in `while`'s `={…}` stay regions: their variables)
  equiv_while (={S.m, S.mi, S.paths, SLCommon.F.RO.m, lres, i, n, p, b})
  -- EC: + sp;if;auto.
  · stmt_sp; stmt_if
    · ec_close
    on_goals 2 => (ec_auto; ec_close)
    --     (EC's `auto` on the branch: nothing to do here)
    -- EC: call(: ={glob IF});auto.
    equiv_call (_ : ={arg, SLCommon.F.RO.m} ==> ={res, SLCommon.F.RO.m})
    on_goals 2 => (ec_auto; ec_close)
    --     (EC's `call (: I)` opens the callees)
    equiv_proc
    -- EC: call(: ={glob IF});auto.
    equiv_call (_ : ={SLCommon.F.RO.m})
    ec_auto
    -- EC: conseq(:_==> true);auto.
    --     (GAP 4: EC's `inline*` of the next line first — `conseq`'s frame does not see that
    --     `F.LRO.sample` writes nothing, and loses `F.RO.m` on the left)
    stmt_inline*
    equiv_conseq (: _ ==> True)
    case post => ec_close
    -- EC: by inline*;while{1}(true)(n{1}-i{1});auto;smt().
    equiv_while{1} (True) ((§n{1} - §i{1}).toNat)
    · while_ll_phoare
      intro σ₂
      ec_auto
    · intro σ₂ k
      ec_auto
    ec_auto
  -- EC: call(: ={glob IF});auto.
  equiv_call (_ : ={arg, SLCommon.F.RO.m} ==> ={res, SLCommon.F.RO.m})
  on_goals 2 => ec_auto
  --     (EC's `call (: I)` opens the callees)
  equiv_proc
  -- EC: call(: ={glob IF});auto.
  equiv_call (_ : ={SLCommon.F.RO.m})
  ec_auto
  -- EC: conseq(:_==> true);auto.
  --     (GAP 4: EC's `inline*` of the next line first)
  stmt_inline*
  equiv_conseq (: _ ==> True)
  case post => ec_close
  -- EC: by inline*;while{1}(true)(n{1}-i{1});auto;smt().
  equiv_while{1} (True) ((§n{1} - §i{1}).toNat)
  · while_ll_phoare
    intro σ₂
    ec_auto
  · intro σ₂ k
    ec_auto
  ec_auto

-- the oracles' three judgments, each through the inlined simulator and squeezing loop
set_option maxHeartbeats 4000000 in
/-- EC's `local equiv ideal_equiv2 (D <: DISTINGUISHER{-SLCommon.C, -C, -IF, -S}) :
L2(D,F.RO).distinguish ~ SLCommon.IdealIndif(IF,S,A(D)).main : ={glob D} ==> ={glob D, res}`.

Deviations: GAP 5 of the file header (EC's `call (: I)` on two concrete procedures).  EC's
`smt(parse_valid parseK formatK)` are closed without the lemmas. -/
theorem ideal_equiv2 : ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S}),
    equiv[ L2(D, SLCommon.F.RO.asRO).distinguish ~ SLCommon.IdealIndif(IF, S, A(D)).main :
      ={glob D} ==> ={glob D, res} ] := by
  intro D _
  -- EC: proc;inline*;sp;wp.
  equiv_proc; stmt_inline*; stmt_sp; stmt_wp
  -- EC: call(: ={glob F.RO, glob S, glob C});auto.
  equiv_call (_ : ={glob SLCommon.F.RO.asRO, glob S, glob C})
  on_goals 4 => ec_auto
  -- EC: + proc;auto;sp;if;auto.
  · equiv_proc; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto
    -- EC: call(: ={glob F.RO, glob S});auto.
    equiv_call (_ : ={arg, SLCommon.F.RO.m, S.m, S.mi, S.paths} ==>
      ={res, SLCommon.F.RO.m, S.m, S.mi, S.paths})
    on_goals 2 => ec_auto
    --     (EC's `call (: I)` opens the callees)
    equiv_proc
    -- EC: if; [1,3:by auto]; sim 2 2;if; auto.
    stmt_if
    · ec_close
    on_goals 2 => ec_auto
    sim 2 2
    stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto
    -- EC: call(: ={glob F.RO});2:auto.
    equiv_call (_ : ={arg, SLCommon.F.RO.m} ==> ={res, SLCommon.F.RO.m})
    on_goals 2 => ec_auto
    --     (EC's `call (: I)` opens the callees)
    equiv_proc
    -- EC: by inline*;sp;wp 2 2;sim.
    stmt_inline*; stmt_sp; stmt_wp 2 2
    sim
  -- EC: + by proc;sim.
  · equiv_proc; sim
  -- EC: proc;sp;if;auto;sp.
  equiv_proc; stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (EC's `auto` on the branch: nothing to do here)
  stmt_sp
  -- EC: call(: ={glob F.RO});auto;sp;if;auto;inline*;auto;sp.
  equiv_call (_ : ={arg, SLCommon.F.RO.m} ==> ={res, SLCommon.F.RO.m})
  on_goals 2 => (ec_auto; ec_close)
  --     (EC's `call (: I)` opens the callees)
  equiv_proc
  stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (EC's two `auto`s on the branch: nothing to do here)
  stmt_inline*; stmt_sp
  -- EC: case(0 < n{1});last first.
  equiv_case (0 < §n{1})
  rotate_left
  -- EC: + by rcondf{2}4;1:auto;rcondf{1}5;auto.
  · stmt_rcondf{2} 4
    · ec_auto
    stmt_rcondf{1} 5
    · ec_auto
    ec_auto
  -- EC: while(={lres,F.RO.m,i,n,p,b} /\ valid p{1} /\ 0 <= i{1} <= n{1}).
  equiv_while (={lres, SLCommon.F.RO.m, i, n, p, b} ∧ valid §p{1} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1})
  -- EC: + sp;if;1:auto.
  · stmt_sp; stmt_if
    · ec_close
    --     - by auto;smt(parse_valid parseK formatK).
    · ec_auto; ec_close
    --     by auto;smt(parse_valid parseK formatK).
    ec_auto; ec_close
  -- EC: by auto;smt(parse_valid parseK formatK).
  ec_auto; ec_close

/-- EC's `local module (L3 (D : DISTINGUISHER) : F.RO_Distinguisher) (F : F.RO)`:
`proc distinguish = SLCommon.IdealIndif(IF2(F,F2.RO), S, A(D)).main` (an alias; the old port's
`L3` is a `def`). -/
noncomputable abbrev L3 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) : procmod () → Bool :=
  SLCommon.IdealIndif (Module.app IF2 (Module.pair F F2.RO.asRO)) S (A D)

-- the oracles' three judgments; the functionality's is EC's 60 lines over both inlined loops
set_option maxHeartbeats 8000000 in
/-- EC's `local equiv Ideal_equiv3 (D <: DISTINGUISHER{-SLCommon.C, -C, -IF, -S, -F2.RO}) :
L(D,F.RO).distinguish ~ L3(D,F.RO).distinguish : ={glob D} ==> ={glob D, res}`.

Deviations: GAPs 5 and 6 of the file header.  EC's `smt(lemma1 lemma2 incl_dom parse_valid …)`
calls are closed by hand with those lemmas and the old port's `inv_L_L3.dom_valid`, `get_valid`,
`set_valid`, `dom_invalid`, `get_invalid` (the invariant on a query with a valid, or an invalid,
prefix); the hypotheses are taken by type. -/
theorem Ideal_equiv3 : ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S, -F2.RO}),
    equiv[ L(D, SLCommon.F.RO.asRO).distinguish ~ L3(D, SLCommon.F.RO.asRO).distinguish :
      ={glob D} ==> ={glob D, res} ] := by
  intro D _
  --     (EC's `parse_valid` for our `valid`, the decision of `valid_block`)
  have hparse : ∀ q : List block, valid q = true → parse q = (q, 1) := fun q h =>
    parse_valid q (by simpa [valid] using h)
  -- EC: proc;inline*;auto;sp.
  equiv_proc; stmt_inline*; ec_auto; stmt_sp
  -- EC: call(: ={glob S, glob C} /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});auto;first last.
  equiv_call (_ : ={glob S, glob C} ∧
    inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  rotate_left
  -- EC: + proc;sp;if;auto.
  --       by call(: ={glob S});auto;sim.
  · equiv_proc; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto
    --     (GAP 6: the frame of the call is the module's, `S(F)`, not the procedure's — `fi`
    --     does not call `F` — and loses the oracles' maps: the invariant is carried along)
    equiv_call (_ : ={arg, S.m, S.mi, S.paths} ∧
        inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2} ==>
      ={res, S.m, S.mi, S.paths} ∧ inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
    on_goals 2 => ec_auto
    --     (EC's `call (: I)` opens the callees)
    equiv_proc; sim (_ : inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  -- EC: + proc;sp;if;auto;call(: inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});auto;sp.
  · equiv_proc; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    --     (EC's `auto`: nothing to do here)
    equiv_call (_ : ={arg} ∧ inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2} ==>
      ={res} ∧ inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
    on_goals 2 => (ec_auto; ec_close)
    --     (EC's `call (: I)` opens the callees)
    equiv_proc; stmt_sp
    -- EC: inline*;if;auto;sp.
    stmt_inline*; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    --     (EC's `auto`: nothing to do here)
    stmt_sp
    -- EC: rcondt{1}1;1:auto;1:smt(parse_valid parseK formatK).
    stmt_rcondt{1} 1
    · ec_auto
    -- EC: rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK).
    stmt_rcondt{2} 1
    · ec_auto
    -- EC: rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK);sp.
    stmt_rcondt{2} 1
    · ec_auto
    stmt_sp
    -- EC: rcondf{1}3;1:auto;1:smt(parse_valid parseK formatK);sp.
    stmt_rcondf{1} 3
    · ec_auto
    -- EC: rcondf{2}3;1:auto;1:smt(parse_valid parseK formatK);sp.
    stmt_rcondf{2} 3
    · ec_auto
    -- EC: rcondf{1}5;2:rcondf{2}5;
    --       1,2:by auto;smt(mem_set nseq0 cats0 parse_valid).
    stmt_rcondf{1} 5
    on_goals 2 => stmt_rcondf{2} 5
    · ec_auto; smt_close [FMap.mem_set, format_one, parse_valid, valid]
    · ec_auto; smt_close [FMap.mem_set, format_one, parse_valid, valid]
    -- EC: case(0 < n{1});auto;last first.
    equiv_case (0 < §n{1})
    rotate_left
    -- EC: - rcondf{1}7;1:auto;rcondf{2}7;1:auto.
    · stmt_rcondf{1} 7
      · ec_auto
      stmt_rcondf{2} 7
      · ec_auto
      -- EC: by wp;rnd;auto;progress;smt(lemma1 nseq0 cats0 lemma2 incl_dom
      --       parse_valid parseK formatK in_fsetU).
      stmt_wp; equiv_rnd; ec_auto; ec_progress
      --     (EC's `smt`, by hand: `parse_valid` on the valid `p`, then one lemma per goal)
      all_goals
        have hpv : parse x₂.1 = (x₂.1, 1) :=
          parse_valid _ (by simpa [valid] using ‹valid x₂.1 = true›)
        simp only [hpv] at *
      · exact absurd (lemma2 _ _ _ _ _ ‹inv_L_L3 _ _ _› ‹valid _ = true› one_pos
          ‹FMap.dom m₁ _›) ‹¬ FMap.dom F_RO_m₂ _›
      · exact absurd ((incl_dom _ _ _ _ ‹inv_L_L3 _ _ _›).mpr (Or.inl ‹FMap.dom F_RO_m₂ _›))
          ‹¬ FMap.dom m₁ _›
      · exact lemma1 _ _ _ _ _ _ ‹inv_L_L3 _ _ _› ‹valid _ = true› one_pos ‹¬ FMap.dom m₁ _›
          ‹¬ FMap.dom F_RO_m₂ _›
    -- EC: while(={i,n,p,lres,b} /\ valid p{1} /\ 0 <= i{1} <= n{1}
    --       /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2}).
    equiv_while (={i, n, p, lres, b} ∧ valid §p{1} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ §n{1} ∧
      inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
    -- EC: - sp;if;1,3:auto=>/#.
    · stmt_sp; stmt_if
      · ec_close
      on_goals 2 => (ec_auto; ec_close)
      -- EC: sp;rcondt{2}1;1:auto;1:smt(parse_valid parseK formatK).
      stmt_sp; stmt_rcondt{2} 1
      · ec_auto; smt_close [parse_valid, parseK, formatK, valid]
      -- EC: conseq(:_==> ={b} /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});1:progress=>/#.
      equiv_conseq (: _ ==> ={b} ∧ inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
      case post => ec_close
      -- EC: auto=>/=.
      ec_auto
      -- EC: conseq(:_==> inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});progress.
      equiv_conseq (: _ ==> inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
      --     * by rewrite!get_setE//=.
      --     * smt(lemma1 parse_valid).
      --     * smt(lemma2 parse_valid).
      --     * smt(lemma2 parse_valid).
      --     * smt(incl_dom).
      --     * smt(incl_dom).
      --     * case:H8;smt(joinE).
      --     (EC's `smt`s by hand: the query `format p k` is valid, then the invariant's lemmas)
      case post =>
        ec_progress
        all_goals
          have hvf : ∀ k : ℤ, 0 < k → valid (parse (format p₂ k)).1 = true := fun k hk => by
            rw [parseK _ _ hk (by simpa [valid] using ‹valid p₂ = true›)]; assumption
          have hinv := ‹inv_L_L3 SLCommon_F_RO_m₁ SLCommon_F_RO_m₂ _›
        · exact congrArg oget (inv_L_L3.get_valid hinv (hvf _ (by omega)))
        · refine absurd ((inv_L_L3.dom_valid hinv (hvf _ ?_)).mp
            ‹FMap.dom SLCommon_F_RO_m₁ _›) ‹¬ FMap.dom SLCommon_F_RO_m₂ _›
          omega
        · refine absurd ((inv_L_L3.dom_valid hinv (hvf _ ?_)).mpr
            ‹FMap.dom SLCommon_F_RO_m₂ _›) ‹¬ FMap.dom SLCommon_F_RO_m₁ _›
          omega
        · refine absurd ((inv_L_L3.dom_valid hinv (hvf _ ?_)).mp
            ‹FMap.dom SLCommon_F_RO_m₁ _›) ‹¬ FMap.dom SLCommon_F_RO_m₂ _›
          omega
        · refine absurd ((inv_L_L3.dom_valid hinv (hvf _ ?_)).mpr
            ‹FMap.dom SLCommon_F_RO_m₂ _›) ‹¬ FMap.dom SLCommon_F_RO_m₁ _›
          omega
        · exact inv_L_L3.set_valid hinv (hvf _ (by omega)) _
      -- EC: while(={i1,n1,p1} /\ valid p1{1} /\ 0 <= i1{1} <= n1{1}
      --       /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2}).
      equiv_while (={i1, n1, p1} ∧ valid §p1{1} ∧ 0 ≤ §i1{1} ∧ §i1{1} ≤ §n1{1} ∧
        inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
      -- EC: * sp;conseq(:_==> inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});1:smt().
      · stmt_sp
        equiv_conseq (: _ ==> inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
        case post => ec_close
        -- EC: case(x6{1} \in F.RO.m{1}).
        equiv_case (FMap.dom §SLCommon.F.RO.m{1} §x6{1})
        -- EC: + by rcondf{1}2;2:rcondf{2}2;auto;smt(incl_dom lemma2).
        · stmt_rcondf{1} 2
          on_goals 2 => stmt_rcondf{2} 2
          · ec_auto
          · ec_auto; smt_close [incl_dom, lemma2]
          ec_auto; ec_close
        -- EC: by rcondt{1}2;2:rcondt{2}2;auto;smt(lemma2 incl_dom lemma1).
        stmt_rcondt{1} 2
        on_goals 2 => stmt_rcondt{2} 2
        · ec_auto
        --     (EC's `smt`, by hand)
        · ec_auto; ec_prep
          exact fun h => ‹¬ FMap.dom _ _› ((incl_dom _ _ _ _ ‹inv_L_L3 _ _ _›).mpr (Or.inl h))
        ec_auto; ec_prep
        exact lemma1 _ _ _ _ _ _ ‹inv_L_L3 _ _ _› ‹valid _ = true› (by omega) ‹¬ FMap.dom m₁ _›
          fun h => ‹¬ FMap.dom m₁ _› ((incl_dom _ _ _ _ ‹inv_L_L3 _ _ _›).mpr (Or.inl h))
      -- EC: by auto;smt(parseK).
      ec_auto; smt_close [parseK, valid]
    -- EC: wp;rnd;wp 2 2.
    stmt_wp; equiv_rnd; stmt_wp 2 2
    -- EC: conseq(:_==> F.RO.m{1}.[p{1}] = F.RO.m{2}.[p{2}]
    --       /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});progress.
    equiv_conseq (: _ ==> (§SLCommon.F.RO.m{1}).get §p{1} = (§SLCommon.F.RO.m{2}).get §p{2} ∧
      inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
    --     (EC's two `progress` goals: closed by `progress` already)
    case post => ec_progress
    -- EC: case(x5{1} \in F.RO.m{1}).
    --     (EC's `x5` of the left's inlined `F.RO.sample` is our `x2`)
    equiv_case (FMap.dom §SLCommon.F.RO.m{1} §x2{1})
    -- EC: - rcondf{1}2;2:rcondf{2}2;auto;progress.
    --       * smt(lemma2 incl_dom parse_valid).
    --       by have[]add_maps h1 h2:=H1;rewrite add_maps joinE//=;smt(parse_valid).
    --     (EC's `smt`s by hand: `parse_valid` on the valid `p`, then the invariant's lemmas)
    · stmt_rcondf{1} 2
      on_goals 2 => stmt_rcondf{2} 2
      · ec_auto
      · ec_auto; ec_prep
        have hpv := hparse _ ‹valid _ = true›
        simp only [hpv] at *
        simpa using lemma2 _ _ _ _ _ ‹inv_L_L3 _ _ _› ‹valid _ = true› one_pos ‹FMap.dom _ _›
      ec_auto; ec_progress
      exact inv_L_L3.get_valid ‹_› (by rw [hparse _ ‹valid x₂.1 = true›]; assumption)
    -- EC: rcondt{1}2;2:rcondt{2}2;auto;progress.
    --     - move:H4;rewrite/format/=nseq0 !cats0 => p0_notin_ROm_m.
    --       case: H1 => joint _ _; move: p0_notin_ROm_m.
    --       by rewrite joint mem_join negb_or; smt(parse_valid).
    --     - have[]add_maps h1 h2:=H1;rewrite add_maps !get_setE joinE//=;
    --       smt(parse_valid nseq0 cats0).
    --     - have:=H;rewrite -H0=>//=[][]->>->>;apply lemma1=>//=;1:smt(parse_valid).
    --       have[]add_maps h1 h2:=H1;smt(parse_valid formatK parseK incl_dom).
    stmt_rcondt{1} 2
    on_goals 2 => stmt_rcondt{2} 2
    · ec_auto
    · ec_auto; ec_prep
      have hpv := hparse _ ‹valid _ = true›
      simp only [hpv] at *
      exact fun h => ‹¬ FMap.dom _ _› ((incl_dom _ _ _ _ ‹inv_L_L3 _ _ _›).mpr (Or.inl h))
    ec_auto; ec_progress
    all_goals
      have hpv := hparse _ ‹valid x₂.1 = true›
      simp only [hpv, format_one] at *
    · simp [FMap.get_set_sameE]
    · have hn2 : ¬ FMap.dom F_RO_m₂ (format x₂.1 1) := fun h => ‹¬ FMap.dom m₁ _›
        ((incl_dom _ _ _ _ ‹inv_L_L3 _ _ _›).mpr (Or.inl (by simpa [format_one] using h)))
      simpa [format_one] using lemma1 _ _ _ x₂.1 1 a ‹inv_L_L3 _ _ _› ‹valid _ = true› one_pos
        (by simpa [format_one] using ‹¬ FMap.dom m₁ _›) hn2
  -- EC: + progress;split.
  --       - by apply/fmap_eqP=>x;rewrite joinE mem_empty.
  --       - smt(mem_empty).
  --       - smt(mem_empty).
  --     (the invariant on the empty maps: the old port's `inv_L_L3_empty`)
  · ec_auto; ec_progress
    exact inv_L_L3_empty
  -- EC: proc;sp;if;auto;call(: ={glob S} /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});auto.
  equiv_proc; stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  ec_auto
  equiv_call (_ : ={arg, S.m, S.mi, S.paths} ∧
      inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2} ==>
    ={res, S.m, S.mi, S.paths} ∧ inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  on_goals 2 => ec_auto
  --     (EC's `call (: I)` opens the callees)
  equiv_proc
  -- EC: if;1,3:auto.
  stmt_if
  · ec_close
  on_goals 2 => ec_auto
  -- EC: seq 1 1 : (={x, y1, S.paths, S.mi, S.m} /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});
  --     last first.
  equiv_seq 1 1 : (={x, y1, S.paths, S.mi, S.m} ∧
    inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  rotate_left
  -- EC: + by conseq(:_==> ={y, S.paths, S.mi, S.m});progress;sim.
  · equiv_conseq (: _ ==> ={y, S.paths, S.mi, S.m})
    case post => ec_progress
    sim
  -- EC: if;auto.
  stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (EC's `auto`: nothing to do here)
  -- EC: call(: inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});auto;sp;inline*.
  equiv_call (_ : ={arg} ∧ inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2} ==>
    ={res} ∧ inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  on_goals 2 => ec_auto
  --     (EC's `call (: I)` opens the callees)
  equiv_proc; stmt_sp; stmt_inline*
  -- EC: if{2}.
  stmt_if{2}
  -- EC: + seq 1 1 : (={x,p,n} /\ parse x{1} = (p,n){1} /\ valid p{1}
  --         /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});last first.
  · equiv_seq 1 1 : (={x, p, n} ∧ parse §x{1} = (§p{1}, §n{1}) ∧ valid §p{1} ∧
      inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
    rotate_left
    -- EC: - sp;case(x1{1} \in F.RO.m{1}).
    --     (EC's `x1` of the inlined `F.RO.get` is our `x2`)
    · stmt_sp
      equiv_case (FMap.dom §SLCommon.F.RO.m{1} §x2{1})
      -- EC: * rcondf{1}2;2:rcondf{2}2;auto;progress.
      --       + have:=H2;rewrite -formatK H/=;smt(lemma2 incl_dom parse_gt0).
      --       have[]add_maps h1 h2:=H1;rewrite add_maps joinE.
      --       have:=H2;rewrite -formatK H/==>in_dom1.
      --       case(format p{2} n{2} \in F2.RO.m{2})=>//=in_dom3.
      --       by have:=h2 _ in_dom3;rewrite parseK//=;smt(parse_gt0).
      --     (by hand: the invariant on a query with a valid prefix, `inv_L_L3.dom_valid`,
      --     `get_valid`, `set_valid` of the old port)
      · stmt_rcondf{1} 2
        on_goals 2 => stmt_rcondf{2} 2
        · ec_auto
        · ec_auto; ec_prep
          simpa using (inv_L_L3.dom_valid ‹inv_L_L3 _ _ _› ‹valid _ = true›).mp ‹FMap.dom _ _›
        ec_auto; ec_progress
        exact congrArg _ (inv_L_L3.get_valid ‹_› ‹valid _ = true›)
      -- EC: rcondt{1}2;2:rcondt{2}2;auto;progress.
      --     + smt(incl_dom lemma2).
      --     + have[]:=H1;smt(get_setE joinE).
      --     by have:=H2;rewrite-formatK H/==>nin_dom1;rewrite lemma1//=;
      --       smt(parse_gt0 lemma2 incl_dom).
      stmt_rcondt{1} 2
      on_goals 2 => stmt_rcondt{2} 2
      · ec_auto
      · ec_auto; ec_prep
        exact fun h => ‹¬ FMap.dom _ _›
          ((inv_L_L3.dom_valid ‹inv_L_L3 _ _ _› ‹valid _ = true›).mpr h)
      ec_auto; ec_progress
      exact inv_L_L3.set_valid ‹_› ‹valid _ = true› _
    -- EC: conseq(:_==> inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});1:smt().
    equiv_conseq (: _ ==> inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
    case post => ec_close
    -- EC: while(={i,n,p} /\ 0 <= i{1} /\ valid p{1} /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2}).
    equiv_while (={i, n, p} ∧ 0 ≤ §i{1} ∧ valid §p{1} ∧
      inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
    -- EC: + sp;case(x2{1} \in F.RO.m{1}).
    --     (EC's `x2` of the inlined `F.RO.sample` is our `x1`)
    · stmt_sp
      equiv_case (FMap.dom §SLCommon.F.RO.m{1} §x1{1})
      -- EC: - by rcondf{1}2;2:rcondf{2}2;auto;smt(lemma2).
      · stmt_rcondf{1} 2
        on_goals 2 => stmt_rcondf{2} 2
        · ec_auto
        · ec_auto; ec_prep
          simpa using lemma2 _ _ _ _ _ ‹inv_L_L3 _ _ _› ‹valid _ = true› (by omega)
            ‹FMap.dom _ _›
        ec_auto; ec_progress
      -- EC: rcondt{1}2;2:rcondt{2}2;auto;progress.
      --     - smt(incl_dom lemma1).
      --     - smt(incl_dom lemma1).
      --     apply/lemma1=> //=.
      --     - smt().
      --     smt(incl_dom mem_join).
      stmt_rcondt{1} 2
      on_goals 2 => stmt_rcondt{2} 2
      · ec_auto
      · ec_auto; ec_prep
        exact fun h => ‹¬ FMap.dom _ _› ((incl_dom _ _ _ _ ‹inv_L_L3 _ _ _›).mpr (Or.inl h))
      ec_auto; ec_progress
      exact lemma1 _ _ _ _ _ _ ‹inv_L_L3 _ _ _› ‹valid _ = true› (by omega) ‹¬ FMap.dom m₁ _›
        fun h => ‹¬ FMap.dom m₁ _› ((incl_dom _ _ _ _ ‹inv_L_L3 _ _ _›).mpr (Or.inl h))
    -- EC: auto;smt().
    ec_auto; ec_progress
  -- EC: seq 1 1 : (={x,p,n} /\ parse x{1} = (p,n){1} /\ ! valid p{1}
  --       /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});last first.
  equiv_seq 1 1 : (={x, p, n} ∧ parse §x{1} = (§p{1}, §n{1}) ∧ valid §p{1} = false ∧
    inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  rotate_left
  -- EC: + sp;case(x1{1} \in F.RO.m{1}).
  --     (by hand, as above: the invariant on a query with an invalid prefix,
  --     `inv_L_L3.dom_invalid`, `get_invalid` of the old port, and EC's `lemma3`)
  · stmt_sp
    equiv_case (FMap.dom §SLCommon.F.RO.m{1} §x2{1})
    -- EC: - rcondf{1}2;2:rcondf{2}2;auto;progress.
    --       * have[]:=H1;smt(incl_dom).
    --       have[]:=H1;smt(joinE incl_dom).
    · stmt_rcondf{1} 2
      on_goals 2 => stmt_rcondf{2} 2
      · ec_auto
      · ec_auto; ec_prep
        simpa using (inv_L_L3.dom_invalid ‹inv_L_L3 _ _ _› ‹valid _ = false›).mp ‹FMap.dom _ _›
      ec_auto; ec_progress
      exact congrArg _ (inv_L_L3.get_invalid ‹_› ‹valid _ = false›)
    -- EC: rcondt{1}2;2:rcondt{2}2;auto;progress.
    --     * have[]:=H1;smt(incl_dom).
    --     * have[]:=H1;smt(joinE incl_dom get_setE).
    --     by rewrite(lemma3 _ _ _ _ rL H1 _ H2)H//=.
    stmt_rcondt{1} 2
    on_goals 2 => stmt_rcondt{2} 2
    · ec_auto
    · ec_auto; ec_prep
      exact fun h => ‹¬ FMap.dom _ _›
        ((inv_L_L3.dom_invalid ‹inv_L_L3 _ _ _› ‹valid _ = false›).mpr h)
    ec_auto; ec_progress
    exact lemma3 _ _ _ _ _ ‹inv_L_L3 _ _ _› ‹valid _ = false› ‹¬ FMap.dom m₁ _›
  -- EC: conseq(:_==> inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2});1:smt().
  equiv_conseq (: _ ==> inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  case post => ec_close
  -- EC: while(={i,n,p,x} /\ 0 <= i{1} /\ ! valid p{1} /\ parse x{1} = (p,n){1}
  --       /\ inv_L_L3 F.RO.m{1} F.RO.m{2} F2.RO.m{2}).
  equiv_while (={i, n, p, x} ∧ 0 ≤ §i{1} ∧ valid §p{1} = false ∧ parse §x{1} = (§p{1}, §n{1}) ∧
    inv_L_L3 §SLCommon.F.RO.m{1} §SLCommon.F.RO.m{2} §F2.RO.m{2})
  -- EC: + sp;case(x2{1} \in F.RO.m{1}).
  · stmt_sp
    equiv_case (FMap.dom §SLCommon.F.RO.m{1} §x1{1})
    -- EC: - rcondf{1}2;2:rcondf{2}2;auto;progress.
    --       * have[]h_join h1 h2:=H2.
    --         have:= H5; rewrite h_join mem_join.
    --         have:= h1 (format p{hr} (i_R + 1)).
    --         have:=parse_not_valid x{hr}; rewrite H1 /= H0 /= => h.
    --         by rewrite (h (i_R+1)) /= => ->.
    --       smt().
    · stmt_rcondf{1} 2
      on_goals 2 => stmt_rcondf{2} 2
      · ec_auto
      · ec_auto; ec_prep
        simpa using (inv_L_L3.dom_invalid ‹inv_L_L3 _ _ _›
          (parse_not_valid _ ‹valid _ = false› _)).mp ‹FMap.dom _ _›
      ec_auto; ec_progress
    -- EC: rcondt{1}2;2:rcondt{2}2;auto;progress.
    --     * smt(incl_dom lemma1).
    --     * smt().
    --     * have//=:=lemma3 _ _ _ _ r0L H2 _ H5.
    --       by have:= parse_not_valid x{2}; rewrite H1 /= H0 /= => h; exact/(h (i_R+1)).
    stmt_rcondt{1} 2
    on_goals 2 => stmt_rcondt{2} 2
    · ec_auto
    · ec_auto; ec_prep
      exact fun h => ‹¬ FMap.dom _ _› ((inv_L_L3.dom_invalid ‹inv_L_L3 _ _ _›
        (parse_not_valid _ ‹valid _ = false› _)).mpr h)
    ec_auto; ec_progress
    exact lemma3 _ _ _ _ _ ‹inv_L_L3 _ _ _› (parse_not_valid _ ‹valid _ = false› _)
      ‹¬ FMap.dom m₁ _›
  -- EC: auto;smt().
  ec_auto; ec_progress

/-- EC's `local module L4 (D : DISTINGUISHER) (F : F.RO) (F2 : F2.RO)`:
`proc distinguish = IdealIndif(DSqueeze2(F,F2),S2,DValid(DRestr(D))).main` (an alias; the old
port's `L4` is a `def`). -/
noncomputable abbrev L4 (D : DISTINGUISHER) (F : SLCommon.F.RO_T) (F2 : F2.RO_T) :
    procmod () → Bool :=
  IdealIndif (Module.app DSqueeze2 (Module.pair F F2)) S2 (DValid (DRestr D))

set_option hygiene false in
/-- EC's `auto` and `by while(i < n);auto;2:smt();sp;if;auto;1:(sp;if;auto);while(i < n);auto.`,
the side goal of each `rcond` on the last round of `equiv_L3_L4`'s squeezing loop: the loop keeps
`i < n` (through the functionality's two inner loops).  (No hygiene: `§i`, `§n` are the program's
variables.) -/
local macro "l3l4_round" : tactic => `(tactic| (
  intro σ₂
  (try stmt_wp)
  hoare_while (§i < §n)
  · stmt_sp; stmt_if
    · stmt_sp; stmt_if
      · ec_auto; hoare_while (§i < §n)
        · ec_auto <;> ec_close
        · ec_close
        · ec_auto <;> ec_close
      · ec_auto; hoare_while (§i < §n)
        · ec_auto <;> ec_close
        · ec_close
        · ec_auto <;> ec_close
    · ec_auto <;> ec_close
  · ec_close
  · ec_auto <;> ec_close))

set_option hygiene false in
/-- EC's `auto` and `by while(i<n);auto;smt(parse_valid parse_gt0).`, the side goal of an `rcond`
on the last round of a sampling loop in `equiv_L3_L4`'s simulator oracle: the loop keeps `i < n`,
and `n` is positive (`parse_gt0`).  (No hygiene: `§i`, `§n` are the program's variables.) -/
local macro "l3l4_i_lt_n" : tactic => `(tactic| (
  intro σ
  (try ec_auto)
  hoare_while (§i < §n)
  · ec_auto <;> ec_close
  · first
    | ec_close
    | (ec_prep; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *; omega)
  · ec_auto; ec_prep
    first | exact parse_gt0 _ | omega))

-- the oracles' three judgments, over the two functionalities' inlined loops (EC's 120 lines)
set_option maxHeartbeats 16000000 in
/-- EC's `local equiv equiv_L3_L4 (D <: DISTINGUISHER{-SLCommon.C, -C, -IF, -S, -F2.RO, -BIRO.IRO,
-BIRO2.IRO}) : L3(D,F.RO).distinguish ~ L4(D,F.RO,F2.RO).distinguish : ={glob D} ==>
={glob D, res}`.

Deviations: GAPs 5 and 7 of the file header.  `S2(F)` is a wrapper of `S(Last(F))` in the old
declarations (exception E5), one call more than EC's alias: `stmt_inline{2} 0; stmt_sp` after
EC's `call` into the simulator.  EC's variables of inlined callees are named differently
(noted at each use).  EC's `smt` calls with `parse_gt0`, `parseK`, `formatK`, `parse_valid` are
by hand (`smt_close` fails on them with an unknown free variable, GAP 2); the two loop side goals
EC repeats are the local macros `l3l4_round` and `l3l4_i_lt_n`. -/
theorem equiv_L3_L4 :
    ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S, -F2.RO, -BIRO.IRO, -BIRO2.IRO}),
    equiv[ L3(D, SLCommon.F.RO.asRO).distinguish ~
      L4(D, SLCommon.F.RO.asRO, F2.RO.asRO).distinguish : ={glob D} ==> ={glob D, res} ] := by
  intro D _
  --     (EC's `parse_valid` for our `valid`, the decision of `valid_block`)
  have hparse : ∀ q : List block, valid q = true → parse q = (q, 1) := fun q h =>
    parse_valid q (by simpa [valid] using h)
  -- EC: proc; inline*; auto; sp.
  equiv_proc; stmt_inline*; ec_auto; stmt_sp
  -- EC: call(: ={glob S, glob C, glob F.RO, glob F2.RO}); auto;first last.
  equiv_call (_ : ={glob S, glob C, glob SLCommon.F.RO.asRO, glob F2.RO.asRO})
  on_goals 4 => ec_auto
  rotate_left
  -- EC: + by proc; sim.
  · equiv_proc; sim
  -- EC: + proc; sp; if; auto; call(: ={glob F.RO, glob F2.RO}); auto; sp; if; auto; inline*; sp.
  · equiv_proc; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    --     (EC's `auto`: nothing to do here)
    equiv_call (_ : ={arg, SLCommon.F.RO.m, F2.RO.m} ==> ={res, SLCommon.F.RO.m, F2.RO.m})
    on_goals 2 => (ec_auto; ec_close)
    --     (EC's `call (: I)` opens the callees)
    equiv_proc; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    --     (EC's `auto`: nothing to do here)
    stmt_inline*; stmt_sp
    -- EC: rcondt{1}1; 1:(auto; smt(parse_valid parse_gt0)); sp.
    stmt_rcondt{1} 1
    · ec_auto
    --     (EC's `sp`: nothing to do here)
    -- EC: rcondt{1}1; 1:(auto; smt(parse_valid parse_gt0)); sp.
    stmt_rcondt{1} 1
    · ec_auto
    stmt_sp
    -- EC: rcondf{1}3; 1:(auto; smt(parse_valid parse_gt0)); sp.
    stmt_rcondf{1} 3
    · ec_auto
    --     (EC's `sp`: nothing to do here)
    -- EC: rcondt{2}1; 1:(auto; smt(parse_valid parse_gt0 parseK formatK)); sp; wp.
    stmt_rcondt{2} 1
    · ec_auto
    --     (EC's `sp`: nothing to do here)
    stmt_wp
    -- EC: if{2};sp.
    stmt_if{2} <;> stmt_sp
    -- EC: - rcondf{2}3; 1:(auto; smt(parse_valid parse_gt0)); sp.
    · stmt_rcondf{2} 3
      · ec_auto
      --     (EC's `sp`: nothing to do here)
      -- EC: rcondf{1}8; 1:(auto; smt(parse_valid parse_gt0)); sp.
      stmt_rcondf{1} 8
      · ec_auto; ec_close
      --     (EC's `sp`: nothing to do here)
      -- EC: rcondf{1}5; 1:(auto; smt(parse_valid parse_gt0 mem_set nseq0 cats0)); sp.
      stmt_rcondf{1} 5
      · ec_auto; smt_close [FMap.mem_set, format_one, parse_valid, valid]
      --     (EC's `sp`: nothing to do here)
      -- EC: wp 4 2;rnd{1};wp 2 2.
      stmt_wp 4 2; equiv_rnd{1}; stmt_wp 2 2
      -- EC: by conseq(:_==> ={F.RO.m} /\ r3{1} = r2{2} /\ x9{1} = x4{2});2:sim;
      --       smt(DBlock.dunifin_ll nseq0 cats0 parse_valid);progress.
      --     (EC's `r3`, `x9` on the left and `r2`, `x4` on the right are our `r0`, `x2`)
      equiv_conseq (: _ ==> ={SLCommon.F.RO.m} ∧ §r0{1} = §r0{2} ∧ §x2{1} = §x2{2})
      case post => ec_progress
      --     (EC's `smt` on what `sim` leaves: the two keys are the valid `p`)
      sim
      smt_close [format_one, parse_valid, valid]
    -- EC: rcondt{2}1; 1:(auto; smt(parse_valid parse_gt0)); sp; wp.
    stmt_rcondt{2} 1
    · ec_auto
    stmt_sp
    --     (EC's `wp`: nothing to do here)
    -- EC: splitwhile{1} 8 : i + 1 < n.
    stmt_splitwhile{1} 8 : §i + 1 < §n
    -- EC: rcondt{1}9;1:auto.
    stmt_rcondt{1} 9
    --     - by while(i < n);auto;2:smt();sp;if;auto;1:(sp;if;auto);while(i < n);auto.
    · l3l4_round
    -- EC: rcondf{1}11;1:auto.
    --     - by while(i < n);auto;2:smt();sp;if;auto;1:(sp;if;auto);while(i < n);auto.
    stmt_rcondf{1} 11
    · l3l4_round
    -- EC: rcondf{1}11;1:auto.
    --     - by while(i < n);auto;2:smt();sp;if;auto;1:(sp;if;auto);while(i < n);auto.
    stmt_rcondf{1} 11
    · l3l4_round
    -- EC: wp.
    stmt_wp
    -- EC: while((n,p){1} = (n0,p0){2} /\ i{1} + 1 = i{2} /\ valid p{1} /\ 0 < n{1}
    --       /\ 0 <= i{2} <= n{1}
    --       /\ (forall j, 1 <= j <= i{2} => format p{1} j \in F.RO.m{1})
    --       /\ rcons lres{1} b{1} = lres{2} /\ ={F.RO.m, F2.RO.m});last first.
    --     (EC's `i`, `lres` on the right are our `i0`, `lres0`)
    equiv_while ((§n{1}, §p{1}) = (§n0{2}, §p0{2}) ∧ §i{1} + 1 = §i0{2} ∧ valid §p{1} ∧
      0 < §n{1} ∧ 0 ≤ §i0{2} ∧ §i0{2} ≤ §n{1} ∧
      (∀ j : ℤ, 1 ≤ j ∧ j ≤ §i0{2} → FMap.dom §SLCommon.F.RO.m{1} (format §p{1} j)) ∧
      rcons §lres{1} §b{1} = §lres0{2} ∧ ={SLCommon.F.RO.m, F2.RO.m})
    rotate_left
    -- EC: - rcondf{1}5;1:auto;1:smt(mem_set nseq0 cats0 parse_valid).
    · stmt_rcondf{1} 5
      · ec_auto; smt_close [FMap.mem_set, format_one, parse_valid, valid]
      -- EC: wp 4 2;rnd{1};wp 2 2.
      stmt_wp 4 2; equiv_rnd{1}; stmt_wp 2 2
      -- EC: conseq(:_==> ={F.RO.m} /\ r3{1} = r0{2} /\ x9{1} \in F.RO.m{1});
      --       1:smt(DBlock.dunifin_ll nseq0 cats0 parse_valid).
      --     (EC's `r3`, `x9` on the left are our `r0`, `x2`; `r0` on the right our `r1`)
      equiv_conseq (: _ ==> ={SLCommon.F.RO.m} ∧ §r0{1} = §r1{2} ∧
        FMap.dom §SLCommon.F.RO.m{1} §x2{1})
      case post =>
        ec_progress
        all_goals smt_close [format_one, parse_valid, valid]
      -- EC: by auto;smt(parse_valid nseq0 cats0 mem_set).
      ec_auto; ec_progress
      smt_close [FMap.mem_set]
    -- EC: sp.
    stmt_sp
    -- EC: rcondt{1}1;1:auto;sp.
    stmt_rcondt{1} 1
    · ec_auto; ec_close
    stmt_sp
    -- EC: rcondt{1}1;1:(auto;smt(parse_valid parseK formatK)).
    stmt_rcondt{1} 1
    · ec_auto; smt_close [parse_valid, parseK, formatK, valid]
    -- EC: splitwhile{1} 1 : i1 + 1 < n1.
    stmt_splitwhile{1} 1 : §i1 + 1 < §n1
    -- EC: rcondt{1}2;1:auto.
    --     - by while(i1 < n1);auto;smt(parse_gt0 parse_valid parseK formatK).
    stmt_rcondt{1} 2
    · intro σ₂
      hoare_while (§i1 < §n1)
      · ec_auto
      · ec_close
      · ec_auto; ec_prep; exact parse_gt0 _
    -- EC: rcondf{1}7;1:auto.
    --     - by while(i1 < n1);auto;smt(parse_gt0 parse_valid parseK formatK).
    stmt_rcondf{1} 7
    · intro σ₂
      ec_auto
      hoare_while (§i1 < §n1)
      · ec_auto
      · ec_close
      · ec_auto; ec_prep; exact parse_gt0 _
    -- EC: rcondf{1}9;1:auto.
    --     - conseq(:_==> i1 + 1 = n1);1:smt(mem_set parseK parse_valid formatK).
    --       by while(i1 + 1 <= n1);auto;smt(parse_gt0 parse_valid parseK formatK).
    stmt_rcondf{1} 9
    · intro σ₂
      ec_auto
      --     (GAP 7: `hoare_conseq` has no frame — what the loop keeps, `(p1, n1) = parse x7`, is
      --     carried in the new postcondition and in the invariant)
      hoare_conseq (: _ ==> §i1 + 1 = §n1 ∧ (§p1, §n1) = parse §x7)
      case post =>
        ec_prep
        rw [‹i1 + 1 = _›, formatK]
        split_ifs <;> simp_all [FMap.mem_set]
      hoare_while (§i1 + 1 ≤ §n1 ∧ (§p1, §n1) = parse §x7)
      · ec_auto
      · ec_prep; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *; omega
      · ec_auto; ec_prep
        exact Int.add_one_le_iff.mpr (parse_gt0 _)
    -- EC: wp 8 2;rnd{1};wp 6 2.
    stmt_wp 8 2; equiv_rnd{1}; stmt_wp 6 2
    -- EC: conseq(:_==> n1{1} = i{2} /\ ={F.RO.m} /\ i1{1} = n1{1}
    --       /\ (forall (j : int), 1 <= j <= i{2} =>
    --            format p1{1} j \in F.RO.m{1}));
    --     1:smt(parseK formatK parse_valid DBlock.dunifin_ll).
    --     (EC's `i` on the right is our `i0`)
    equiv_conseq (: _ ==> §n1{1} = §i0{2} ∧ ={SLCommon.F.RO.m} ∧ §i1{1} = §n1{1} ∧
      (∀ j : ℤ, 1 ≤ j ∧ j ≤ §i0{2} → FMap.dom §SLCommon.F.RO.m{1} (format §p1{1} j)))
    --     (EC's `smt`, by hand: `smt_close` with these hints fails on an unknown free variable,
    --     GAP 2)
    case post =>
      ec_progress
      · exact bdistr_expected_one
      · have h := ‹∀ j : ℤ, 1 ≤ j ∧ j ≤ _ + 1 + 1 → FMap.dom SLCommon_F_RO_m₂ _› j
          ⟨‹1 ≤ j›, ‹j ≤ _›⟩
        rwa [parseK _ _ (by omega) (by simpa [valid] using ‹valid p0₂1 = true›)] at h
      · rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    -- EC: seq 2 0 : (={F.RO.m,x0} /\ i1{1} = n1{1} /\ x0{2} = format p{1} i{2}
    --       /\ n1{1} = i{1} + 1 /\ p1{1} = p{1} /\ i{2} = i{1} + 1 /\ forall (j : int),
    --         1 <= j <= i{1} => format p{1} j \in F.RO.m{1});last first.
    --     (EC's `x0` is the functionality's argument on the left, our `x7`, and the oracle's on
    --     the right, our `x3`; EC's `i` on the right is our `i0`)
    equiv_seq 2 0 : (={SLCommon.F.RO.m} ∧ §x7{1} = §x3{2} ∧ §i1{1} = §n1{1} ∧
      §x3{2} = format §p{1} §i0{2} ∧ §n1{1} = §i{1} + 1 ∧ §p1{1} = §p{1} ∧ §i0{2} = §i{1} + 1 ∧
      (∀ j : ℤ, 1 ≤ j ∧ j ≤ §i{1} → FMap.dom §SLCommon.F.RO.m{1} (format §p{1} j)))
    rotate_left
    -- EC: - auto;smt(mem_set).
    --     (EC's `smt`, by hand: `j` is at most `i`, or the new key)
    · ec_auto; ec_progress
      all_goals
        have hj : j ≤ i₁ ∨ j = i₁ + 1 := by omega
      · rcases hj with h | rfl
        · exact ‹∀ j : ℤ, 1 ≤ j ∧ j ≤ i₁ → FMap.dom m₂ (format p1₁ j)› j ⟨‹1 ≤ j›, h⟩
        · assumption
      · rw [FMap.mem_set]
        rcases hj with h | rfl
        · exact Or.inl (‹∀ j : ℤ, 1 ≤ j ∧ j ≤ i₁ → FMap.dom m₂ (format p1₁ j)› j ⟨‹1 ≤ j›, h⟩)
        · exact Or.inr rfl
    -- EC: wp;conseq(:_==> ={F.RO.m} /\ i1{1} + 1 = n1{1}
    --       /\ (forall (j : int), 1 <= j < n1{1} =>
    --           format p1{1} j \in F.RO.m{1}));1:smt(parseK).
    stmt_wp
    equiv_conseq (: _ ==> ={SLCommon.F.RO.m} ∧ §i1{1} + 1 = §n1{1} ∧
      (∀ j : ℤ, 1 ≤ j ∧ j < §n1{1} → FMap.dom §SLCommon.F.RO.m{1} (format §p1{1} j)))
    --     (EC's `smt(parseK)`, by hand)
    case post =>
      ec_progress
      · have h := ‹i1₁1 + 1 = _›
        rw [parseK] at h
        exacts [h, by omega, by simpa [valid] using ‹valid p₁1 = true›]
      · rw [parseK]
        all_goals first | rfl | omega | (simpa [valid] using ‹valid p₁1 = true›)
    -- EC: while{1}(={F.RO.m} /\ 0 <= i1{1} /\ i1{1} + 1 <= n1{1} /\ i{2} = n1{1} /\ i{2} = i{1} + 1
    --       /\ (forall (j : int), 1 <= j < n1{1} =>
    --           format p1{1} j \in F.RO.m{1}))(n1{1}-i1{1}-1);progress.
    equiv_while{1} (={SLCommon.F.RO.m} ∧ 0 ≤ §i1{1} ∧ §i1{1} + 1 ≤ §n1{1} ∧ §i0{2} = §n1{1} ∧
      §i0{2} = §i{1} + 1 ∧
      (∀ j : ℤ, 1 ≤ j ∧ j < §n1{1} → FMap.dom §SLCommon.F.RO.m{1} (format §p1{1} j)))
      ((§n1{1} - §i1{1} - 1).toNat)
    -- EC: + by sp;rcondf 2;auto;smt(DBlock.dunifin_ll).
    --     (the key of this round is among those already sampled: by hand)
    · while_ll_phoare
      intro σ₂
      ec_auto
    · intro σ₂ k
      stmt_sp; stmt_rcondf 2
      · ec_auto; ec_prep
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_false] at *
        apply_assumption; constructor <;> omega
      ec_auto; ec_progress
      simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega
    -- EC: by auto;smt(parse_gt0 parseK formatK parse_valid).
    --     (EC's `smt`, by hand: `parseK` on the valid `p`, then arithmetic)
    ec_auto; ec_progress
    all_goals
      have hK : ∀ k : ℤ, 0 < k → parse (format p0₂ k) = (p0₂, k) := fun k hk =>
        parseK _ _ hk (by simpa [valid] using ‹valid p0₂ = true›)
      simp (disch := omega) only [hK] at *
    all_goals first
      | omega
      | (simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *; omega)
      | (apply_assumption; constructor <;> omega)
  -- EC: proc; sp; if; auto; call(: ={glob S, glob F.RO, glob F2.RO}); auto.
  equiv_proc; stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  ec_auto
  equiv_call (_ : ={arg, S.m, S.mi, S.paths, SLCommon.F.RO.m, F2.RO.m} ==>
    ={res, S.m, S.mi, S.paths, SLCommon.F.RO.m, F2.RO.m})
  on_goals 2 => ec_auto
  --     (EC's `call (: I)` opens the callees)
  equiv_proc
  --     (E5: `S2(F)` is a wrapper of `S(Last(F))` here, one call more than EC's alias)
  stmt_inline{2} 0; stmt_sp
  -- EC: if; [1,3:by auto]; sim 1 1; if; auto; sim 2 2; sp.
  stmt_if
  · ec_close
  on_goals 2 => ec_auto
  sim 1 1
  stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (EC's `auto`: nothing to do here)
  stmt_sp
  -- EC: call(: ={glob F.RO, glob F2.RO});auto;last smt().
  equiv_call (_ : ={arg, SLCommon.F.RO.m, F2.RO.m} ==> ={res, SLCommon.F.RO.m, F2.RO.m})
  on_goals 2 => (ec_auto; ec_close)
  --     (EC's `call (: I)` opens the callees)
  equiv_proc
  -- EC: inline*;auto;sp.
  stmt_inline*; ec_auto; stmt_sp
  -- EC: if;1:auto;1:smt().
  stmt_if
  · ec_close
  -- EC: + rcondf{2}1;1:(auto;smt(parse_valid parse_gt0)).
  · stmt_rcondf{2} 1
    · ec_auto; ec_prep; exact parse_gt0 _
    -- EC: splitwhile{1} 1 : i + 1 < n;splitwhile{2} 1 : i + 1 < n.
    stmt_splitwhile{1} 1 : §i + 1 < §n
    stmt_splitwhile{2} 1 : §i + 1 < §n
    -- EC: rcondt{1}2;1:auto.
    --     - by while(i<n);auto;smt(parse_valid parse_gt0).
    stmt_rcondt{1} 2
    · l3l4_i_lt_n
    -- EC: rcondt{2}2;1:auto.
    --     - by while(i<n);auto;smt(parse_valid parse_gt0).
    stmt_rcondt{2} 2
    · l3l4_i_lt_n
    -- EC: rcondf{1}7;1:auto.
    --     - by while(i<n);auto;smt(parse_valid parse_gt0).
    stmt_rcondf{1} 7
    · l3l4_i_lt_n
    -- EC: rcondf{2}8;1:auto.
    --     - by while(i<n);auto;smt(parse_valid parse_gt0).
    stmt_rcondf{2} 8
    · l3l4_i_lt_n
    -- EC: rcondf{1}9;1:auto.
    --     - by while(i+1<=n);auto;
    --       smt(parse_valid parse_gt0 parseK mem_set formatK).
    --     (GAP 7: no frame in the Hoare `while`: `(p, n) = parse x` is carried in the invariant)
    stmt_rcondf{1} 9
    · intro σ₂
      ec_auto
      hoare_while (§i + 1 ≤ §n ∧ (§p, §n) = parse §x)
      · ec_auto
      · ec_prep
        have hi : i + 1 = (parse x).2 := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *; omega
        rw [hi, formatK]
        split_ifs <;> simp_all [FMap.mem_set]
      · ec_auto; ec_prep
        exact Int.add_one_le_iff.mpr (parse_gt0 _)
    -- EC: wp 8 5;rnd{1};wp 6 5.
    stmt_wp 8 5; equiv_rnd{1}; stmt_wp 6 5
    -- EC: conseq(:_==> ={F.RO.m} /\ p{2} = x0{2});progress.
    --     + smt(last_rcons formatK parseK).
    --     (EC's `x0` on the right, the oracle's argument, is our `x3`)
    equiv_conseq (: _ ==> ={SLCommon.F.RO.m} ∧ §p{2} = §x3{2})
    case post =>
      ec_progress
      simp [last, rcons]
    -- EC: seq 3 3 : (={F.RO.m,i,x0} /\ x0{1} = p{2});
    --       last by conseq(:_==> ={F.RO.m});progress;sim.
    --     (the left's `x0`, a `List block`, is written with its type: the right has an `x0` of
    --     another type)
    equiv_seq 3 3 : (={SLCommon.F.RO.m, i} ∧ §(localVarLens "x0" (List block)){1} = §x3{2} ∧
      §(localVarLens "x0" (List block)){1} = §p{2})
    rotate_left
    · equiv_conseq (: _ ==> ={SLCommon.F.RO.m})
      case post => ec_progress
      sim
    -- EC: auto;conseq(:_==> ={F.RO.m,i,n} /\ p{1} = p0{2} /\ i{1} + 1 = n{2});1:smt(formatK).
    ec_auto
    equiv_conseq (: _ ==> ={SLCommon.F.RO.m, i, n} ∧ §p{1} = §p0{2} ∧ §i{1} + 1 = §n{2})
    case post =>
      ec_progress
      rw [‹i₂1 + 1 = _›, formatK]
    -- EC: by while(={F.RO.m,i,n} /\ p{1} = p0{2} /\ 0 <= i{1} /\ i{1} + 1 <= n{2});
    --       auto;smt(parse_gt0).
    equiv_while (={SLCommon.F.RO.m, i, n} ∧ §p{1} = §p0{2} ∧ 0 ≤ §i{1} ∧ §i{1} + 1 ≤ §n{2})
    · ec_auto; ec_progress
    ec_auto; ec_progress
    · exact Int.add_one_le_iff.mpr (parse_gt0 _)
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *; omega
  -- EC: sp;rcondf{2}1;1:(auto;smt(parse_gt0)).
  --     (EC's `sp`: nothing to do here)
  stmt_rcondf{2} 1
  · ec_auto; ec_prep; exact parse_gt0 _
  -- EC: rcondf{2}1;1:auto;1:smt(parseK formatK).
  stmt_rcondf{2} 1
  · ec_auto; ec_prep; rw [formatK]; omega
  -- EC: splitwhile{1} 1 : i + 1 < n;splitwhile{2} 1 : i + 1 < n.
  stmt_splitwhile{1} 1 : §i + 1 < §n
  stmt_splitwhile{2} 1 : §i + 1 < §n
  -- EC: rcondt{1}2;1:auto.
  --     - by while(i<n);auto;smt(parse_valid parse_gt0).
  stmt_rcondt{1} 2
  · l3l4_i_lt_n
  -- EC: rcondt{2}2;1:auto.
  --     - while(i<n);auto;-1:smt(parse_valid parse_gt0).
  stmt_rcondt{2} 2
  · l3l4_i_lt_n
  -- EC: rcondf{1}7;1:auto.
  --     - by while(i<n);auto;smt(parse_valid parse_gt0).
  stmt_rcondf{1} 7
  · l3l4_i_lt_n
  -- EC: rcondf{2}8;1:auto.
  --     - by while(i<n);auto;smt(parse_valid parse_gt0).
  stmt_rcondf{2} 8
  · l3l4_i_lt_n
  -- EC: rcondf{1}9;1:auto.
  --     - by while(i+1<=n);auto;
  --       smt(parse_valid parse_gt0 parseK mem_set formatK).
  --     (GAP 7, as above)
  stmt_rcondf{1} 9
  · intro σ₂
    ec_auto
    hoare_while (§i + 1 ≤ §n ∧ (§p, §n) = parse §x)
    · ec_auto
    · ec_prep
      have hi : i + 1 = (parse x).2 := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *; omega
      rw [hi, formatK]
      split_ifs <;> simp_all [FMap.mem_set]
    · ec_auto; ec_prep
      exact Int.add_one_le_iff.mpr (parse_gt0 _)
  -- EC: wp 8 5;rnd{1};wp 6 5.
  stmt_wp 8 5; equiv_rnd{1}; stmt_wp 6 5
  -- EC: conseq(:_==> ={F2.RO.m} /\ format pp{2} n{2} = x3{2}).
  --     + move=> /> &1 &2 H H0 /= /> [#] H1 H2 m lres /= ?.
  --       smt(last_rcons formatK parseK).
  --     (EC's `x3` on the right, the oracle's argument, is our `x8`)
  equiv_conseq (: _ ==> ={F2.RO.m} ∧ format §pp{2} §n{2} = §x8{2})
  case post =>
    ec_progress
    simp [formatK, last, rcons]
  -- EC: seq 3 3 : (={F2.RO.m,i} /\ x2{1} = x3{2} /\ pp{2} = p{1} /\ format pp{2} n{2} = x3{2});
  --       last by conseq(:_==> ={F2.RO.m});progress;sim.
  --     (EC's `x2` on the left is our `x3`)
  equiv_seq 3 3 : (={F2.RO.m, i} ∧ §x3{1} = §x8{2} ∧ §pp{2} = §p{1} ∧
    format §pp{2} §n{2} = §x8{2})
  rotate_left
  · equiv_conseq (: _ ==> ={F2.RO.m})
    case post => ec_progress
    sim
  -- EC: auto;conseq(:_==> ={F2.RO.m,i,n} /\ i{1} + 1 = n{2});1:smt(formatK).
  ec_auto
  equiv_conseq (: _ ==> ={F2.RO.m, i, n} ∧ §i{1} + 1 = §n{2})
  case post =>
    ec_progress
    all_goals simp only [formatK]
  -- EC: by while(={F2.RO.m,i,n} /\ p{1} = pp{2} /\ 0 <= i{1} /\ i{1} + 1 <= n{2});
  --       auto;smt(parse_gt0 parseK formatK).
  equiv_while (={F2.RO.m, i, n} ∧ §p{1} = §pp{2} ∧ 0 ≤ §i{1} ∧ §i{1} + 1 ≤ §n{2})
  · ec_auto; ec_progress
  ec_auto; ec_progress
  · rw [formatK]
  · exact Int.add_one_le_iff.mpr (parse_gt0 _)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *; omega

-- the oracles' three judgments, over the squeezing loops against the indexed oracles
set_option maxHeartbeats 16000000 in
/-- EC's `local equiv equiv_L4_ideal (D <: DISTINGUISHER{-SLCommon.C, -C, -IF, -S, -F2.RO,
-BIRO.IRO, -BIRO2.IRO}) : L4(D,F.LRO,F2.LRO).distinguish ~
IdealIndif(BIRO.IRO,SimLast(S),DRestr(D)).main : ={glob D} ==> ={glob D, res}`.

Deviations: GAP 5 of the file header.  `S2(F)` and `SimLast(S)(F)` are wrappers in the old
declarations (exception E5): `stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp` after EC's `call`
into the simulators.  What EC's `smt(parseK)`, `smt(parse_twice)` read off `INV_L4_ideal` is
stated once at the top (`hdom`, `hget` for a valid prefix; `hpt`, `hdom'`, `hget'` for an invalid
one) and applied by hand at EC's `progress` goals, with EC's `lemma5`, `lemma5bis`. -/
theorem equiv_L4_ideal :
    ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S, -F2.RO, -BIRO.IRO, -BIRO2.IRO}),
    equiv[ L4(D, SLCommon.F.LRO, F2.LRO).distinguish ~
      IdealIndif(BIRO.IRO.asF, SimLast(S), DRestr(D)).main : ={glob D} ==> ={glob D, res} ] := by
  intro D _
  --     (what EC's `smt(parseK)` reads off the invariant for a valid `p`: the entry `(p, n)` of
  --     the indexed oracle is the entry `format p (n + 1)` of the plain one)
  have hdom : ∀ (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block)
      (m3 : FMap (List block) block) (m4 : FMap (List block × ℤ) block) (p : List block) (n : ℤ),
      INV_L4_ideal m1 m2 m3 m4 → valid p = true → 0 ≤ n →
      (FMap.dom m2 (p, n) ↔ FMap.dom m1 (format p (n + 1))) := by
    rintro m1 m2 m3 m4 p n ⟨⟨h1, -, -, -⟩, -, -, -⟩ hp hn
    exact h1 _ _ _ (parseK _ _ (by omega) (by simpa [valid] using hp))
  have hget : ∀ (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block)
      (m3 : FMap (List block) block) (m4 : FMap (List block × ℤ) block) (p : List block) (n : ℤ),
      INV_L4_ideal m1 m2 m3 m4 → valid p = true → 0 ≤ n →
      FMap.get m2 (p, n) = FMap.get m1 (format p (n + 1)) := by
    rintro m1 m2 m3 m4 p n ⟨⟨-, -, h3, -⟩, -, -, -⟩ hp hn
    exact h3 _ _ _ (parseK _ _ (by omega) (by simpa [valid] using hp))
  --     (the same for an invalid prefix, `(p, n) = parse x`, by EC's `parse_twice`)
  have hpt : ∀ (x : List block) (i : ℤ), 0 ≤ i → i < (parse x).2 →
      parse (format (parse x).1 (i + 1)) = ((parse x).1, i + 1) := fun x i h0 hi =>
    parse_twice (parse x).1 (parse x).2 x rfl (i + 1) ⟨by omega, by omega⟩
  have hdom' : ∀ (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block)
      (m3 : FMap (List block) block) (m4 : FMap (List block × ℤ) block) (x : List block) (i : ℤ),
      INV_L4_ideal m1 m2 m3 m4 → 0 ≤ i → i < (parse x).2 →
      (FMap.dom m4 ((parse x).1, i) ↔ FMap.dom m3 (format (parse x).1 (i + 1))) := by
    rintro m1 m2 m3 m4 x i ⟨-, ⟨h1, -, -, -⟩, -, -⟩ h0 hi
    exact h1 _ _ _ (hpt x i h0 hi)
  have hget' : ∀ (m1 : FMap (List block) block) (m2 : FMap (List block × ℤ) block)
      (m3 : FMap (List block) block) (m4 : FMap (List block × ℤ) block) (x : List block) (i : ℤ),
      INV_L4_ideal m1 m2 m3 m4 → 0 ≤ i → i < (parse x).2 →
      FMap.get m4 ((parse x).1, i) = FMap.get m3 (format (parse x).1 (i + 1)) := by
    rintro m1 m2 m3 m4 x i ⟨-, ⟨-, -, h3, -⟩, -, -⟩ h0 hi
    exact h3 _ _ _ (hpt x i h0 hi)
  -- EC: proc; inline*; auto; sp.
  equiv_proc; stmt_inline*; ec_auto; stmt_sp
  -- EC: call(: ={glob S, glob C}
  --       /\ INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2} F2.RO.m{1} BIRO2.IRO.mp{2});
  --       auto; -1:(progress;split;smt(mem_empty in_fset0 emptyE)).
  equiv_call (_ : ={glob S, glob C} ∧
    INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
  --     (the invariant on the empty maps: the old port's `INV_L4_ideal_empty`)
  on_goals 4 =>
    ec_auto; ec_progress
    exact INV_L4_ideal_empty
  -- EC: + proc;sp;if;auto;call(: ={glob S}
  --         /\ INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2} F2.RO.m{1} BIRO2.IRO.mp{2}); auto.
  · equiv_proc; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto
    equiv_call (_ : ={arg, S.m, S.mi, S.paths} ∧
        INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ==>
      ={res, S.m, S.mi, S.paths} ∧
        INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
    on_goals 2 => ec_auto
    --     (EC's `call (: I)` opens the callees; E5: `S2(F)` and `SimLast(S)(F)` are wrappers of
    --     `S(Last(F))` and `S(Last(Valid(F)))` here, one call more than EC's aliases)
    equiv_proc; stmt_inline{1} 0; stmt_inline{2} 0; stmt_sp
    -- EC: if;1,3:auto.
    stmt_if
    · ec_close
    on_goals 2 => ec_auto
    -- EC: seq 1 1 : (={y1, x, glob S}
    --       /\ INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2} F2.RO.m{1} BIRO2.IRO.mp{2});
    --     last by conseq(:_==> ={y, glob S});progress;sim.
    --     (EC's `x` is the wrappers' inlined parameter, our `x0`)
    equiv_seq 1 1 : (={y1, x0, S.m, S.mi, S.paths} ∧
      INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
    rotate_left
    · equiv_conseq (: _ ==> ={y, S.m, S.mi, S.paths})
      case post => ec_progress
      sim
    -- EC: if;auto;call(: INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2} F2.RO.m{1} BIRO2.IRO.mp{2});auto.
    stmt_if
    · ec_close
    on_goals 2 => ec_auto
    --     (EC's `auto`: nothing to do here)
    equiv_call (_ : ={arg} ∧
        INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ==>
      ={res} ∧ INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
    on_goals 2 => ec_auto
    --     (EC's `call (: I)` opens the callees)
    equiv_proc
    -- EC: inline*;auto;sp;if;auto;1:smt(parseK parse_gt0 formatK);1:sp 0 4;2:sp 0 3.
    stmt_inline*; ec_auto; stmt_sp
    stmt_if
    --     (EC's `smt(parseK parse_gt0 formatK)`, by hand: the right's query is `parse p` again)
    · ec_prep; simp only [Prod.mk.eta] at *; subst_vars; rw [formatK]
    -- EC: - rcondt{2}1;1:auto;1:smt(parseK parse_gt0 formatK).
    · ec_auto; stmt_sp 0 4
      stmt_rcondt{2} 1
      · ec_auto; ec_prep; simp only [Prod.mk.eta] at *; subst_vars
        simp only [formatK] at *
        rw [‹xn.1 = _›]; exact ‹valid _ = true›
      -- EC: while(lres{1} = bs{2} /\ ={i,n} /\ x{2} = p0{1} /\ valid p0{1} /\ 0 <= i{1}
      --       /\ INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2} F2.RO.m{1} BIRO2.IRO.mp{2});progress.
      --     (EC's `x` on the right, `BIRO.IRO.f`'s parameter, is our `x0`)
      equiv_while (§lres{1} = §bs{2} ∧ ={i, n} ∧ §x0{2} = §p0{1} ∧ valid §p0{1} ∧ 0 ≤ §i{1} ∧
        INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
      -- EC: * sp;if{2}.
      · stmt_sp; stmt_if{2}
        -- EC: + rcondt{1}2;auto;progress.
        --     - have[]h1 _ _ _:=H1;have[]h'1 _:=h1;smt(parseK).
        --     - smt(get_setE).
        --     - smt().
        --     - exact lemma5.
        · stmt_rcondt{1} 2
          · ec_auto; ec_prep
            refine fun h => ‹¬ FMap.dom _ (_, _)›
              ((hdom _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹valid _ = true› ?_).mpr h)
            assumption
          ec_auto; ec_progress
          exact lemma5 _ _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹¬ FMap.dom _ (_, _)› ‹0 ≤ n0₂›
            ‹valid x1₂ = true›
        -- EC: rcondf{1}2;auto;progress.
        --     - have[]h1 _ _ _:=H1;have[]h'1 _:=h1;smt(parseK).
        --     - have[]h1:=H1;have[]:=h1;smt(parseK).
        --     smt().
        stmt_rcondf{1} 2
        · ec_auto; ec_prep
          simp only [Bool.not_false, decide_eq_true_eq] at *
          refine (hdom _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹valid _ = true› ?_).mp
            ‹FMap.dom _ (_, _)›
          assumption
        ec_auto; ec_progress
        rw [hget _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹valid x1₂ = true› ‹0 ≤ n0₂›]
      -- EC: by if{1};auto;smt(parseK parse_gt0 formatK).
      --     (EC's `smt`, by hand: the right's query is `parse p` again)
      stmt_if{1} <;> (ec_auto; ec_progress)
      all_goals
        simp only [Prod.mk.eta] at *; subst_vars; simp only [formatK] at *
        first | omega | simp_all
    -- EC: rcondf{1}1;1:auto;1:smt(parse_gt0);sp.
    ec_auto; stmt_sp 0 3
    stmt_rcondf{1} 1
    · ec_auto; ec_prep; exact parse_gt0 _
    stmt_sp
    -- EC: rcondt{2}1;1:auto.
    stmt_rcondt{2} 1
    · ec_auto
    -- EC: while(lres{1} = bs0{2} /\ (i,n,pp){1} = (i0,n0,x0){2}
    --       /\ (x0{2}, n0{2}) = parse (format q{2} k{2}) /\ ! valid x0{2} /\ 0 <= i{1}
    --       /\ INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2} F2.RO.m{1} BIRO2.IRO.mp{2});progress.
    --     (EC's `n0`, `x0` on the right, `BIRO2.IRO.f`'s, are our `n1`, `x2`)
    equiv_while (§lres{1} = §bs0{2} ∧ (§i{1}, §n{1}, §pp{1}) = (§i0{2}, §n1{2}, §x2{2}) ∧
      (§x2{2}, §n1{2}) = parse (format §q{2} §k{2}) ∧ valid §x2{2} = false ∧ 0 ≤ §i{1} ∧
      INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
    -- EC: * sp;if{2}.
    · stmt_sp; stmt_if{2}
      -- EC: + rcondt{1}2;auto;progress.
      --       - have[]_ h1 _ _:=H2;have[]:=h1;progress.
      --         have:=H7 x0{m} i0{m} (format x0{m} (i0{m} + 1));rewrite H5/==>->//=.
      --         have->/#:=parse_twice _ _ _ H.
      --       - smt(get_setE).
      --       - smt().
      --       - apply lemma5bis=>//=.
      --         rewrite(parse_twice _ _ _ H)/#.
      · stmt_rcondt{1} 2
        · ec_auto; ec_prep
          refine fun h => ‹¬ FMap.dom _ (_, _)›
            ((hdom' _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ?_ ?_).mpr h) <;> assumption
        ec_auto; ec_progress
        exact lemma5bis _ _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹¬ FMap.dom _ (_, _)› ‹0 ≤ n2₂›
          ‹valid _ = false› (hpt _ _ ‹0 ≤ n2₂› ‹n2₂ < _›)
      -- EC: rcondf{1}2;auto;progress.
      --     - have[]_ h1 _ _:=H2;have[]:=h1;progress.
      --       have:=H7 x0{m} i0{m} (format x0{m} (i0{m} + 1));rewrite H5/==>->//=.
      --       have->/#:=parse_twice _ _ _ H.
      --     - have[]_ h1 _ _:=H2;have[]h'1 _:=h1;smt(parseK parse_twice).
      --     - smt().
      stmt_rcondf{1} 2
      · ec_auto; ec_prep
        simp only [Bool.not_false, decide_eq_true_eq] at *
        refine (hdom' _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ?_ ?_).mp ‹FMap.dom _ (_, _)› <;>
          assumption
      ec_auto; ec_progress
      rw [hget' _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹0 ≤ n2₂› ‹n2₂ < _›]
    -- EC: by rcondf{1}1;auto;smt(parseK formatK).
    stmt_rcondf{1} 1
    · ec_auto; ec_prep; rw [formatK]; omega
    ec_auto; ec_progress
    all_goals
      simp only [Prod.mk.eta] at *; subst_vars; simp only [formatK] at *
      first
        | omega
        | (simp_all [formatK]; done)
        | (simp_all [formatK]; apply Prod.ext <;> assumption)
  -- EC: + by proc;inline*;conseq(:_==> ={glob C, glob S, z});progress;sim.
  · equiv_proc; stmt_inline*
    equiv_conseq (: _ ==> ={C.c, S.m, S.mi, S.paths, z})
    case post => ec_progress
    sim
  -- EC: proc;sp;if;auto;call(: INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2}
  --       F2.RO.m{1} BIRO2.IRO.mp{2});auto.
  equiv_proc; stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (EC's `auto`: nothing to do here)
  equiv_call (_ : ={arg} ∧
      INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2} ==>
    ={res} ∧ INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
  on_goals 2 => (ec_auto; ec_close)
  --     (EC's `call (: I)` opens the callees)
  equiv_proc
  -- EC: inline*;sp;if;auto;sp.
  stmt_inline*; stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  ec_auto; stmt_sp
  -- EC: rcondt{1}1;1:auto;if{1};sp.
  stmt_rcondt{1} 1
  · ec_auto; ec_close
  stmt_if{1} <;> stmt_sp
  -- EC: - by rcondf{1}1;2:rcondf{2}1;auto;smt().
  · stmt_rcondf{1} 1
    on_goals 2 => stmt_rcondf{2} 1
    · ec_auto
    · ec_auto
    ec_auto
  -- EC: while(lres{1} = bs{2} /\ ={i} /\ n0{1} = n{2} /\ x{2} = p0{1} /\ valid p0{1} /\ 0 <= i{1}
  --       /\ INV_L4_ideal F.RO.m{1} BIRO.IRO.mp{2} F2.RO.m{1} BIRO2.IRO.mp{2});progress.
  --     (the right's `x`, a `List block`, is written with its type: there is an `x` of another
  --     type)
  equiv_while (§lres{1} = §bs{2} ∧ ={i} ∧ §n0{1} = §n{2} ∧
    §(localVarLens "x" (List block)){2} = §p0{1} ∧ valid §p0{1} ∧ 0 ≤ §i{1} ∧
    INV_L4_ideal §SLCommon.F.RO.m{1} §BIRO.IRO.mp{2} §F2.RO.m{1} §BIRO2.IRO.mp{2})
  -- EC: sp;if{2}.
  · stmt_sp; stmt_if{2}
    -- EC: + rcondt{1}2;auto;progress.
    --       - have[]h1 _ _ _:=H1;have[]h'1 _:=h1;smt(parseK).
    --       - smt(get_setE).
    --       - smt().
    --       - exact lemma5.
    · stmt_rcondt{1} 2
      · ec_auto; ec_prep
        refine fun h => ‹¬ FMap.dom _ (_, _)›
          ((hdom _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹valid _ = true› ?_).mpr h)
        assumption
      ec_auto; ec_progress
      exact lemma5 _ _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹¬ FMap.dom _ (_, _)› ‹0 ≤ n0₂›
        ‹valid x0₂ = true›
    -- EC: rcondf{1}2;auto;progress.
    --     - have[]h1 _ _ _:=H1;have[]h'1 _:=h1;smt(parseK).
    --     - have[]h1:=H1;have[]:=h1;smt(parseK).
    --     smt().
    stmt_rcondf{1} 2
    · ec_auto; ec_prep
      simp only [Bool.not_false, decide_eq_true_eq] at *
      refine (hdom _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹valid _ = true› ?_).mp
        ‹FMap.dom _ (_, _)›
      assumption
    ec_auto; ec_progress
    rw [hget _ _ _ _ _ _ ‹INV_L4_ideal _ _ _ _› ‹valid x0₂ = true› ‹0 ≤ n0₂›]
  --     (EC's `progress` on the loop's entry)
  ec_auto

-- ten `byequiv`s over the section's games
set_option maxHeartbeats 4000000 in
/-- EC's `lemma equiv_ideal (D <: DISTINGUISHER{-SLCommon.C, -C, -IF, -S, -F.FRO, -F2.RO,
-F2.FRO, -BIRO.IRO, -BIRO2.IRO}) &m: Pr[SLCommon.IdealIndif(IF,S,SLCommon.DRestr(A(D))).main()
@ &m : res] = Pr[IdealIndif(BIRO.IRO,SimLast(S),DRestr(D)).main() @ &m : res]`.

Deviations: the four lazy/eager steps (EC: `byequiv; proc; sp; inline*; sp; wp;
call (F.FullEager.RO_LRO_D (D2(D)) _)`, and the same with `D3`, `D5`, `D6`) are the old port's
`L2_RO_LRO`, `L_RO_LRO`, `L4_F_RO_LRO`, `L4_F2_RO_LRO` — the wrappers `D2`…`D6` of the old
declarations (exception E5) are not EC's aliases, and the old lemmas bridge them; their
restriction hypotheses are read off `D`'s declaration.  EC's sequence of rewrites is one chain of
equations at the end.  `-F.FRO`, `-F2.FRO` are written as their variables. -/
theorem equiv_ideal :
    ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -IF, -S, -SLCommon.F.FRO.m, -F2.RO, -F2.FRO.m,
      -BIRO.IRO, -BIRO2.IRO}), ∀ m : VariableAssignment,
    Pr[ SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main () @ &m : §res ] =
      Pr[ IdealIndif(BIRO.IRO.asF, SimLast(S), DRestr(D)).main () @ &m : §res ] := by
  intro D _ m
  --     (the section's restriction in the old port's form, for its lazy/eager steps)
  have hDr : DRestrictions_Ideal D :=
    (Module.Declared.le_compl D).trans (Footprint.compl_antimono (by first | fp_le | gcol_fp))
  have hDf : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint)ᶜ :=
    (Module.Declared.le_compl D).trans (Footprint.compl_antimono (by first | fp_le | gcol_fp))
  have hDr2 : DRestrictions_Ideal2 D :=
    ⟨hDr, (Module.Declared.le_compl D).trans
      (Footprint.compl_antimono (by first | fp_le | gcol_fp))⟩
  have hDf2 : FVP.fvP D ≤ ((SLCommon.F.FRO.m).footprint ⊔ (F2.FRO.m).footprint)ᶜ :=
    (Module.Declared.le_compl D).trans (Footprint.compl_antimono (by first | fp_le | gcol_fp))
  -- EC: have->:Pr[SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main() @ &m : res]
  --       = Pr[SLCommon.IdealIndif(IF, S, A(D)).main() @ &m : res].
  --     + by byequiv(ideal_equiv D)=>//=.
  have e1 : Pr[ SLCommon.IdealIndif(IF, S, SLCommon.DRestr(A(D))).main () @ &m : §res ] =
      Pr[ SLCommon.IdealIndif(IF, S, A(D)).main () @ &m : §res ] := by
    byequiv (ideal_equiv D)
  -- EC: have<-:Pr[L2(D,F.RO).distinguish() @ &m : res] =
  --       Pr[SLCommon.IdealIndif(IF,S,A(D)).main() @ &m : res].
  --     + by byequiv(ideal_equiv2 D).
  have e2 : Pr[ L2(D, SLCommon.F.RO.asRO).distinguish () @ &m : §res ] =
      Pr[ SLCommon.IdealIndif(IF, S, A(D)).main () @ &m : §res ] := by
    byequiv (ideal_equiv2 D)
  -- EC: have->:Pr[L2(D, F.RO).distinguish() @ &m : res] =
  --       Pr[L2(D,F.LRO).distinguish() @ &m : res].
  --     + byequiv=>//=;proc;sp;inline*;sp;wp.
  --       call(F.FullEager.RO_LRO_D (D2(D)) _);auto.
  --       by move=> _; exact/dunifin_ll.
  --     (the old port's `L2_RO_LRO`, which is this step: deviation)
  have e3 : Pr[ L2(D, SLCommon.F.RO.asRO).distinguish () @ &m : §res ] =
      Pr[ L2(D, SLCommon.F.LRO).distinguish () @ &m : §res ] := by
    byequiv (L2_RO_LRO D (by ec_module) hDr hDf)
  -- EC: have->:Pr[IdealIndif(BIRO.IRO, SimLast(S), DRestr(D)).main() @ &m : res] =
  --       Pr[L4(D,F.LRO,F2.LRO).distinguish() @ &m : res].
  --     + by rewrite eq_sym;byequiv(equiv_L4_ideal D)=>//=.
  have e4 : Pr[ IdealIndif(BIRO.IRO.asF, SimLast(S), DRestr(D)).main () @ &m : §res ] =
      Pr[ L4(D, SLCommon.F.LRO, F2.LRO).distinguish () @ &m : §res ] := by
    symm
    byequiv (equiv_L4_ideal D)
  -- EC: have<-:Pr[L4(D, F.RO, F2.RO).distinguish() @ &m : res] =
  --       Pr[L4(D,F.LRO,F2.LRO).distinguish() @ &m : res].
  --     + have->:Pr[L4(D, F.RO, F2.RO).distinguish() @ &m : res] =
  --         Pr[L4(D,F.LRO, F2.RO).distinguish() @ &m : res].
  --       - byequiv=>//=;proc;sp;inline*;sp;wp.
  --         call(F.FullEager.RO_LRO_D (D5(D)) _); auto.
  --         by move=> _; exact/dunifin_ll.
  --       byequiv=>//=;proc;sp;inline*;sp;wp.
  --       call(F2.FullEager.RO_LRO_D (D6(D)) _); auto.
  --       by move=> _; exact/dunifin_ll.
  --     (the old port's `L4_F_RO_LRO`, `L4_F2_RO_LRO`: deviation)
  have e5 : Pr[ L4(D, SLCommon.F.RO.asRO, F2.RO.asRO).distinguish () @ &m : §res ] =
      Pr[ L4(D, SLCommon.F.LRO, F2.LRO).distinguish () @ &m : §res ] := by
    have e5a : Pr[ L4(D, SLCommon.F.RO.asRO, F2.RO.asRO).distinguish () @ &m : §res ] =
        Pr[ L4(D, SLCommon.F.LRO, F2.RO.asRO).distinguish () @ &m : §res ] := by
      byequiv (L4_F_RO_LRO D (by ec_module) hDr2 hDf2)
    refine e5a.trans ?_
    byequiv (L4_F2_RO_LRO D (by ec_module) hDr2 hDf2)
  -- EC: have<-:Pr[L3(D, F.RO).distinguish() @ &m : res] =
  --       Pr[L4(D, F.RO, F2.RO).distinguish() @ &m : res].
  --     + by byequiv(equiv_L3_L4 D)=>//=.
  have e6 : Pr[ L3(D, SLCommon.F.RO.asRO).distinguish () @ &m : §res ] =
      Pr[ L4(D, SLCommon.F.RO.asRO, F2.RO.asRO).distinguish () @ &m : §res ] := by
    byequiv (equiv_L3_L4 D)
  -- EC: have<-:Pr[L(D, F.RO).distinguish() @ &m : res] =
  --       Pr[L3(D, F.RO).distinguish() @ &m : res].
  --     + by byequiv(Ideal_equiv3 D).
  have e7 : Pr[ L(D, SLCommon.F.RO.asRO).distinguish () @ &m : §res ] =
      Pr[ L3(D, SLCommon.F.RO.asRO).distinguish () @ &m : §res ] := by
    byequiv (Ideal_equiv3 D)
  -- EC: have->:Pr[L(D, F.RO).distinguish() @ &m : res] =
  --       Pr[L(D,F.LRO).distinguish() @ &m : res].
  --     + byequiv=>//=;proc;sp;inline*;sp;wp.
  --       call(F.FullEager.RO_LRO_D (D3(D)) _); auto.
  --       by move=> _; exact/dunifin_ll.
  --     (the old port's `L_RO_LRO`: deviation)
  have e8 : Pr[ L(D, SLCommon.F.RO.asRO).distinguish () @ &m : §res ] =
      Pr[ L(D, SLCommon.F.LRO).distinguish () @ &m : §res ] := by
    byequiv (L_RO_LRO D (by ec_module) hDr hDf)
  -- EC: rewrite eq_sym.
  --     by byequiv(Ideal_equiv_valid D).
  have e9 : Pr[ L(D, SLCommon.F.LRO).distinguish () @ &m : §res ] =
      Pr[ L2(D, SLCommon.F.LRO).distinguish () @ &m : §res ] := by
    byequiv (Ideal_equiv_valid D)
  --     (EC's rewrites, in their order, as one chain)
  exact e1.trans (e2.symm.trans (e3.trans (e9.symm.trans (e8.symm.trans
    (e7.trans (e6.trans (e5.trans e4.symm)))))))

/-! ## Section `Real` -/

/-- `Perm` where `SLCommon`'s `DPRIMITIVE` is expected (`SqueezelessSponge(Perm)`): EC's
subtyping.  EC's `module P = Perm` is not declared: the old port's alias `P` is a `BlockSponge`
primitive that `inline*` does not open, and EC's scripts are the same with `Perm` for `P`. -/
module_subtype (EC.PRP.StrongPRP.PRP (block × capacity)) <: SLCommon.DPRIMITIVE

/-! The absorbing loop of `equiv_sponge` extends `Redo.prefixes` by `take (i + 1) p`, a prefix
it does not know.  EC proves the invariant's facts on the extended map inline, in both branches
of the permutation's test (`smt(mem_set get_setE domE take_take size_take …)` and by hand); here
each is stated once. -/

section AbsorbStep

open SLCommon.Prefix (all_prefixes take_take)

variable {P pref : FMap (List block) SLCommon.state} {bl : List block} {i : ℤ}

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- A key of the extended map is in `pref`, or a prefix of `p`. -/
theorem absorb_dom
    (hdom : ∀ l, FMap.dom P l → FMap.dom pref l ∨ ∃ j, 0 < j ∧ j ≤ i ∧ l = take j bl)
    (hi : 0 ≤ i) (v : SLCommon.state) (l : List block)
    (hl : FMap.dom (FMap.set P (take (i + 1) bl) v) l) :
    FMap.dom pref l ∨ ∃ j, 0 < j ∧ j ≤ i + 1 ∧ l = take j bl := by
  rcases (FMap.mem_set _ _ _ _).mp hl with h | rfl
  · rcases hdom l h with h | ⟨j, hj, hj', rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, by omega, rfl⟩
  · exact Or.inr ⟨i + 1, by omega, le_rfl, rfl⟩

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- The extended map agrees with `pref` on `pref`'s keys. -/
theorem absorb_get (hpl : ∀ l, FMap.dom pref l → pref.get l = P.get l)
    (hnd : ¬ FMap.dom P (take (i + 1) bl)) (v : SLCommon.state) (l : List block)
    (hl : FMap.dom pref l) : pref.get l = (FMap.set P (take (i + 1) bl) v).get l := by
  have hl' : FMap.dom P l := by rw [FMap.domE, ← hpl l hl, ← FMap.domE]; exact hl
  rw [FMap.get_set_neqE P (take (i + 1) bl) l v (fun h => hnd (h ▸ hl'))]
  exact hpl l hl

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- The extended map does not know the next prefix. -/
theorem absorb_fresh (hall : all_prefixes P) (hnd : ¬ FMap.dom P (take (i + 1) bl))
    (hi : 0 ≤ i) (hlt : i + 1 < size bl) (v : SLCommon.state) :
    ¬ FMap.dom (FMap.set P (take (i + 1) bl) v) (take (i + 1 + 1) bl) := by
  intro hd
  rcases (FMap.mem_set _ _ _ _).mp hd with h | h
  · have := hall _ h (i + 1)
    rw [take_take, min_eq_left (show i + 1 ≤ i + 1 + 1 by omega)] at this
    exact hnd this
  · have := congrArg size h
    rw [size_take (i + 1 + 1) bl (by omega), size_take (i + 1) bl (by omega)] at this
    split_ifs at this <;> omega

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- The extended map is closed under prefixes. -/
theorem absorb_all_prefixes (hall : all_prefixes P) (hd : FMap.dom P (take i bl))
    (v : SLCommon.state) :
    all_prefixes (FMap.set P (take (i + 1) bl) v) := by
  intro bs hbs k
  rw [FMap.mem_set]
  rcases (FMap.mem_set _ _ _ _).mp hbs with h | h
  · exact Or.inl (hall _ h k)
  · rw [h, take_take]
    by_cases hk : k ≤ i
    · left
      rw [min_eq_left (show k ≤ i + 1 by omega)]
      have := hall _ hd k
      rwa [take_take, min_eq_left hk] at this
    · right
      rw [min_eq_right (show i + 1 ≤ k by omega)]

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- The extended map records the permutation's steps along `p`, up to `i + 1`: `m'` is the
permutation's map after the step (`m` with, possibly, one more entry), `v` its value at the
state recorded for `take i p` xored with the next block. -/
theorem absorb_step {m m' : FMap SLCommon.state SLCommon.state} {sa : block} {sc : capacity}
    (hall : all_prefixes P) (hnd : ¬ FMap.dom P (take (i + 1) bl))
    (hget : P.get (take i bl) = some (sa, sc))
    (hstep : ∀ j, 0 ≤ j ∧ j < i → ∃ b c, P.get (take j bl) = some (b, c) ∧
      m.get (b +^ nth default bl j, c) = P.get (take (j + 1) bl))
    (hm : ∀ x, FMap.dom m x → m'.get x = m.get x) (v : SLCommon.state)
    (hv : m'.get (sa +^ nth default bl i, sc) = some v) (j : ℤ) (hj : 0 ≤ j ∧ j < i + 1) :
    ∃ b c, (FMap.set P (take (i + 1) bl) v).get (take j bl) = some (b, c) ∧
      m'.get (b +^ nth default bl j, c) =
        (FMap.set P (take (i + 1) bl) v).get (take (j + 1) bl) := by
  have hd : FMap.dom P (take i bl) := (FMap.domE _ _).mpr (by rw [hget]; simp)
  have hdt : ∀ k, k ≤ i → FMap.dom P (take k bl) := fun k hk => by
    have := hall _ hd k
    rwa [take_take, min_eq_left hk] at this
  have hne : ∀ l, FMap.dom P l → l ≠ take (i + 1) bl := fun l hl h => hnd (h ▸ hl)
  by_cases hji : j = i
  · subst hji
    exact ⟨sa, sc, by rw [FMap.get_set_neqE _ _ _ _ (hne _ hd)]; exact hget,
      by rw [FMap.get_set_sameE]; exact hv⟩
  · obtain ⟨b, c, hb, hmb⟩ := hstep j ⟨hj.1, by omega⟩
    have hd1 := hdt (j + 1) (by omega)
    refine ⟨b, c, by rw [FMap.get_set_neqE _ _ _ _ (hne _ (hdt j (by omega)))]; exact hb, ?_⟩
    rw [FMap.get_set_neqE _ _ _ _ (hne _ hd1),
      hm _ (by rw [FMap.domE, hmb, ← FMap.domE]; exact hd1)]
    exact hmb

end AbsorbStep

/-! The squeezing loop of `equiv_sponge` runs the squeezeless sponge on `format p (i + 1)` when
`format p i` is a known prefix: all its blocks but the last are known.  EC proves this at each
`rcond` and in each loop (`have->: take (i1 + 1) (format bl (i + 1)) = take (i1 + 1) (format bl i);
smt(all_prefixes_of_INV_real)`, `smt(take_format size_cat size_nseq …)`); here once for the blocks
of `p` and once for the padding. -/

section SqueezeStep

variable {P : FMap (List block) SLCommon.state} {bl : List block} {i i1 : ℤ}

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- EC's `size_cat`, `size_nseq` on `format`. -/
theorem size_format (bl : List block) (j : ℤ) : size (format bl j) = size bl + max 0 (j - 1) := by
  simp only [format, size_cat, size_nseq]

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- EC's `smt(take_cat take_le0 cats0)`: within `p`, a prefix of `format p j` is one of `p`. -/
theorem take_format_le (bl : List block) (j k : ℤ) (hk : k ≤ size bl) :
    take k (format bl j) = take k bl := by
  rw [format, take_cat]
  split_ifs with h
  · rfl
  · rw [show k - size bl = 0 by omega, take0, cats0, take_oversize k bl (by omega)]

/-- A prefix of `format p (i + 1)` within `p` is known. -/
theorem squeeze_known_head {c1 c2 : ℤ} {m mi : FMap SLCommon.state SLCommon.state}
    (hinv : INV_Real c1 c2 m mi P) (hd : FMap.dom P (format bl i)) (hlt : i1 < size bl) :
    FMap.dom P (take (i1 + 1) (format bl (i + 1))) := by
  rw [take_format_le bl (i + 1) (i1 + 1) (by omega), ← take_format_le bl i (i1 + 1) (by omega)]
  exact all_prefixes_of_INV_real _ _ _ _ _ hinv _ hd _

/-- A prefix of `format p (i + 1)` past `p`, but for the last block, is known. -/
theorem squeeze_known_tail {c1 c2 : ℤ} {m mi : FMap SLCommon.state SLCommon.state}
    (hinv : INV_Real c1 c2 m mi P) (hd : FMap.dom P (format bl i)) (hlo : size bl ≤ i1)
    (hlt : i1 < size (format bl (i + 1)) - 1) :
    FMap.dom P (take (i1 + 1) (format bl (i + 1))) := by
  have hs := size_format bl (i + 1)
  rw [take_format_succ bl i (i1 + 1) (by omega) (by rw [size_format]; omega)]
  exact all_prefixes_of_INV_real _ _ _ _ _ hinv _ hd _

end SqueezeStep

set_option hygiene false in
/-- EC's `smt(size_cat size_nseq)` on the guards of `equiv_sponge`'s split loops: the sizes of
the formats and the guards' conjunctions as linear facts, then `omega`.  (GAP 9: the closer
leaves a split loop's guard `a && b` as it is.) -/
local macro "sponge_guard" : tactic => `(tactic| (
  simp only [size_format, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not] at *
  omega))

set_option hygiene false in
/-- EC's `auto` and `while(i < n);auto;2:smt(). by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;
auto.`, the side goal of each `rcond` on the last round of `equiv_sponge`'s squeezing loop: the
loop keeps `i < n` (through the squeezeless sponge's inlined loop).  (No hygiene: `§i`, `§n` are
the program's variables.) -/
local macro "sponge_round" : tactic => `(tactic| (
  intro σ
  (try stmt_wp)
  hoare_while (§i < §n)
  · stmt_sp; stmt_if
    · ec_auto; stmt_sp; hoare_while (§i < §n)
      · ec_auto <;> ec_close
      · ec_close
      · ec_auto <;> ec_close
    · ec_auto <;> ec_close
  · ec_close
  · ec_auto <;> ec_close))

set_option hygiene false in
/-- EC's `by auto; while(i1 < size p1);auto;1:if;2:(sp;if);auto;smt(size_cat size_nseq size_ge0)`
and its variant through `seq 1 : (i1 = size p1 - 1)`, the side goals of the `rcond`s on the last
block of `format p (i + 1)` in `equiv_sponge`'s squeezing loop: the split loop keeps
`i1 < size p1`, and `p1` is not empty.  (No `seq` on a Hoare triple, GAP 9: our `auto` takes the
last round first.  No hygiene: `§i1`, `§p1` are the program's variables.) -/
local macro "sponge_last" : tactic => `(tactic| (
  intro σ
  (try ec_auto)
  hoare_while (§i1 < size §p1)
  · ec_auto; ec_progress
    all_goals
      simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      omega
  · first
    | ec_close
    | (ec_prep
       have h : size p1 ≤ i1 + 1 := by
         simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *
         omega
       split_ifs <;> simp [h])
  · ec_auto; ec_prep
    simp only [format, size_cat, size_nseq]
    refine lt_of_lt_of_le ?_ (le_add_of_nonneg_left (size_ge0 _))
    omega))

-- the functionality's oracle: the squeezeless sponge's inlined loop three times (EC's 300 lines)
set_option maxHeartbeats 16000000 in
/-- EC's `local lemma equiv_sponge (D <: DISTINGUISHER {-P, -Redo, -C, -SLCommon.C}) :
equiv [ GReal(A(D)).main ~ NIndif(Squeeze(SqueezelessSponge(P)),P,DRestr(D)).main :
={glob D} ==> ={res, glob D, glob P, C.c} /\ SLCommon.C.c{1} <= C.c{2} <= max_size]`.

Deviations: EC's `P` (`module P = Perm`) is written `Perm`, and `glob P` its two maps (GAP 3);
the facts EC proves inline in the two branches of the permutation's test and at each `rcond` are
the lemmas above (`absorb_*`, `squeeze_known_*`); GAPs 8 to 10 of the file header. -/
theorem equiv_sponge : ∀ (D <: DISTINGUISHER {-Perm, -SLCommon.Redo, -C, -SLCommon.C}),
    equiv[ SLCommon.GReal(A(D)).main ~
      NIndif(Squeeze(SLCommon.SqueezelessSponge(Perm)), Perm, DRestr(D)).main :
      ={glob D} ==> ={res, glob D, Perm.m, Perm.mi, C.c} ∧ §SLCommon.C.c{1} ≤ §C.c{2} ∧
        §C.c{2} ≤ max_size ] := by
  intro D _
  -- EC: proc;inline*;sp;wp.
  equiv_proc; stmt_inline*; stmt_sp; stmt_wp
  -- EC: call(: ={Redo.prefixes, glob P, C.c} /\ C.c{1} <= max_size /\
  --       INV_Real SLCommon.C.c{1} C.c{2} Perm.m{1} Perm.mi{1} Redo.prefixes{1});auto;last first.
  equiv_call (_ : ={SLCommon.Redo.prefixes, Perm.m, Perm.mi, C.c} ∧ §C.c{1} ≤ max_size ∧
    INV_Real §SLCommon.C.c{1} §C.c{2} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
  rotate_right
  -- EC: + progress.
  --       + exact max_ge0.
  --       + by split=>//=;1:split;smt(mem_empty in_fset0 mem_set get_setE).
  --       by case:H2=>//=.
  · ec_auto; ec_progress
    · exact SLCommon.max_ge0
    --     (the old port's `INV_Real_init`)
    · exact INV_Real_init
    · obtain ⟨h, -, -⟩ := ‹INV_Real _ _ _ _ _›
      exact h
  -- EC: + by proc;inline*;auto;sp;if;auto;sp;if;auto;
  --         smt(INV_Real_addm_mi INV_Real_incr supp_dexcepted).
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto; stmt_sp; stmt_if
    · ec_close
    all_goals ec_auto
    all_goals ec_progress
    · exact INV_Real_incr _ _ _ _ _ (INV_Real_addm_mi _ _ _ _ _ _ _ ‹INV_Real _ _ _ _ _› ‹¬ _›
        (not_of_mem_support_dexcepted ‹_›))
    · exact INV_Real_incr _ _ _ _ _ ‹_›
  -- EC: + proc;inline*;auto;sp;if;auto;sp;if;auto;progress.
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto; stmt_sp; stmt_if
    · ec_close
    all_goals ec_auto
    all_goals ec_progress
    --     + apply INV_Real_incr=>//=.
    --       apply INV_Real_addm_mi=>//=.
    --       + case:H0=>H_c H_m_p H_invm;rewrite (invm_dom_rng _ _ H_invm)//=.
    --         by move:H3;rewrite supp_dexcepted.
    --       case:H0=>H_c H_m_p H_invm;have<-//:=(invm_dom_rng Perm.mi{2} Perm.m{2}).
    --       by rewrite invmC.
    · apply INV_Real_incr
      obtain ⟨H_c, H_m_p, H_invm⟩ := ‹INV_Real _ _ _ _ _›
      apply INV_Real_addm_mi _ _ _ _ _ _ _ ⟨H_c, H_m_p, H_invm⟩
      · rw [invm_dom_rng _ _ H_invm]
        exact not_of_mem_support_dexcepted ‹_›
      · rw [← invm_dom_rng _ _ ((invmC _ _).mp H_invm)]
        assumption
    --     + exact INV_Real_incr.
    · exact INV_Real_incr _ _ _ _ _ ‹_›
  -- EC: + proc;inline*;sp;if;auto.
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto
    -- EC: swap 6;wp;sp=>/=;if;auto;last by progress;split;case:H0=>//=;smt(size_ge0).
    stmt_swap 6; stmt_wp; stmt_sp; stmt_if
    · ec_close
    on_goals 2 =>
      ec_auto; ec_progress
      obtain ⟨h, hm, hi⟩ := ‹INV_Real _ _ _ _ _›
      exact ⟨by have := size_ge0 x0₂.1; omega, hm, hi⟩
    -- EC: conseq(: p{2} = bl{2} /\ n{2} = nb{2} /\ lres{2} = [] /\ b{2} = b0 /\
    --     i{2} = 0 /\ p{1} = bl{1} /\ n{1} = nb{1} /\ lres{1} = [] /\ b{1} = b0 /\
    --     i{1} = 0 /\ z{2} = [] /\ z{1} = [] /\ ={bl, nb} /\ ={Redo.prefixes} /\
    --     ={Perm.mi, Perm.m} /\ ={C.c} /\
    --     INV_Real SLCommon.C.c{1} C.c{2} Perm.m{1} Perm.mi{1} Redo.prefixes{1} /\
    --     C.c{1} + size bl{1} + max (nb{1} - 1) 0 <= max_size /\ valid p{1}
    --   ==> ={lres} /\ ={Redo.prefixes} /\ ={Perm.mi, Perm.m} /\
    --     C.c{1} + size bl{1} + max (nb{1} - 1) 0 =
    --     C.c{2} + size bl{2} + max (nb{2} - 1) 0 /\
    --     INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + max (nb{2} - 1) 0)
    --     Perm.m{1} Perm.mi{1} Redo.prefixes{1});progress.
    equiv_conseq (: §p{2} = §bl{2} ∧ §n{2} = §nb{2} ∧ §lres{2} = [] ∧ §b{2} = b0 ∧
      §i{2} = 0 ∧ §p{1} = §bl{1} ∧ §n{1} = §nb{1} ∧ §lres{1} = [] ∧ §b{1} = b0 ∧
      §i{1} = 0 ∧ §z{2} = [] ∧ §z{1} = [] ∧ ={bl, nb} ∧ ={SLCommon.Redo.prefixes} ∧
      ={Perm.mi, Perm.m} ∧ ={C.c} ∧
      INV_Real §SLCommon.C.c{1} §C.c{2} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1} ∧
      §C.c{1} + size §bl{1} + max (§nb{1} - 1) 0 ≤ max_size ∧ valid §p{1}
      ==> ={lres} ∧ ={SLCommon.Redo.prefixes} ∧ ={Perm.mi, Perm.m} ∧
      §C.c{1} + size §bl{1} + max (§nb{1} - 1) 0 =
      §C.c{2} + size §bl{2} + max (§nb{2} - 1) 0 ∧
      INV_Real §SLCommon.C.c{1} (§C.c{2} + size §bl{2} + max (§nb{2} - 1) 0)
      §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
    case pre => ec_close
    case post => ec_close
    -- EC: sp.
    stmt_sp
    -- EC: seq 2 2:(={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
    --            /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2})
    --                  Perm.m{1} Perm.mi{1} Redo.prefixes{1}
    --            /\  (n,p){1} = (nb,bl){1} /\ lres{1} = [] /\ i{1} = 0
    --            /\  valid p{1}
    --            /\ Redo.prefixes.[p]{1} = Some (b,sc){1}).
    equiv_seq 2 2 : (={i, n, p, lres, nb, bl, b, Perm.m, Perm.mi, C.c, SLCommon.Redo.prefixes} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{2} + size §bl{2}) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      (§n{1}, §p{1}) = (§nb{1}, §bl{1}) ∧ §lres{1} = [] ∧ §i{1} = 0 ∧ valid §p{1} ∧
      (§SLCommon.Redo.prefixes{1}).get §p{1} = some (§b{1}, §sc{1}))
    -- EC: + exists* Redo.prefixes{1},SLCommon.C.c{1};elim* => pref count/=.
    · equiv_exists* §SLCommon.Redo.prefixes{1}, §SLCommon.C.c{1}
      intro pref count
      -- EC: wp;conseq(:_==> ={i0,p0,i,p,n,nb,bl,sa,lres,C.c,glob Redo,glob Perm}
      --           /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = p{1} /\ i0{1} = size p{1}
      --           /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1},sc{1})
      --           /\ INV_Real count C.c{1} Perm.m{1} Perm.mi{1} pref
      --           /\ (forall l, l \in Redo.prefixes{1} =>
      --                l \in pref \/ (exists j, 0 < j <= i0{2} /\ l = take j p{1}))
      --           /\ (forall l, l \in pref => pref.[l] = Redo.prefixes{1}.[l])
      --           /\ SLCommon.C.c{1} <= count + i0{1} <= C.c{1} + i0{1}
      --           /\ (forall j, 0 <= j < i0{1} =>
      --                exists b c, Redo.prefixes{1}.[take j p{1}] = Some (b,c) /\
      --                Perm.m{1}.[(b +^ nth witness p{1} j, c)] =
      --                Redo.prefixes{1}.[take (j+1) p{1}]));
      --       progress.
      stmt_wp
      equiv_conseq (: _ ==> ={i0, p0, i, p, n, nb, bl, sa, lres, C.c, SLCommon.Redo.prefixes,
          Perm.m, Perm.mi} ∧
        §n{1} = §nb{1} ∧ §p{1} = §bl{1} ∧ §p0{1} = §p{1} ∧ §i0{1} = size §p{1} ∧
        (§SLCommon.Redo.prefixes{1}).get (take §i0{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
        INV_Real count §C.c{1} §Perm.m{1} §Perm.mi{1} pref ∧
        (∀ l, FMap.dom §SLCommon.Redo.prefixes{1} l →
          FMap.dom pref l ∨ ∃ j, 0 < j ∧ j ≤ §i0{2} ∧ l = take j §p{1}) ∧
        (∀ l, FMap.dom pref l → pref.get l = (§SLCommon.Redo.prefixes{1}).get l) ∧
        §SLCommon.C.c{1} ≤ count + §i0{1} ∧ count + §i0{1} ≤ §C.c{1} + §i0{1} ∧
        (∀ j, 0 ≤ j ∧ j < §i0{1} →
          ∃ b c, (§SLCommon.Redo.prefixes{1}).get (take j §p{1}) = some (b, c) ∧
            (§Perm.m{1}).get (b +^ nth default §p{1} j, c) =
              (§SLCommon.Redo.prefixes{1}).get (take (j + 1) §p{1})))
      case post =>
        ec_progress
        --     - have inv0:=H3;have[]h_c1c2[]Hmp0 Hmp1 Hinvm:=inv0;split=>//=.
        · obtain ⟨h_c1c2, ⟨Hmp0, Hmp1⟩, Hinvm⟩ := ‹INV_Real _ _ Perm_m₂ _ _›
          have H4 : ∀ l, FMap.dom Redo_prefixes₂ l →
              FMap.dom prefixes₂ l ∨ ∃ j, 0 < j ∧ j ≤ size p0₂1 ∧ l = take j p0₂1 := by assumption
          have H5 : ∀ l, FMap.dom prefixes₂ l → prefixes₂.get l = Redo_prefixes₂.get l := by
            assumption
          have H8 : ∀ j : ℤ, 0 ≤ j ∧ j < size p0₂1 →
              ∃ b c, Redo_prefixes₂.get (take j p0₂1) = some (b, c) ∧
                Perm_m₂.get (b +^ nth default p0₂1 j, c) =
                  Redo_prefixes₂.get (take (j + 1) p0₂1) := by assumption
          refine ⟨?_, ⟨?_, ?_⟩, Hinvm⟩
          --       - case:inv0;smt(size_ge0).
          · omega
          --       split=>//=.
          --       - smt(domE).
          · rw [← H5 [] ((FMap.domE _ _).mpr (by rw [Hmp0]; simp))]
            exact Hmp0
          --       - move=>l H_dom_R i []Hi0 Hisize;have:=H4 l H_dom_R.
          --         case(l \in Redo.prefixes{2})=>H_in_pref//=.
          · intro l H_dom_R i ⟨Hi0, Hisize⟩
            rcases H4 l H_dom_R with H_in_pref | ⟨j, hj0, hjsize, rfl⟩
            --         * have:=Hmp1 l H_in_pref i _;rewrite//=.
            --           rewrite ?H5//=;1:smt(domE).
            --           case(i+1 < size l)=>h;1:smt(domE).
            --           by rewrite take_oversize 1:/#.
            · obtain ⟨b, c, hb, hm⟩ := Hmp1 l H_in_pref i ⟨Hi0, Hisize⟩
              refine ⟨b, c, ?_, ?_⟩
              · rw [← H5 _ ((FMap.domE _ _).mpr (by rw [hb]; simp))]
                exact hb
              rw [hm]
              by_cases h : i + 1 < size l
              · obtain ⟨b', c', hb', -⟩ := Hmp1 l H_in_pref (i + 1) ⟨by omega, h⟩
                exact H5 _ ((FMap.domE _ _).mpr (by rw [hb']; simp))
              · rw [take_oversize (i + 1) l (by omega)]
                exact H5 _ H_in_pref
            --         move=>[]j[][]hj0 hjsize ->>.
            --         have:=Hisize;rewrite size_take 1:/#.
            --         pose k:=if _ then _ else _.
            --         have: k = j by smt().
            --         move: k=> /> Hij.
            --         rewrite !take_take!minrE 1:nth_take 1,2:/#.
            --         rewrite lez_eqVlt -ltzE Hij /=.
            --         by move: (H8 i _)=> /#.
            · have Hij : i < j := by
                rw [size_take j p0₂1 (by omega)] at Hisize
                split_ifs at Hisize <;> omega
              obtain ⟨b, c, hb, hm⟩ := H8 i ⟨Hi0, by omega⟩
              refine ⟨b, c, ?_, ?_⟩
              · rw [SLCommon.Prefix.take_take, min_eq_left (show i ≤ j by omega)]
                exact hb
              · rw [nth_take default j p0₂1 i (by omega) Hij, SLCommon.Prefix.take_take,
                  min_eq_left (show i + 1 ≤ j by omega)]
                exact hm
        --     - smt(get_setE oget_some domE take_oversize).
        · rw [← take_size p0₂1]
          assumption
      -- EC: while( ={i0,p0,i,p,n,nb,bl,sa,sc,lres,C.c,glob Redo,glob Perm}
      --       /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p0{1} = p{1} /\ 0 <= i0{1} <= size p{1}
      --       /\ Redo.prefixes{1}.[take i0{1} p{1}] = Some (sa{1},sc{1})
      --       /\ INV_Real count C.c{1} Perm.m{1} Perm.mi{1} pref
      --       /\ (forall l, l \in Redo.prefixes{1} =>
      --            l \in pref \/ (exists j, 0 < j <= i0{2} /\ l = take j p{1}))
      --       /\ (forall l, l \in pref => pref.[l] = Redo.prefixes{1}.[l])
      --       /\ SLCommon.C.c{1} <= count + i0{1} <= C.c{1} + i0{1}
      --       /\ (i0{1} < size p0{1} =>
      --            take (i0{1}+1) p{1} \in Redo.prefixes{1} =>
      --            Redo.prefixes{1} = pref)
      --       /\ all_prefixes Redo.prefixes{1}
      --       /\ (forall j, 0 <= j < i0{1} =>
      --            exists b c, Redo.prefixes{1}.[take j p{1}] = Some (b,c) /\
      --            Perm.m{1}.[(b +^ nth witness p{1} j, c)] =
      --            Redo.prefixes{1}.[take (j+1) p{1}]));last first.
      equiv_while (={i0, p0, i, p, n, nb, bl, sa, sc, lres, C.c, SLCommon.Redo.prefixes,
          Perm.m, Perm.mi} ∧
        §n{1} = §nb{1} ∧ §p{1} = §bl{1} ∧ §p0{1} = §p{1} ∧ 0 ≤ §i0{1} ∧ §i0{1} ≤ size §p{1} ∧
        (§SLCommon.Redo.prefixes{1}).get (take §i0{1} §p{1}) = some (§sa{1}, §sc{1}) ∧
        INV_Real count §C.c{1} §Perm.m{1} §Perm.mi{1} pref ∧
        (∀ l, FMap.dom §SLCommon.Redo.prefixes{1} l →
          FMap.dom pref l ∨ ∃ j, 0 < j ∧ j ≤ §i0{2} ∧ l = take j §p{1}) ∧
        (∀ l, FMap.dom pref l → pref.get l = (§SLCommon.Redo.prefixes{1}).get l) ∧
        §SLCommon.C.c{1} ≤ count + §i0{1} ∧ count + §i0{1} ≤ §C.c{1} + §i0{1} ∧
        (§i0{1} < size §p0{1} → FMap.dom §SLCommon.Redo.prefixes{1} (take (§i0{1} + 1) §p{1}) →
          §SLCommon.Redo.prefixes{1} = pref) ∧
        SLCommon.Prefix.all_prefixes §SLCommon.Redo.prefixes{1} ∧
        (∀ j, 0 ≤ j ∧ j < §i0{1} →
          ∃ b c, (§SLCommon.Redo.prefixes{1}).get (take j §p{1}) = some (b, c) ∧
            (§Perm.m{1}).get (b +^ nth default §p{1} j, c) =
              (§SLCommon.Redo.prefixes{1}).get (take (j + 1) §p{1})))
      rotate_left
      -- EC: + auto;progress.
      --       - exact size_ge0.
      --       - by rewrite take0;have[]_[]->//=:=H.
      --       - smt().
      --       - by have[]->//=:=H.
      --       - smt(all_prefixes_of_INV_real).
      --       - smt().
      --       - smt().
      --     (four left after `progress`)
      · ec_auto; ec_progress
        · exact size_ge0 _
        · rw [take0]
          obtain ⟨-, ⟨h0, -⟩, -⟩ := ‹INV_Real _ _ _ _ _›
          exact h0
        · obtain ⟨h, -, -⟩ := ‹INV_Real _ _ _ _ _›
          omega
        · exact all_prefixes_of_INV_real _ _ _ _ _ ‹_› _ ‹_› _
      -- EC: if;auto;progress.
      --     - smt().
      --     - smt().
      --     - smt(domE).
      --     - smt(domE).
      --     - smt().
      --     - smt().
      --     - smt(all_prefixes_of_INV_real domE take_take size_take).
      --     (two left after `progress`: the known prefix's entry, and the step at `i0`)
      stmt_if
      · ec_close
      · ec_auto; ec_progress
        · exact FMap.get_some _ _ ‹_›
        --     - case(j < i0{2})=>hj;1:smt().
        --       have<<-/=:j = i0{2} by smt().
        --       have->>:=H7 H10 H12.
        --       have[]_[]hmp0 hmp1 _:=H2.
        --       have[]b3 c3:=hmp1 _ H12 j _;1:smt(size_take).
        --       smt(take_take nth_take size_take).
        · by_cases hj : j < i0₂
          · apply_assumption
            exact ⟨‹0 ≤ j›, hj⟩
          obtain rfl : i0₂ = j := by omega
          obtain ⟨-, ⟨-, hmp1⟩, -⟩ := ‹INV_Real count c₂ m₂ mi₂ prefixes₂›
          obtain ⟨b3, c3, hb, hm⟩ := hmp1 _ ‹FMap.dom prefixes₂ (take (i0₂ + 1) bl₂)› i0₂
            ⟨‹0 ≤ i0₂›, by rw [size_take (i0₂ + 1) bl₂ (by omega)]; split_ifs <;> omega⟩
          rw [SLCommon.Prefix.take_take, min_eq_left (show i0₂ ≤ i0₂ + 1 by omega)] at hb
          rw [nth_take default (i0₂ + 1) bl₂ i0₂ (by omega) (by omega),
            SLCommon.Prefix.take_take, min_self] at hm
          exact ⟨b3, c3, hb, hm⟩
      -- EC: sp;if;auto;progress.
      --     (GAP 8: the guard, the same state on both sides: its components are known equal,
      --     the closer does not put them together)
      stmt_sp; stmt_if
      · ec_prep
        have hx : x3₁ = x1₂ := Prod.ext (by simp only [*]) (by simp only [*])
        simp [hx]
      all_goals ec_auto
      all_goals ec_progress
      --     (the facts of the invariant, by their statements; the permutation's argument is the
      --     same state on both sides, GAP 8)
      all_goals
        have hx : x3₁ = x1₂ := Prod.ext (by simp only [*]) (by simp only [*])
        subst hx
        have hinv : INV_Real count c₂ m₂ mi₂ pref := by assumption
        have hall : SLCommon.Prefix.all_prefixes prefixes₂ := by assumption
        have hpl : ∀ l, FMap.dom pref l → pref.get l = prefixes₂.get l := by assumption
        have hdom : ∀ l, FMap.dom prefixes₂ l →
            FMap.dom pref l ∨ ∃ j, 0 < j ∧ j ≤ i0₂ ∧ l = take j bl₂ := by assumption
        have hstep : ∀ j : ℤ, 0 ≤ j ∧ j < i0₂ →
            ∃ b c, prefixes₂.get (take j bl₂) = some (b, c) ∧
              m₂.get (b +^ nth default bl₂ j, c) = prefixes₂.get (take (j + 1) bl₂) := by
          assumption
        have hnd : ¬ FMap.dom prefixes₂ (take (i0₂ + 1) bl₂) := by assumption
        have hi0 : 0 ≤ i0₂ := by assumption
        obtain ⟨sa, sc, hget, hx3⟩ : ∃ sa sc, prefixes₂.get (take i0₂ bl₂) = some (sa, sc) ∧
            x3₁ = (sa +^ nth default bl₂ i0₂, sc) :=
          ⟨_, _, ‹prefixes₂.get (take i0₂ bl₂) = some _›, Prod.ext ‹x3₁.1 = _› ‹x3₁.2 = _›⟩
        have hdi : FMap.dom prefixes₂ (take i0₂ bl₂) := (FMap.domE _ _).mpr (by rw [hget]; simp)
      --     - smt().
      --     - smt().
      · rfl
      · rfl
      --     - smt(get_setE domE).
      --     - rewrite INV_Real_addm_mi//=;smt(supp_dexcepted).
      · exact INV_Real_addm_mi _ _ _ _ _ _ _ hinv ‹¬ FMap.dom m₂ x3₁›
          (not_of_mem_support_dexcepted ‹_›)
      --     - smt(mem_set).
      · exact absorb_dom hdom hi0 _ _ ‹_›
      --     - smt(get_setE domE).
      · exact absorb_get hpl hnd _ _ ‹_›
      --     - smt().
      --     - smt().
      --     - move:H17;apply absurd=>//=_;rewrite mem_set.
      --       pose x:=_ = _;have->/={x}:x=false by smt(size_take).
      --       move:H12;apply absurd=>//= hpref.
      --       have:= H8 _ hpref (i0{2}+1).
      --       smt(mem_set take_take size_take).
      · exact absurd ‹_› (absorb_fresh hall hnd hi0 ‹_› _)
      --     - move=>l;rewrite!mem_set;case=>[H_dom i|->>]/=.
      --       * by rewrite mem_set;smt().
      --       move=>j; case(0 <= j)=>hj0; rewrite mem_set.
      --       * case: (j <= i0{2}) => hjmax; 2:smt(take_oversize size_take).
      --         left; have-> : take j (take (i0{2}+1) bl{2}) = take j (take i0{2} bl{2}).
      --         * by rewrite 2!take_take !minrE /#.
      --         by apply H8; rewrite domE H1.
      --       rewrite take_le0 1:/#; left.
      --       by rewrite-(take0 (take i0{2} bl{2})) H8 domE H1.
      · exact absorb_all_prefixes hall hdi _ _ ‹_› _
      --     - rewrite !get_set_sameE /=.
      --       rewrite get_set_neqE 1:/#.
      --       case: (j = i0{2})=> />.
      --       + by exists sa_R sc{2}; rewrite !get_set_sameE H1; case: y1L H14 H15.
      --       move=> neq_j_i0; move: (H9 j _); [1:smt()|2:case=> b' c' []].
      --       move=> ^ H18 -> H19; exists b' c'=> //=.
      --       by rewrite !get_set_neqE 1,2:/#.
      · exact absorb_step hall hnd hget hstep
          (fun x hx => FMap.get_set_neqE _ _ _ _ (by rintro rfl; exact ‹¬ FMap.dom m₂ _› hx)) _
          (by rw [← hx3]; exact FMap.get_some _ _ ((FMap.mem_set _ _ _ _).mpr (Or.inr rfl)))
          j ⟨‹0 ≤ j›, ‹j < i0₂ + 1›⟩
      --     - smt(get_setE domE).
      --     - smt().
      --     - smt(get_setE domE).
      · rfl
      · rfl
      · rfl
      --     - smt(mem_set).
      · exact absorb_dom hdom hi0 _ _ ‹_›
      --     - smt(get_setE domE).
      · exact absorb_get hpl hnd _ _ ‹_›
      --     - smt().
      --     - smt().
      --     - move:H15;apply absurd=>//=_;rewrite mem_set.
      --       pose x:=_ = _;have->/={x}:x=false by smt(size_take).
      --       move:H12;apply absurd=>//=.
      --       have:=take_take bl{2}(i0{2} + 1)(i0{2} + 1 + 1).
      --       rewrite minrE (: i0{2} + 1 <= i0{2} + 1 + 1) 1:/#=><-h.
      --       by rewrite (H8 _ h).
      · exact absurd ‹_› (absorb_fresh hall hnd hi0 ‹_› _)
      --     - move=>l;rewrite!mem_set;case=>[H_dom|->>]/=;1:smt(mem_set).
      --       move=>j;rewrite mem_set.
      --       case(0 <= j)=>hj0; last first.
      --       * rewrite take_le0 1:/#; left.
      --         by rewrite-(take0 (take i0{2} bl{2})) H8 domE H1.
      --       case(j < i0{2} + 1)=>hjiS;2:smt(domE take_take).
      --       rewrite take_take/min hjiS//=;left.
      --       have:=(take_take bl{2} j i0{2}).
      --       rewrite minrE (: j <= i0{2}) 1:/#=><-.
      --       smt(all_prefixes_of_INV_real domE).
      · exact absorb_all_prefixes hall hdi _ _ ‹_› _
      --     - rewrite get_set_neqE 1:/# get_setE; case: (j = i0{2})=> />.
      --       + move: H13; rewrite domE; case _: (Perm.m.[sa_R +^ nth witness bl i0, sc]{2})=> />.
      --         move=> [] b' c' /= p_sasc.
      --         by exists sa_R sc{2}.
      --       move=> j_neq_i0; move: (H9 j _); smt().
      · exact absorb_step hall hnd hget hstep (fun _ _ => rfl) _
          (by rw [← hx3]; exact FMap.get_some _ _ (of_decide_eq_true ‹_›))
          j ⟨‹0 ≤ j›, ‹j < i0₂ + 1›⟩
    -- EC: sp;case(0 < n{1});last first.
    --     (EC's `sp`: nothing to do here)
    equiv_case (0 < §n{1})
    -- EC: - rcondf{1}1;2:rcondf{2}1;auto;1:smt().
    on_goals 2 =>
      stmt_rcondf{1} 1
      on_goals 2 => stmt_rcondf{2} 1
      · intro σ₂; ec_auto
      · intro σ₁; ec_auto
      ec_auto; smt_close []
    -- EC: splitwhile{1} 1 : i + 1 < n;splitwhile{2} 1 : i + 1 < n.
    stmt_splitwhile{1} 1 : §i + 1 < §n
    stmt_splitwhile{2} 1 : §i + 1 < §n
    -- EC: rcondt{1}2;2:rcondt{2}2;auto;progress.
    --     + while(i < n);auto.
    --       by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    --     + while(i < n);auto.
    --       by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    stmt_rcondt{1} 2
    on_goals 2 => stmt_rcondt{2} 2
    · sponge_round
    · sponge_round
    -- EC: rcondf{1}4;2:rcondf{2}4;auto.
    --     + while(i < n);auto;2:smt().
    --       by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    --     + while(i < n);auto;2:smt().
    --       by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    stmt_rcondf{1} 4
    on_goals 2 => stmt_rcondf{2} 4
    · sponge_round
    · sponge_round
    -- EC: rcondf{1}4;2:rcondf{2}4;1,2:auto.
    --     + while(i < n);auto;2:smt().
    --       by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    --     + while(i < n);auto;2:smt().
    --       by sp;if;auto;sp;while(i < n);auto;if;auto;sp;if;auto.
    stmt_rcondf{1} 4
    on_goals 2 => stmt_rcondf{2} 4
    · sponge_round
    · sponge_round
    -- EC: conseq(:_==> ={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
    --            /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + i{1} - 1)
    --                  Perm.m{1} Perm.mi{1} Redo.prefixes{1}
    --            /\  i{1} = n{1});1:smt();wp.
    equiv_conseq (: _ ==> ={i, n, p, lres, nb, bl, b, Perm.m, Perm.mi, C.c,
        SLCommon.Redo.prefixes} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{2} + size §bl{2} + §i{1} - 1) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      §i{1} = §n{1})
    case post => smt_close []
    stmt_wp
    -- EC: conseq(:_==> ={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
    --            /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + i{1})
    --                  Perm.m{1} Perm.mi{1} Redo.prefixes{1}
    --            /\  i{1}+1 = n{1});1:smt().
    equiv_conseq (: _ ==> ={i, n, p, lres, nb, bl, b, Perm.m, Perm.mi, C.c,
        SLCommon.Redo.prefixes} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{2} + size §bl{2} + §i{1}) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      §i{1} + 1 = §n{1})
    case post => smt_close []
    -- EC: while(={i,n,p,lres,nb,bl,b,glob P,glob C,glob Redo}
    --            /\  INV_Real SLCommon.C.c{1} (C.c{2} + size bl{2} + i{1})
    --                  Perm.m{1} Perm.mi{1} Redo.prefixes{1}
    --            /\  (n,p){1} = (nb,bl){1} /\ 0 < i{1}+1 <= n{1}
    --            /\  valid p{1}
    --            /\  (exists c2, Redo.prefixes.[format p (i+1)]{1} = Some (b,c2){1}));
    --     last by auto;smt(nseq0 cats0).
    equiv_while (={i, n, p, lres, nb, bl, b, Perm.m, Perm.mi, C.c, SLCommon.Redo.prefixes} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{2} + size §bl{2} + §i{1}) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      (§n{1}, §p{1}) = (§nb{1}, §bl{1}) ∧ 0 < §i{1} + 1 ∧ §i{1} + 1 ≤ §n{1} ∧ valid §p{1} ∧
      ∃ c2, (§SLCommon.Redo.prefixes{1}).get (format §p{1} (§i{1} + 1)) = some (§b{1}, c2))
    rotate_left
    · ec_auto; ec_progress
      · exact ⟨sc₁, by rw [zero_add, format_one]; assumption⟩
      · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *
        omega
    -- EC: sp;rcondt{1}1;2:rcondt{2}1;auto.
    stmt_sp; stmt_rcondt{1} 1
    on_goals 2 => stmt_rcondt{2} 1
    · intro σ₂; ec_auto; ec_close
    · intro σ₁; ec_auto; ec_close
    -- EC: sp.
    stmt_sp
    -- EC: splitwhile{1} 1 : i1 < size p1 - 1;splitwhile{2} 1 : i1 < size p1 - 1.
    stmt_splitwhile{1} 1 : §i1 < size §p1 - 1
    stmt_splitwhile{2} 1 : §i1 < size §p1 - 1
    -- EC: rcondt{1}2;2:rcondt{2}2;1,2:by auto;
    --       while(i1 < size p1);auto;1:if;2:(sp;if);auto;smt(size_cat size_nseq size_ge0).
    stmt_rcondt{1} 2
    on_goals 2 => stmt_rcondt{2} 2
    · sponge_last
    · sponge_last
    -- EC: rcondf{1}4;2:rcondf{2}4;1,2:by auto;
    --       seq 1 : (i1 = size p1 - 1);1:(auto;
    --         while(i1 < size p1);auto;1:if;2:(sp;if);auto;smt(size_cat size_nseq size_ge0));
    --       if;sp;2:if;auto;smt(size_cat size_nseq size_ge0).
    stmt_rcondf{1} 4
    on_goals 2 => stmt_rcondf{2} 4
    · sponge_last
    · sponge_last
    -- EC: wp=>//=.
    stmt_wp
    -- EC: wp;conseq(:_==> ={sa0,sc0,glob Redo,glob Perm}
    --             /\ INV_Real SLCommon.C.c{1} (C.c{1} + size bl{2} + i{1})
    --                  Perm.m{1} Perm.mi{1} Redo.prefixes{1}
    --             /\ (format p{1} i{1} \in Redo.prefixes{1})
    --             /\ exists (c2 : capacity), Redo.prefixes{1}.[format p{1} (i{1}+1)] =
    --                  Some (sa0{1}, c2));progress.
    --     + smt(size_ge0).
    --     + smt(size_ge0).
    --     + smt().
    equiv_conseq (: _ ==> ={sa0, sc0, SLCommon.Redo.prefixes, Perm.m, Perm.mi} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{1} + size §bl{2} + §i{1}) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      FMap.dom §SLCommon.Redo.prefixes{1} (format §p{1} §i{1}) ∧
      ∃ c2 : capacity,
        (§SLCommon.Redo.prefixes{1}).get (format §p{1} (§i{1} + 1)) = some (§sa0{1}, c2))
    case post => ec_close
    -- EC: seq 1 1 : (={nb,bl,n,p,p1,i,i1,lres,sa0,sc0,C.c,glob Redo,glob Perm}
    --             /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p1{1} = format p{1} (i{1}+1)
    --             /\ 1 <= i{1} < n{1} /\ valid p{1} /\ i1{1} = size p1{1} - 1
    --             /\ Redo.prefixes{1}.[format p{1} i{1}] = Some (sa0{1},sc0{1})
    --             /\ INV_Real SLCommon.C.c{1} (C.c{1} + size bl{2} + i{1} - 1) Perm.m{1}
    --                  Perm.mi{1} Redo.prefixes{1});last first.
    equiv_seq 1 1 : (={nb, bl, n, p, p1, i, i1, lres, sa0, sc0, C.c, SLCommon.Redo.prefixes,
        Perm.m, Perm.mi} ∧
      §n{1} = §nb{1} ∧ §p{1} = §bl{1} ∧ §p1{1} = format §p{1} (§i{1} + 1) ∧
      1 ≤ §i{1} ∧ §i{1} < §n{1} ∧ valid §p{1} ∧ §i1{1} = size §p1{1} - 1 ∧
      (§SLCommon.Redo.prefixes{1}).get (format §p{1} §i{1}) = some (§sa0{1}, §sc0{1}) ∧
      INV_Real §SLCommon.C.c{1} (§C.c{1} + size §bl{2} + §i{1} - 1) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1})
    rotate_left
    -- EC: + if;auto;progress.
    · stmt_if
      · ec_close
      · ec_auto; ec_progress
        --     - by split;case:H3=>//=;smt().
        · obtain ⟨h, hm, hi⟩ := ‹INV_Real _ _ _ _ _›
          exact ⟨by omega, hm, hi⟩
        --     - by rewrite domE H2//=.
        · rw [FMap.domE, ‹prefixes₂.get (format p₂ i₂) = some _›]
          simp
        --     - move:H4;rewrite take_size /= domE=> h.
        --       exists (oget Redo.prefixes{2}.[format bl{2} (i{2} + 1)]).`2; move: h.
        --       by case: (Redo.prefixes{2}.[format bl{2} (i{2} + 1)]); smt().
        · have h := ‹FMap.dom prefixes₂ (take _ _)›
          rw [sub_add_cancel, take_size] at h ⊢
          exact ⟨_, FMap.get_some _ _ h⟩
      -- EC: sp;if;auto;progress.
      --     (GAP 8: the guard, the same state on both sides)
      stmt_sp; stmt_if
      · ec_prep
        have hx : x4₁ = x2₂ := Prod.ext (by simp only [*]) (by simp only [*])
        simp [hx]
      all_goals ec_auto
      all_goals ec_progress
      --     (EC's `rewrite nth_last take_size last_cat last_nseq addr0`, once for all the goals:
      --     the last block of `format p (i + 1)` is `b0`, and the permutation's argument the
      --     state recorded for `format p i`, the same on both sides, GAP 8)
      all_goals
        have hx : x4₁ = x2₂ := Prod.ext (by simp only [*]) (by simp only [*])
        have hi : 1 ≤ i₂ := by assumption
        have hinv : INV_Real (SLCommon_C_c₁ + 1) (c₂ + size p₂ + i₂) m₂ mi₂ prefixes₂ := by
          obtain ⟨h, hm, hi'⟩ := ‹INV_Real _ _ _ _ _›
          exact ⟨by omega, hm, hi'⟩
        obtain ⟨sa0, sc0, hget, hx4⟩ : ∃ sa0 sc0, prefixes₂.get (format p₂ i₂) = some (sa0, sc0) ∧
            x4₁ = (sa0, sc0) :=
          ⟨_, _, ‹prefixes₂.get (format p₂ i₂) = some _›,
            Prod.ext (by rw [‹x4₁.1 = _›, nth_last, format, last_cat,
              last_nseq _ (i₂ + 1 - 1) b0 (by omega), xorw_b0]) ‹x4₁.2 = _›⟩
        subst hx
        subst hx4
        have hget' : prefixes₂.get (format p₂ (i₂ + 1 - 1)) = some (sa0, sc0) := by
          rw [add_sub_cancel_right]
          exact hget
        simp only [sub_add_cancel, take_size] at *
      --     (the equalities of the two sides' states are closed with it)
      --     - move:H4 H5;rewrite!get_setE/= nth_last/=take_size.
      --       rewrite last_cat last_nseq 1:/# Block.WRing.addr0;progress.
      --       have//=:=lemma2'(SLCommon.C.c{1} + 1)(C.c{2} + size bl{2} + i{2})
      --         Perm.m{2}.[(sa0_R, sc0{2}) <- y2L] Perm.mi{2}.[y2L <- (sa0_R, sc0{2})]
      --         Redo.prefixes{2} bl{2} (i{2}+1) sa0_R sc0{2}.
      --       rewrite H1/=!mem_set/=H4/=H2/=get_setE/=.
      --       have->->//=:y2L = (y2L.`1, y2L.`2);1,-1:smt().
      --       rewrite INV_Real_addm_mi//=;2:smt(supp_dexcepted).
      --       by have:=H3=>hinv0;split;case:hinv0=>//=/#.
      · exact lemma2' _ _ _ _ _ p₂ (i₂ + 1) sa0 sc0
          (INV_Real_addm_mi _ _ _ _ _ _ _ hinv ‹¬ FMap.dom m₂ (sa0, sc0)›
            (not_of_mem_support_dexcepted ‹_›))
          (by omega) ‹valid p₂ = true› ((FMap.mem_set _ _ _ _).mpr (Or.inr rfl)) ‹_› hget'
      --     - by rewrite mem_set//=take_size domE H2.
      · exact (FMap.mem_set _ _ _ _).mpr (Or.inl ((FMap.domE _ _).mpr (by rw [hget]; simp)))
      --     - by rewrite!get_setE take_size/=;smt().
      · exact ⟨_, FMap.get_set_sameE _ _ _⟩
      --     - move:H4 H5;rewrite nth_last take_size.
      --       rewrite last_cat last_nseq 1:/# Block.WRing.addr0;progress.
      --       pose a:=(_, _);have->/={a}:a = oget Perm.m{2}.[(sa0_R, sc0{2})] by smt().
      --       apply lemma2'=>//=;first have:=H3=>hinv0;split;case:hinv0=>//=/#.
      --       smt().
      · exact lemma2' _ _ _ _ _ p₂ (i₂ + 1) sa0 sc0 hinv (by omega) ‹valid p₂ = true›
          (of_decide_eq_true ‹_›) ‹_› hget'
      --     - by rewrite mem_set//=take_size;smt(domE).
      · exact (FMap.mem_set _ _ _ _).mpr (Or.inl ((FMap.domE _ _).mpr (by rw [hget]; simp)))
      --     - by rewrite!get_setE/=take_size/=;smt().
      · exact ⟨_, FMap.get_set_sameE _ _ _⟩
    -- EC: alias{1} 1 pref = Redo.prefixes;sp;alias{1} 1 count = SLCommon.C.c.
    stmt_alias{1} 1 pref = §SLCommon.Redo.prefixes
    stmt_sp
    stmt_alias{1} 1 count = §SLCommon.C.c
    -- EC: alias{1} 1 pm = Perm.m;sp;alias{1} 1 pmi = Perm.mi;sp.
    stmt_alias{1} 1 pm = §Perm.m
    stmt_sp
    stmt_alias{1} 1 pmi = §Perm.mi
    stmt_sp
    -- EC: conseq(:_==> ={nb,bl,n,p,p1,i,i1,lres,sa0,sc0,C.c,glob Redo,glob Perm}
    --           /\ pmi{1} = Perm.mi{1} /\ pm{1} = Perm.m{1}
    --           /\ pref{1} = Redo.prefixes{1} /\ SLCommon.C.c{1} = count{1}
    --           /\ n{1} = nb{1} /\ p{1} = bl{1} /\ p1{1} = format p{1} (i{1}+1)
    --           /\ i1{1} = size p1{1} - 1
    --           /\ Redo.prefixes{1}.[format p{1} (i1{1} - size p{1} + 1)] =
    --                Some (sa0{1}, sc0{1}));progress.
    equiv_conseq (: _ ==> ={nb, bl, n, p, p1, i, i1, lres, sa0, sc0, C.c, SLCommon.Redo.prefixes,
        Perm.m, Perm.mi} ∧
      §pmi{1} = §Perm.mi{1} ∧ §pm{1} = §Perm.m{1} ∧ §pref{1} = §SLCommon.Redo.prefixes{1} ∧
      §SLCommon.C.c{1} = §count{1} ∧
      §n{1} = §nb{1} ∧ §p{1} = §bl{1} ∧ §p1{1} = format §p{1} (§i{1} + 1) ∧
      §i1{1} = size §p1{1} - 1 ∧
      (§SLCommon.Redo.prefixes{1}).get (format §p{1} (§i1{1} - size §p{1} + 1)) =
        some (§sa0{1}, §sc0{1}))
    --     + smt().
    --     + by move: H8; rewrite size_cat size_nseq /= ler_maxr /#.
    --     + move:H8;rewrite size_cat size_nseq/=/max H0/=;smt().
    --     (two left after `progress`)
    case post =>
      ec_progress
      · have h := ‹Redo_prefixes₂.get (format p₂1 _) = some (sa0₂1, sc0₂1)›
        convert h using 3
        rw [size_format]
        omega
      · obtain ⟨h, hm, hi⟩ := ‹INV_Real _ _ _ _ _›
        exact ⟨by omega, hm, hi⟩
    -- EC: splitwhile{1}1:i1 < size p;splitwhile{2}1:i1 < size p.
    --     (GAP 10: `p` is not in the code left, and `splitwhile` reads the code's variables
    --     only: `p` by its lens)
    stmt_splitwhile{1} 1 : §i1 < size §(localVarLens "p" (List block))
    stmt_splitwhile{2} 1 : §i1 < size §(localVarLens "p" (List block))
    -- EC: while(...)
    equiv_while (={nb, bl, n, p, p1, i, i1, lres, sa0, sc0, C.c, SLCommon.Redo.prefixes,
        Perm.m, Perm.mi} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{1} + size §bl{2} + §i{1} - 1) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      §pmi{1} = §Perm.mi{1} ∧ §pm{1} = §Perm.m{1} ∧ §pref{1} = §SLCommon.Redo.prefixes{1} ∧
      §SLCommon.C.c{1} = §count{1} ∧
      §n{1} = §nb{1} ∧ §p{1} = §bl{1} ∧ §p1{1} = format §p{1} (§i{1} + 1) ∧
      FMap.dom §SLCommon.Redo.prefixes{1} (format §p{1} §i{1}) ∧
      size §p{1} ≤ §i1{1} ∧ §i1{1} ≤ size §p1{1} - 1 ∧ valid §p{1} ∧
      (§SLCommon.Redo.prefixes{1}).get (format §p{1} (§i1{1} - size §p{1} + 1)) =
        some (§sa0{1}, §sc0{1}))
    -- EC: + rcondt{1}1;2:rcondt{2}1;auto;progress.
    --       + have->:take (i1{m} + 1) (format bl{m} (i{m} + 1)) =
    --               take (i1{m} + 1) (format bl{m} i{m});2:smt(all_prefixes_of_INV_real).
    --         smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    --       + have->:take (i1{hr} + 1) (format bl{hr} (i{hr} + 1)) =
    --               take (i1{hr} + 1) (format bl{hr} i{hr});2:smt(all_prefixes_of_INV_real).
    --         smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    · stmt_rcondt{1} 1
      on_goals 2 => stmt_rcondt{2} 1
      · intro σ₂; ec_auto; ec_prep
        exact squeeze_known_tail ‹INV_Real _ _ _ _ _› ‹FMap.dom _ (format _ _)› ‹size _ ≤ _›
          (by simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
      · intro σ₁; ec_auto; ec_prep
        exact squeeze_known_tail ‹INV_Real _ _ _ _ _› ‹FMap.dom _ (format _ _)› ‹size _ ≤ _›
          (by simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
      ec_auto; ec_progress
      --       + smt().
      --       + smt(size_cat size_nseq).
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at *
        omega
      --       + have->:take (i1{2} + 1) (format bl{2} (i{2} + 1)) =
      --                take (i1{2} + 1) (format bl{2} i{2}).
      --         - smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
      --         have->:format bl{2} (i1{2} + 1 - size bl{2} + 1) =
      --                take (i1{2} + 1) (format bl{2} i{2}).
      --         - smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
      --         have all_pref:=all_prefixes_of_INV_real _ _ _ _ _ H.
      --         by have:=all_pref _ H0 (i1{2}+1); rewrite domE; smt().
      · have hg : i1₂ < size (format p₂ (i₂ + 1)) - 1 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          omega
        have hk := squeeze_known_tail ‹INV_Real _ _ _ _ _› ‹FMap.dom prefixes₂ (format p₂ i₂)›
          ‹size p₂ ≤ i1₂› hg
        have hs := size_format p₂ (i₂ + 1)
        have hp := size_ge0 p₂
        rw [take_format p₂ (i₂ + 1) (i1₂ + 1) (by omega) ⟨by omega, by omega⟩,
          if_neg (by omega)] at hk ⊢
        exact FMap.get_some _ _ hk
    -- EC: conseq(...)
    equiv_conseq (: _ ==> ={nb, bl, n, p, p1, i, i1, lres, sa0, sc0, C.c, SLCommon.Redo.prefixes,
        Perm.m, Perm.mi} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{1} + size §bl{2} + §i{1} - 1) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      §pmi{1} = §Perm.mi{1} ∧ §pm{1} = §Perm.m{1} ∧ §pref{1} = §SLCommon.Redo.prefixes{1} ∧
      §SLCommon.C.c{1} = §count{1} ∧
      §n{1} = §nb{1} ∧ §p{1} = §bl{1} ∧ §p1{1} = format §p{1} (§i{1} + 1) ∧
      FMap.dom §SLCommon.Redo.prefixes{1} (format §p{1} §i{1}) ∧
      §i1{1} = size §p{1} ∧ valid §p{1} ∧
      (§SLCommon.Redo.prefixes{1}).get (take §i1{1} §p{1}) = some (§sa0{1}, §sc0{1}))
    --       1:smt(size_cat size_nseq nseq0 cats0 take_size).
    case post =>
      ec_progress
      · rw [size_format]
        omega
      · have h := ‹Redo_prefixes₂.get (take _ _) = some _›
        rw [take_size] at h
        rw [sub_self, zero_add, format_one]
        exact h
      · sponge_guard
    -- EC: while(...);last first.
    equiv_while (={nb, bl, n, p, p1, i, i1, lres, sa0, sc0, C.c, SLCommon.Redo.prefixes,
        Perm.m, Perm.mi} ∧
      INV_Real §SLCommon.C.c{1} (§C.c{1} + size §bl{2} + §i{1} - 1) §Perm.m{1} §Perm.mi{1}
        §SLCommon.Redo.prefixes{1} ∧
      §pmi{1} = §Perm.mi{1} ∧ §pm{1} = §Perm.m{1} ∧ §pref{1} = §SLCommon.Redo.prefixes{1} ∧
      §SLCommon.C.c{1} = §count{1} ∧
      §n{1} = §nb{1} ∧ §p{1} = §bl{1} ∧ §p1{1} = format §p{1} (§i{1} + 1) ∧
      FMap.dom §SLCommon.Redo.prefixes{1} (format §p{1} §i{1}) ∧
      0 ≤ §i1{1} ∧ §i1{1} ≤ size §p{1} ∧ valid §p{1} ∧
      (§SLCommon.Redo.prefixes{1}).get (take §i1{1} §p{1}) = some (§sa0{1}, §sc0{1}))
    rotate_left
    -- EC: + auto;progress.
    --     - smt().
    --     - have[]_[]:=H;smt(domE).
    --     - exact size_ge0.
    --     - have[]_[]:=H;smt(domE take0).
    --     - smt(size_cat size_nseq).
    · ec_auto; ec_progress
      · obtain ⟨h, hm, hi⟩ := ‹INV_Real _ _ _ _ _›
        exact ⟨by omega, hm, hi⟩
      · rw [FMap.domE, ‹prefixes₂.get (format bl₂ _) = some _›]
        simp
      · exact size_ge0 _
      · rw [take0]
        obtain ⟨-, ⟨h0, -⟩, -⟩ := ‹INV_Real _ _ _ _ _›
        exact h0
      · sponge_guard
    -- EC: rcondt{1}1;2:rcondt{2}1;auto;progress.
    --     - have->:take (i1{m} + 1) (format bl{m} (i{m} + 1)) =
    --             take (i1{m} + 1) (format bl{m} i{m});2:smt(all_prefixes_of_INV_real).
    --       smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    --     - have->:take (i1{hr} + 1) (format bl{hr} (i{hr} + 1)) =
    --             take (i1{hr} + 1) (format bl{hr} i{hr});2:smt(all_prefixes_of_INV_real).
    --       smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    stmt_rcondt{1} 1
    on_goals 2 => stmt_rcondt{2} 1
    · intro σ₂; ec_auto; ec_prep
      exact squeeze_known_head ‹INV_Real _ _ _ _ _› ‹FMap.dom _ (format _ _)›
        (by simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
    · intro σ₁; ec_auto; ec_prep
      exact squeeze_known_head ‹INV_Real _ _ _ _ _› ‹FMap.dom _ (format _ _)›
        (by simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
    --     - smt().
    --     - smt().
    --     - have->:take (i1{2} + 1) (format bl{2} (i{2} + 1)) =
    --             take (i1{2} + 1) (format bl{2} i{2})
    --         by smt(take_format size_ge0 size_eq0 valid_spec size_cat size_nseq).
    --       have->:take (i1{2} + 1) bl{2} =
    --             take (i1{2} + 1) (format bl{2} i{2})
    --         by smt(take_cat take_le0 cats0).
    --       smt(all_prefixes_of_INV_real).
    ec_auto; ec_progress
    have hg : i1₂ < size p₂ := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      omega
    have hk := squeeze_known_head (i := i₂) ‹INV_Real _ _ _ _ _› ‹FMap.dom prefixes₂ (format p₂ i₂)›
      hg
    rw [take_format_le p₂ (i₂ + 1) (i1₂ + 1) (by omega)] at hk ⊢
    exact FMap.get_some _ _ hk

set_option hygiene false in
/-- EC's `by while(i<n);auto;2:smt();sp;if;auto;sp;if;auto.`, the side goal of each `rcond` on the
last round of the sponge's squeezing loop (the right side of `squeeze_squeezeless`): the loop
keeps `i < n`.  (No hygiene: `§i`, `§n` are the program's variables.) -/
local macro "sponge_round_r" : tactic => `(tactic| (
  intro σ
  (try stmt_wp)
  hoare_while (§i < §n)
  · ec_auto <;> ec_close
  · ec_close
  · ec_auto <;> ec_close))

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- A known next prefix is the permutation's step from the current one.  EC proves it inline at
each use in `squeeze_squeezeless`'s absorbing loop (`have[]_[]_ hmp1 _ :=H2;have:=hmp1 _ H5 i0
_;1:smt(size_take). move=>[]b3 c3;rewrite!take_take!nth_take …`, five times). -/
theorem INV_Real_known_step {c1 c2 : ℤ} {m mi : FMap SLCommon.state SLCommon.state}
    {P : FMap (List block) SLCommon.state} {l : List block} {i : ℤ} {sa : block} {sc : capacity}
    (hinv : INV_Real c1 c2 m mi P) (hi : 0 ≤ i ∧ i < size l) (hd : FMap.dom P (take (i + 1) l))
    (hget : P.get (take i l) = some (sa, sc)) :
    m.get (sa +^ nth default l i, sc) = P.get (take (i + 1) l) := by
  obtain ⟨-, ⟨-, hmp1⟩, -⟩ := hinv
  obtain ⟨b, c, hb, hm⟩ := hmp1 _ hd i
    ⟨hi.1, by rw [size_take (i + 1) l (by omega)]; split_ifs <;> omega⟩
  rw [SLCommon.Prefix.take_take, min_eq_left (show i ≤ i + 1 by omega), hget] at hb
  rw [nth_take default (i + 1) l i (by omega) (by omega), SLCommon.Prefix.take_take,
    min_self] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
  exact hm

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- EC's `rewrite take_oversize;1:rewrite size_cat size_nseq ler_maxr/#` at `i1 = size p + i - 1`:
the whole of `format p (i + 1)`. -/
theorem take_format_full (bl : List block) (i : ℤ) (hi : 0 < i) :
    take (size bl + i - 1 + 1) (format bl (i + 1)) = format bl (i + 1) :=
  take_oversize _ _ (by rw [size_format]; omega)

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- EC's `rewrite nth_cat nth_nseq;1:smt(size_ge0). have->/=:!size p + i - 1 < size p by smt()`
at `i1 = size p + i - 1`: the last block of `format p (i + 1)` is `b0`. -/
theorem nth_format_pad (bl : List block) (i : ℤ) (hi : 0 < i) :
    nth default (format bl (i + 1)) (size bl + i - 1) = b0 := by
  rw [format, nth_cat, if_neg (by omega), nth_nseq _ _ _ _ ⟨by omega, by omega⟩]

/-- A prefix of `format p (i + 1)`, but for the last block, is known (`0 < i`). -/
theorem squeeze_known {c1 c2 : ℤ} {m mi : FMap SLCommon.state SLCommon.state}
    {P : FMap (List block) SLCommon.state} {bl : List block} {i i1 : ℤ}
    (hinv : INV_Real c1 c2 m mi P) (hd : FMap.dom P (format bl i)) (hi : 0 < i)
    (hlt : i1 < size (format bl (i + 1)) - 1) :
    FMap.dom P (take (i1 + 1) (format bl (i + 1))) := by
  rw [take_format_succ bl i (i1 + 1) hi (by rw [size_format] at hlt ⊢; omega)]
  exact all_prefixes_of_INV_real _ _ _ _ _ hinv _ hd _

omit [BlockSponge.Params] [Gconcl_list.Params] in
/-- EC's `rewrite take_format … have->: x = format p (i_R+1)`: `format p (j + 1)` without its
last block is `format p j`. -/
theorem take_format_pred (bl : List block) (j : ℤ) (hj : 0 < j) :
    take (size (format bl (j + 1)) - 1) (format bl (j + 1)) = format bl j := by
  have hk : size (format bl (j + 1)) - 1 = size (format bl j) := by
    rw [size_format, size_format]
    omega
  rw [hk, take_format_succ bl j _ hj le_rfl, take_size]

-- the functionality's oracle: the squeezeless sponge's two loops against the sponge's
set_option maxHeartbeats 16000000 in
/-- EC's `local lemma squeeze_squeezeless (D <: DISTINGUISHER {-P, -Redo, -C, -SLCommon.C}) :
equiv [ NIndif(Squeeze(SqueezelessSponge(P)),P,DRestr(D)).main ~
RealIndif(Sponge,P,DRestr(D)).main : ={glob D} ==> ={res, glob P, glob D, C.c} /\
C.c{1} <= max_size]`.

Deviations: `Perm` for EC's `P`, `glob P` its two maps (as `equiv_sponge`); GAP 11 of the file
header (one bridge line after `inline*`); the facts EC proves inline at each use are the lemmas
above (`INV_Real_known_step`, `squeeze_known`, `take_format_full`, `nth_format_pad`,
`take_format_pred`); EC's one goal on the body of `while{1}` is our two. -/
theorem squeeze_squeezeless :
    ∀ (D <: DISTINGUISHER {-Perm, -SLCommon.Redo, -C, -SLCommon.C}),
    equiv[ NIndif(Squeeze(SLCommon.SqueezelessSponge(Perm)), Perm, DRestr(D)).main ~
      RealIndif(Sponge, Perm, DRestr(D)).main :
      ={glob D} ==> ={res, Perm.m, Perm.mi, glob D, C.c} ∧ §C.c{1} ≤ max_size ] := by
  intro D _
  -- EC: proc;inline*;sp;wp.
  equiv_proc; stmt_inline*; stmt_sp; stmt_wp
  -- EC: call(: ={glob Perm,C.c} /\ C.c{1} <= max_size
  --       /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});auto;last first.
  equiv_call (_ : ={Perm.m, Perm.mi, C.c} ∧ §C.c{1} ≤ max_size ∧
    INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
  rotate_right
  -- EC: + progress.
  --       + exact max_ge0.
  --       split=>//=;1:split=>//=;smt(get_setE mem_empty emptyE in_fset0 mem_set).
  · ec_auto; ec_progress
    · exact SLCommon.max_ge0
    --     (the old port's `INV_Real_init`)
    · exact INV_Real_init
  -- EC: + proc;inline*;auto;sp;if;auto;sp;if;auto;progress.
  --       - by rewrite INV_Real_addm_mi;2..:smt(supp_dexcepted);split;case:H0=>//=;smt().
  --       - by split;case:H0=>//=;smt().
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto; stmt_sp; stmt_if
    · ec_close
    all_goals ec_auto
    all_goals ec_progress
    · exact INV_Real_addm_mi _ _ _ _ _ _ _ (INV_Real_mono ‹_› (by omega)) ‹¬ _›
        (not_of_mem_support_dexcepted ‹_›)
    · exact INV_Real_mono ‹_› (by omega)
  -- EC: + proc;inline*;auto;sp;if;auto;sp;if;auto;progress.
  --       - rewrite INV_Real_addm_mi;1: by split;case:H0=>//=;smt().
  --         * case:H0;smt(invm_dom_rng invmC supp_dexcepted).
  --         case:H0;smt(invm_dom_rng invmC supp_dexcepted).
  --       - by split;case:H0=>//=;smt().
  · equiv_proc; stmt_inline*; stmt_sp; stmt_if
    · ec_close
    on_goals 2 => ec_auto
    ec_auto; stmt_sp; stmt_if
    · ec_close
    all_goals ec_auto
    all_goals ec_progress
    · obtain ⟨H_c, H_m_p, H_invm⟩ := ‹INV_Real _ _ _ _ _›
      apply INV_Real_addm_mi _ _ _ _ _ _ _ ⟨by omega, H_m_p, H_invm⟩
      · rw [invm_dom_rng _ _ H_invm]
        exact not_of_mem_support_dexcepted ‹_›
      · rw [← invm_dom_rng _ _ ((invmC _ _).mp H_invm)]
        assumption
    · exact INV_Real_mono ‹_› (by omega)
  -- EC: proc;inline*;sp;auto;if;auto;sp;if;auto;
  --       last by progress;split;case:H0=>//=;smt(size_ge0).
  equiv_proc; stmt_inline*
  --     (GAP 11: `Sponge(Perm)`'s calls of the permutation, behind the first port's view of
  --     `Perm`, are not opened by `inline*`: the first port's `P_view`, then `inline*` again)
  simp only [P_view]
  stmt_inline*
  stmt_sp; stmt_if
  · ec_close
  on_goals 2 => ec_auto
  --     (the guard: EC's `valid` is `valid_block` by definition, ours its test)
  ec_auto; stmt_sp; stmt_if
  · ec_prep
    rw [valid, ‹x0₁.1 = _›, ‹x0₂.1 = _›]
  on_goals 2 =>
    ec_auto; ec_progress
    exact INV_Real_mono ‹_› (by have := size_ge0 x0₁.1; omega)
  -- EC: conseq(: (exists (c_R : int),
  --         C.c{2} = c_R + size bl{2} + max (nb{2} - 1) 0 /\ xs{2} = bl{2} /\
  --         n{2} = nb{2} /\ z0{2} = [] /\ sc{2} = c0 /\ sa{2} = b0 /\ i{2} = 0 /\
  --         exists (c_L : int), C.c{1} = c_L + size bl{1} + max (nb{1} - 1) 0 /\
  --         p{1} = bl{1} /\ n{1} = nb{1} /\ lres{1} = [] /\ b{1} = b0 /\
  --         i{1} = 0 /\ z{2} = [] /\ z{1} = [] /\ ={bl, nb} /\
  --         ={Perm.mi, Perm.m} /\ c_L = c_R /\
  --         INV_Real 0 c_L Perm.m{1} Perm.mi{1} Redo.prefixes{1} /\ valid p{1})
  --       ==> lres{1} = z0{2} /\ ={Perm.mi, Perm.m} /\ ={C.c} /\
  --         INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});1,2:smt().
  equiv_conseq (: (∃ c_R : ℤ,
      §C.c{2} = c_R + size §bl{2} + max (§nb{2} - 1) 0 ∧ §xs{2} = §bl{2} ∧
      §n{2} = §nb{2} ∧ §z0{2} = [] ∧ §sc{2} = c0 ∧ §sa{2} = b0 ∧ §i{2} = 0 ∧
      ∃ c_L : ℤ, §C.c{1} = c_L + size §bl{1} + max (§nb{1} - 1) 0 ∧
      §p{1} = §bl{1} ∧ §n{1} = §nb{1} ∧ §lres{1} = [] ∧ §b{1} = b0 ∧
      §i{1} = 0 ∧ §z{2} = [] ∧ §z{1} = [] ∧ ={bl, nb} ∧
      ={Perm.mi, Perm.m} ∧ c_L = c_R ∧
      INV_Real 0 c_L §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1} ∧ valid §p{1})
    ==> §lres{1} = §z0{2} ∧ ={Perm.mi, Perm.m} ∧ ={C.c} ∧
      INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
  case pre => ec_close
  case post => ec_close
  -- EC: sp.
  stmt_sp
  -- EC: seq 2 1 : (={glob P, i, n, C.c,sa,sc}
  --       /\ b{1} = sa{2} /\ Redo.prefixes.[p]{1} = Some (sa,sc){2}
  --       /\ lres{1} = z0{2} /\ i{1} = 0 /\ valid p{1}
  --       /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}).
  equiv_seq 2 1 : (={Perm.m, Perm.mi, i, n, C.c, sa, sc} ∧
    §b{1} = §sa{2} ∧ (§SLCommon.Redo.prefixes{1}).get §p{1} = some (§sa{2}, §sc{2}) ∧
    §lres{1} = §z0{2} ∧ §i{1} = 0 ∧ valid §p{1} ∧
    INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
  -- EC: + conseq(:_==> ={glob P, n, C.c,sa,sc} /\ b{1} = sa{2} /\ i0{1} = size p0{1}
  --           /\ Redo.prefixes{1}.[take i0{1} p0{1}] = Some (sa{1}, sc{1})
  --           /\ lres{1} = z0{2} /\ xs{2} = drop i0{1} p0{1}
  --           /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});
  --         1:smt(take_size drop_size).
  · equiv_conseq (: _ ==> ={Perm.m, Perm.mi, n, C.c, sa, sc} ∧ §b{1} = §sa{2} ∧
      §i0{1} = size §p0{1} ∧
      (§SLCommon.Redo.prefixes{1}).get (take §i0{1} §p0{1}) = some (§sa{1}, §sc{1}) ∧
      §lres{1} = §z0{2} ∧ §xs{2} = drop §i0{1} §p0{1} ∧
      INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
    case post =>
      ec_progress
      have h := ‹Redo_prefixes₁.get (take _ _) = some _›
      rwa [take_size] at h
    -- EC: wp;while(={glob P, n, C.c,sa,sc} /\ sa{1} = sa{2} /\ sc{1} = sc{2}
    --         /\ 0 <= i0{1} <= size p0{1}
    --         /\ Redo.prefixes{1}.[take i0{1} p0{1}] = Some (sa{1}, sc{1})
    --         /\ lres{1} = z0{2} /\ xs{2} = drop i0{1} p0{1}
    --         /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}).
    stmt_wp
    equiv_while (={Perm.m, Perm.mi, n, C.c, sa, sc} ∧ §sa{1} = §sa{2} ∧ §sc{1} = §sc{2} ∧
      0 ≤ §i0{1} ∧ §i0{1} ≤ size §p0{1} ∧
      (§SLCommon.Redo.prefixes{1}).get (take §i0{1} §p0{1}) = some (§sa{1}, §sc{1}) ∧
      §lres{1} = §z0{2} ∧ §xs{2} = drop §i0{1} §p0{1} ∧
      INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
    rotate_left
    -- EC: auto;progress.
    --     + exact size_ge0.
    --     + by rewrite take0;have[]_[]->:=H.
    --     + by rewrite drop0.
    --     + split;case:H=>//=;smt(size_ge0).
    --     + smt(size_ge0 size_eq0).
    --     + smt(size_ge0 size_eq0).
    --     + smt().
    · ec_auto; ec_progress
      · exact size_ge0 _
      · rw [take0]
        obtain ⟨-, ⟨h0, -⟩, -⟩ := ‹INV_Real _ _ _ _ _›
        exact h0
      · exact INV_Real_mono ‹_› (by have := size_ge0 xs₂; omega)
      · have h := decide_lt_size_drop xs₂ 0 le_rfl
        rwa [drop0] at h
    -- EC: + if{1};auto.
    stmt_if{1}
    -- EC:   + sp;rcondf{2}1;auto;progress.
    --         + rewrite head_nth nth_drop//=.
    --           have[]_[]_ hmp1 _ :=H2;have:=hmp1 _ H5 i0{m} _;1:smt(size_take).
    --           move=>[]b3 c3;rewrite!take_take!nth_take 1,2:/# !minrE //=
    --             (: i0{m} <= i0{m} + 1) 1:/#.
    --           rewrite H1=>//=[][][]->>->>.
    --           by rewrite nth_onth (onth_nth b0)//=;smt(domE).
    --         (and four more times, on the values; `INV_Real_known_step`)
    · ec_auto; stmt_sp; stmt_rcondf{2} 1
      · intro σ₁; ec_auto; ec_prep
        have hi : (0 : ℤ) ≤ _ ∧ (_ : ℤ) < size (_ : List block) := ⟨‹_›, ‹_›⟩
        have hk := INV_Real_known_step ‹INV_Real _ _ _ _ _› hi ‹FMap.dom _ (take _ _)›
          ‹_ = some _›
        rw [head_drop_nth _ _ _ hi, Bool.not_false, decide_eq_true_eq, FMap.domE, hk,
          ← FMap.domE]
        assumption
      ec_auto; ec_progress
      all_goals
        have hi : 0 ≤ i0₁ ∧ i0₁ < size p0₁ := ⟨by assumption, by assumption⟩
        have hk := INV_Real_known_step ‹INV_Real _ _ _ _ _› hi ‹FMap.dom prefixes₁ _›
          ‹prefixes₁.get _ = some _›
      · rw [head_drop_nth b0 p0₁ i0₁ hi, hk]
      · rw [head_drop_nth b0 p0₁ i0₁ hi, hk]
      · rw [head_drop_nth b0 p0₁ i0₁ hi, hk]
      · rw [head_drop_nth b0 p0₁ i0₁ hi, hk]
      --         + smt().
      --         + smt().
      --         + smt().
      · exact FMap.get_some _ _ ‹_›
      --         + smt(behead_drop drop_add).
      · exact behead_drop_succ _ _ hi.1
      --         + smt(size_drop size_eq0).
      --         + smt(size_drop size_eq0).
      · rw [behead_drop_succ _ _ hi.1]
        exact decide_lt_size_drop _ _ (by omega)
    -- EC: sp=>//=.
    --     if;auto;progress.
    --     (GAP 8: the guard, the same state on both sides)
    ec_auto; stmt_sp; stmt_if
    · ec_prep
      have hi : 0 ≤ i0₁ ∧ i0₁ < size p0₁ := ⟨by assumption, by assumption⟩
      have h1 := ‹x1₁.1 = _›
      have h2 := ‹x1₁.2 = _›
      rw [head_drop_nth b0 p0₁ i0₁ hi, ← h1, ← h2]
      simp
    all_goals ec_auto
    all_goals ec_progress
    all_goals
      have hi : 0 ≤ i0₁ ∧ i0₁ < size p0₁ := ⟨by assumption, by assumption⟩
      have h1 := ‹x1₁.1 = _›
      have h2 := ‹x1₁.2 = _›
    --     + by rewrite head_nth nth_drop //=nth_onth (onth_nth witness)//=.
    --     + by move:H6;rewrite head_nth nth_drop //=nth_onth (onth_nth witness)//=.
    --     + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=.  (six times)
    --     + smt().
    --     + smt().
    --     + by rewrite get_setE/=.
    · rw [head_drop_nth b0 p0₁ i0₁ hi, ← h1, ← h2]
    · rw [head_drop_nth b0 p0₁ i0₁ hi, ← h1, ← h2]
    --     + by rewrite behead_drop drop_add.
    · exact behead_drop_succ _ _ hi.1
    --     + rewrite!get_setE/=.
    --       have:=lemma_3 0 C.c{2}Perm.m{2}.[(sa{2} +^ nth witness p0{1} i0{1}, sc{2}) <- yL]
    --         Perm.mi{2}.[yL <- (sa{2} +^ nth witness p0{1} i0{1}, sc{2})] Redo.prefixes{1}
    --         (take i0{1} p0{1}) (nth witness p0{1} i0{1}) sa{2} sc{2}.
    --       rewrite!mem_set/=-take_nth//=H5/=H1/=get_setE/=.
    --       have->->//=:(yL.`1, yL.`2) = yL by smt().
    --       rewrite INV_Real_addm_mi=>//=;smt(supp_dexcepted).
    · obtain ⟨sa, sc, hget, rfl⟩ : ∃ sa sc, prefixes₁.get (take i0₁ p0₁) = some (sa, sc) ∧
          x1₁ = (sa +^ nth default p0₁ i0₁, sc) :=
        ⟨_, _, ‹prefixes₁.get (take i0₁ p0₁) = some _›, Prod.ext h1 h2⟩
      have h3 := lemma_3 0 c₂ _ _ prefixes₁ (take i0₁ p0₁) (nth default p0₁ i0₁) sa sc
        (INV_Real_addm_mi _ _ _ _ _ _ _ ‹INV_Real _ _ _ _ _› ‹¬ FMap.dom m₂ _›
          (not_of_mem_support_dexcepted ‹_›))
        ((FMap.mem_set _ _ _ _).mpr (Or.inr rfl))
        (by rw [← take_nth default i0₁ p0₁ hi]; assumption) hget
      rw [← take_nth default i0₁ p0₁ hi] at h3
      exact h3
    --     + smt(size_drop size_eq0).
    --     + smt(size_drop size_eq0).
    · rw [behead_drop_succ _ _ hi.1]
      exact decide_lt_size_drop _ _ (by omega)
    --     + by rewrite head_nth nth_drop //=nth_onth (onth_nth b0)//=.  (four times)
    --     + smt().
    --     + smt().
    --     + by rewrite get_setE.
    · rw [head_drop_nth b0 p0₁ i0₁ hi, ← h1, ← h2]
    · rw [head_drop_nth b0 p0₁ i0₁ hi, ← h1, ← h2]
    · rw [head_drop_nth b0 p0₁ i0₁ hi, ← h1, ← h2]
    · rw [head_drop_nth b0 p0₁ i0₁ hi, ← h1, ← h2]
    --     + by rewrite behead_drop drop_add.
    · exact behead_drop_succ _ _ hi.1
    --     + rewrite(take_nth witness)//=.
    --       have:=lemma_3 0 C.c{2} Perm.m{2} Perm.mi{2} Redo.prefixes{1}
    --         (take i0{1} p0{1}) (nth witness p0{1} i0{1}) sa{2} sc{2}.
    --       by rewrite-take_nth//= H5/=H1/=H2/=H6/=;smt().
    · obtain ⟨sa, sc, hget, rfl⟩ : ∃ sa sc, prefixes₁.get (take i0₁ p0₁) = some (sa, sc) ∧
          x1₁ = (sa +^ nth default p0₁ i0₁, sc) :=
        ⟨_, _, ‹prefixes₁.get (take i0₁ p0₁) = some _›, Prod.ext h1 h2⟩
      have h3 := lemma_3 0 c₂ m₂ mi₂ prefixes₁ (take i0₁ p0₁) (nth default p0₁ i0₁) sa sc
        ‹INV_Real _ _ _ _ _› (of_decide_eq_true ‹_›)
        (by rw [← take_nth default i0₁ p0₁ hi]; assumption) hget
      rw [← take_nth default i0₁ p0₁ hi] at h3
      exact h3
    --     + smt(size_drop size_eq0).
    --     + smt(size_drop size_eq0).
    · rw [behead_drop_succ _ _ hi.1]
      exact decide_lt_size_drop _ _ (by omega)
  -- EC: case(0 < n{1});last by rcondf{1}1;2:rcondf{2}1;auto;progress.
  equiv_case (0 < §n{1})
  on_goals 2 =>
    stmt_rcondf{1} 1
    on_goals 2 => stmt_rcondf{2} 1
    · intro σ₂; ec_auto
    · intro σ₁; ec_auto
    ec_auto
  -- EC: splitwhile{1} 1 : i + 1 < n;splitwhile{2} 1 : i + 1 < n.
  stmt_splitwhile{1} 1 : §i + 1 < §n
  stmt_splitwhile{2} 1 : §i + 1 < §n
  -- EC: rcondt{1}2;2:rcondt{2}2;auto;progress.
  --     + by while(i<n);auto;sp;if;auto;sp;while(i<n);auto;if;auto;sp;if;auto.
  --     + by while(i<n);auto;sp;if;auto;sp;if;auto.
  stmt_rcondt{1} 2
  on_goals 2 => stmt_rcondt{2} 2
  · sponge_round
  · sponge_round_r
  -- EC: rcondf{1}4;2:rcondf{2}4;auto;progress.
  --     + by while(i<n);auto;2:smt();sp;if;auto;sp;while(i<n);auto;if;auto;sp;if;auto.
  --     + by while(i<n);auto;2:smt();sp;if;auto;sp;if;auto.
  stmt_rcondf{1} 4
  on_goals 2 => stmt_rcondf{2} 4
  · sponge_round
  · sponge_round_r
  -- EC: rcondf{1}4;2:rcondf{2}4;auto;progress.
  --     + by while(i<n);auto;2:smt();sp;if;auto;sp;while(i<n);auto;if;auto;sp;if;auto.
  --     + by while(i<n);auto;2:smt();sp;if;auto;sp;if;auto.
  stmt_rcondf{1} 4
  on_goals 2 => stmt_rcondf{2} 4
  · sponge_round
  · sponge_round_r
  --     (EC's `auto` on the main goal: the assignments after the loop)
  stmt_wp
  -- EC: conseq(:_==> ={i,n,glob P,C.c} /\ lres{1} = z0{2} /\ b{1} = sa{2}
  --         /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}
  --         /\ Redo.prefixes{1}.[format p{1} (i{1}+1)] = Some (sa,sc){2});progress.
  equiv_conseq (: _ ==> ={i, n, Perm.m, Perm.mi, C.c} ∧ §lres{1} = §z0{2} ∧ §b{1} = §sa{2} ∧
    INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1} ∧
    (§SLCommon.Redo.prefixes{1}).get (format §p{1} (§i{1} + 1)) = some (§sa{2}, §sc{2}))
  case post => ec_close
  -- EC: while(={i,n,glob P,C.c} /\ lres{1} = z0{2} /\ b{1} = sa{2} /\ 0 <= i{1} < n{1}
  --         /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1} /\ valid p{1}
  --         /\ Redo.prefixes{1}.[format p{1} (i{1}+1)] = Some (sa,sc){2});last first.
  equiv_while (={i, n, Perm.m, Perm.mi, C.c} ∧ §lres{1} = §z0{2} ∧ §b{1} = §sa{2} ∧
    0 ≤ §i{1} ∧ §i{1} < §n{1} ∧
    INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1} ∧ valid §p{1} ∧
    (§SLCommon.Redo.prefixes{1}).get (format §p{1} (§i{1} + 1)) = some (§sa{2}, §sc{2}))
  rotate_left
  -- EC: + auto;1:smt(nseq0 cats0).
  · ec_auto; ec_progress
    rw [zero_add, format_one]
    assumption
  -- EC: sp;if;auto;sp.
  --     (GAP 9: the branch `!(i < n)` contradicts the split loop's guard)
  stmt_sp; stmt_if
  · ec_close
  on_goals 2 => (ec_auto; ec_progress; sponge_guard)
  ec_auto; stmt_sp
  -- EC: splitwhile{1}1: i1 < size p1 - 1.
  stmt_splitwhile{1} 1 : §i1 < size §p1 - 1
  -- EC: rcondt{1}2;2:rcondf{1}4;1,2:auto.
  --     + while(i1 < size p1);auto;2:smt(size_cat size_nseq size_ge0 size_eq0 valid_spec).
  --       by if;auto;1:smt();sp;if;auto;progress;smt().
  --     + seq 1 : (i1 = size p1 - 1).
  --       - while(i1 < size p1);auto;2:smt(size_cat size_nseq size_ge0 size_eq0 valid_spec).
  --         by if;auto;1:smt();sp;if;auto;progress;smt().
  --       if;auto;sp;if;auto;smt().
  stmt_rcondt{1} 2
  on_goals 2 => stmt_rcondf{1} 4
  · sponge_last
  · sponge_last
  -- EC: seq 1 0 : (={i,n,glob P,C.c} /\ x0{2} = (sa{2}, sc{2}) /\ 0 < i{1} < n{1}
  --             /\ p1{1} = format p{1} (i{1} + 1) /\ (sa0,sc0){1} = x0{2}
  --             /\ i1{1} = size p{1} + i{1} - 1 /\ lres{1} = z0{2} /\ valid p{1}
  --             /\ Redo.prefixes{1}.[format p{1} i{1}] = Some (sa{2}, sc{2})
  --             /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1}
  --             /\ valid p{1});last first.
  --     (EC's `x0` on the right, the permutation's argument, is our `x2`)
  equiv_seq 1 0 : (={i, n, Perm.m, Perm.mi, C.c} ∧ §x2{2} = (§sa{2}, §sc{2}) ∧
    0 < §i{1} ∧ §i{1} < §n{1} ∧
    §p1{1} = format §p{1} (§i{1} + 1) ∧ (§sa0{1}, §sc0{1}) = §x2{2} ∧
    §i1{1} = size §p{1} + §i{1} - 1 ∧ §lres{1} = §z0{2} ∧ valid §p{1} ∧
    (§SLCommon.Redo.prefixes{1}).get (format §p{1} §i{1}) = some (§sa{2}, §sc{2}) ∧
    INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1} ∧
    valid §p{1})
  rotate_left
  -- EC: + if{1};auto.
  · stmt_if{1}
    -- EC:   + rcondf{2}1;auto;progress.
    --         + move:H5;rewrite take_oversize;1:rewrite size_cat size_nseq ler_maxr/#.
    --           move=>H_dom;rewrite domE.
    --           by have<-:=lemma4 _ _ _ _ _ _ _ _ _ H3 H H2 H_dom;rewrite-domE.
    · ec_auto; stmt_rcondf{2} 1
      · intro σ₁; ec_auto; ec_prep
        have hd := ‹FMap.dom _ (take _ _)›
        rw [take_format_full _ _ ‹(0 : ℤ) < _›] at hd
        have h4 := lemma4 _ _ _ _ _ _ _ _ _ ‹INV_Real _ _ _ _ _› ‹(0 : ℤ) < _› ‹_ = some _› hd
        rw [Bool.not_false, decide_eq_true_eq, FMap.domE]
        rw [FMap.domE, h4] at hd
        exact hd
      ec_auto; ec_progress
      all_goals
        have hd := ‹FMap.dom prefixes₁ (take _ _)›
        rw [take_format_full p₁ i₂ ‹0 < i₂›] at hd
        have h4 := lemma4 _ _ _ _ _ _ _ _ _ ‹INV_Real _ _ _ _ _› ‹0 < i₂›
          ‹prefixes₁.get (format p₁ i₂) = some _› hd
      --         + move:H5;rewrite take_oversize;1:rewrite size_cat size_nseq ler_maxr/#;
      --           move=>H_dom.
      --           by have:=lemma4 _ _ _ _ _ _ _ _ _ H3 H H2 H_dom;smt(domE).
      · rw [take_format_full p₁ i₂ ‹0 < i₂›, h4]
      --         + smt().
      --         + move:H5;rewrite take_oversize;1:rewrite size_cat size_nseq ler_maxr/#;
      --           move=>H_dom.
      --           by have:=lemma4 _ _ _ _ _ _ _ _ _ H3 H H2 H_dom;smt(domE).
      · rw [h4]
        exact FMap.get_some _ _ (by rw [FMap.domE, ← h4, ← FMap.domE]; exact hd)
    -- EC: sp;if;auto;progress.
    --     (GAP 8: the guard, the same state on both sides)
    ec_auto; stmt_sp; stmt_if
    · ec_prep
      have h1 := ‹x2₁.1 = _›
      have h2 := ‹x2₁.2 = _›
      rw [nth_format_pad p₁ i₂ ‹0 < i₂›, xorw_b0] at h1
      rw [← h1, ← h2]
      simp
    all_goals ec_auto
    all_goals ec_progress
    --     + move:H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
    --       have->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
    --       by rewrite Block.WRing.addr0.
    --     (five times; once here for all the goals)
    all_goals
      have hi : 0 < i₂ := by assumption
      have h1 := ‹x2₁.1 = _›
      have h2 := ‹x2₁.2 = _›
      rw [nth_format_pad p₁ i₂ hi, xorw_b0] at h1
    · rw [← h1, ← h2]
    · rw [← h1, ← h2]
    --     + smt().
    --     + move:H5 H6;rewrite nth_cat nth_nseq;1:smt(size_ge0).
    --       have->/=:!size p{1} + i{2} - 1 < size p{1} by smt().
    --       rewrite Block.WRing.addr0 !get_setE/= take_oversize;1:rewrite size_cat size_nseq/#.
    --       move=>H_dom_iS H_dom_p.
    --       have:=lemma2' 0 C.c{2} Perm.m{2}.[(sa{2}, sc{2}) <- y0L]
    --           Perm.mi{2}.[y0L <- (sa{2}, sc{2})] Redo.prefixes{1}
    --           p{1} (i{2}+1) sa{2} sc{2} _ _ H4 _ H_dom_iS.
    --       + by rewrite INV_Real_addm_mi//=;smt(supp_dexcepted).
    --       + smt().
    --       + by rewrite mem_set.
    --       by rewrite!get_setE/=H2/=;smt().
    · obtain ⟨sa, sc, hget, rfl⟩ : ∃ sa sc, prefixes₁.get (format p₁ i₂) = some (sa, sc) ∧
          x2₁ = (sa, sc) :=
        ⟨_, _, ‹prefixes₁.get (format p₁ i₂) = some _›, Prod.ext h1 h2⟩
      rw [take_format_full p₁ i₂ hi] at *
      exact lemma2' _ _ _ _ _ p₁ (i₂ + 1) sa sc
        (INV_Real_addm_mi _ _ _ _ _ _ _ ‹INV_Real _ _ _ _ _› ‹¬ FMap.dom m₂ _›
          (not_of_mem_support_dexcepted ‹_›))
        (by omega) ‹valid p₁ = true› ((FMap.mem_set _ _ _ _).mpr (Or.inr rfl))
        ‹¬ FMap.dom prefixes₁ _› (by rw [add_sub_cancel_right]; exact hget)
    --     + by rewrite!get_setE/=take_oversize//=size_cat size_nseq/#.
    · rw [take_format_full p₁ i₂ hi, FMap.get_set_sameE, ← h1, ← h2]
    --     + rewrite nth_cat;have->/=:! size p{1} + i{2} - 1 < size p{1} by smt().
    --       by rewrite nth_nseq//=1:/# Block.WRing.addr0.
    · rw [← h1, ← h2]
    --     + smt().
    --     + move:H5 H6;rewrite take_oversize 1:size_cat 1:size_nseq 1:/#.
    --       rewrite nth_cat;have->/=:! size p{1} + i{2} - 1 < size p{1} by smt().
    --       rewrite nth_nseq//=1:/# Block.WRing.addr0 =>h1 h2.
    --       by have:=lemma2' 0 C.c{2} Perm.m{2} Perm.mi{2} Redo.prefixes{1}
    --           p{1} (i{2}+1) sa{2} sc{2} H3 _ H1 h2 h1;smt().
    · obtain ⟨sa, sc, hget, rfl⟩ : ∃ sa sc, prefixes₁.get (format p₁ i₂) = some (sa, sc) ∧
          x2₁ = (sa, sc) :=
        ⟨_, _, ‹prefixes₁.get (format p₁ i₂) = some _›, Prod.ext h1 h2⟩
      rw [take_format_full p₁ i₂ hi] at *
      exact lemma2' _ _ _ _ _ p₁ (i₂ + 1) sa sc ‹INV_Real _ _ _ _ _› (by omega)
        ‹valid p₁ = true› (of_decide_eq_true ‹_›) ‹¬ FMap.dom prefixes₁ _›
        (by rw [add_sub_cancel_right]; exact hget)
    --     + move:H5 H6;rewrite take_oversize 1:size_cat 1:size_nseq 1:/#.
    --       rewrite nth_cat;have->/=:! size p{1} + i{2} - 1 < size p{1} by smt().
    --       by rewrite nth_nseq//=1:/# Block.WRing.addr0 !get_setE//=.
    · rw [take_format_full p₁ i₂ hi, FMap.get_set_sameE, ← h1, ← h2]
  -- EC: alias{1} 1 pref = Redo.prefixes;sp.
  stmt_alias{1} 1 pref = §SLCommon.Redo.prefixes
  stmt_sp
  -- EC: conseq(:_==> ={glob P}
  --           /\ p1{1} = format p{1} (i{1} + 1) /\ pref{1} = Redo.prefixes{1}
  --           /\ i1{1} = size p1{1} - 1
  --           /\ Redo.prefixes{1}.[take i1{1} p1{1}] = Some (sa0{1}, sc0{1})
  --           /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1});progress.
  equiv_conseq (: _ ==> ={Perm.m, Perm.mi} ∧
    §p1{1} = format §p{1} (§i{1} + 1) ∧ §pref{1} = §SLCommon.Redo.prefixes{1} ∧
    §i1{1} = size §p1{1} - 1 ∧
    (§SLCommon.Redo.prefixes{1}).get (take §i1{1} §p1{1}) = some (§sa0{1}, §sc0{1}) ∧
    INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
  --     + smt().
  --     + move:H9;rewrite take_format/=1:/#;1:smt(size_ge0 size_cat size_nseq).
  --       pose x := if _ then _ else _ ;have->/={x}: x = format p{1} (i_R+1).
  --       + rewrite/x size_cat size_nseq/=!ler_maxr 1:/#-(addzA _ _ (-1))-(addzA _ _ (-1))/=.
  --         case(size p{1} + i_R <= size p{1})=>//=h;2:smt(size_ge0 size_cat size_nseq).
  --         have->>/=:i_R = 0 by smt().
  --         by rewrite take_size/format nseq0 cats0.
  --       by rewrite H3/==>[][]->>->>.
  --     + (the same) by rewrite H3/=.
  --     + by rewrite size_cat size_nseq;smt().
  case post =>
    ec_progress
    · have hx := ‹Redo_prefixes₁.get (format p₁1 _) = some _›
      have h := ‹Redo_prefixes₁.get (take _ _) = some _›
      rw [take_format_pred p₁1 _ (Int.lt_add_one_iff.mpr ‹(0 : ℤ) ≤ _›), hx] at h
      exact (Option.some.inj h).symm
    · rw [size_format]
      omega
  -- EC: while{1}(={glob P} /\ 0 <= i1{1} <= size p1{1} - 1 /\ 0 < i{1} < n{1}
  --           /\ p1{1} = format p{1} (i{1} + 1) /\ pref{1} = Redo.prefixes{1}
  --           /\ format p{1} i{1} \in pref{1}
  --           /\ Redo.prefixes{1}.[take i1{1} p1{1}] = Some (sa0{1}, sc0{1})
  --           /\ INV_Real 0 C.c{1} Perm.m{1} Perm.mi{1} Redo.prefixes{1})
  --       (size p1{1}-i1{1}-1);auto;last first.
  equiv_while{1} (={Perm.m, Perm.mi} ∧ 0 ≤ §i1{1} ∧ §i1{1} ≤ size §p1{1} - 1 ∧
    0 < §i{1} ∧ §i{1} < §n{1} ∧
    §p1{1} = format §p{1} (§i{1} + 1) ∧ §pref{1} = §SLCommon.Redo.prefixes{1} ∧
    FMap.dom §pref{1} (format §p{1} §i{1}) ∧
    (§SLCommon.Redo.prefixes{1}).get (take §i1{1} §p1{1}) = some (§sa0{1}, §sc0{1}) ∧
    INV_Real 0 §C.c{1} §Perm.m{1} §Perm.mi{1} §SLCommon.Redo.prefixes{1})
    ((size §p1{1} - §i1{1} - 1).toNat)
  -- EC: rcondt 1;auto;progress.
  --     + have->:take (i1{hr} + 1) (format p{hr} (i{hr} + 1)) =
  --             take (i1{hr} + 1) (format p{hr} i{hr});2:smt(all_prefixes_of_INV_real domE).
  --       rewrite!take_format;smt(valid_spec size_ge0 size_eq0 size_cat size_nseq).
  --     + smt().
  --     + smt(valid_spec size_ge0 size_eq0 size_cat size_nseq).
  --     + have->:take (i1{hr} + 1) (format p{hr} (i{hr} + 1)) =
  --             take (i1{hr} + 1) (format p{hr} i{hr});2:smt(all_prefixes_of_INV_real domE).
  --       rewrite!take_format;smt(valid_spec size_ge0 size_eq0 size_cat size_nseq).
  --     smt().
  --     (EC's one goal on the body is our two: its termination, and the invariant with the
  --     variant)
  · while_ll_phoare
    intro σ₂
    stmt_rcondt 1
    · ec_auto; ec_prep
      exact squeeze_known ‹INV_Real _ _ _ _ _› ‹FMap.dom prefixes (format p i)› ‹0 < i›
        (by simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
    ec_auto
  · intro σ₂ k
    stmt_rcondt 1
    · ec_auto; ec_prep
      exact squeeze_known ‹INV_Real _ _ _ _ _› ‹FMap.dom prefixes (format p i)› ‹0 < i›
        (by simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega)
    ec_auto; ec_progress
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      omega
    · exact FMap.get_some _ _ (squeeze_known ‹INV_Real _ _ _ _ _›
        ‹FMap.dom prefixes (format p i)› ‹0 < i›
        (by simp only [Bool.and_eq_true, decide_eq_true_eq] at *; omega))
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at *
      omega
  -- EC: + progress.
  --       + smt(size_cat size_nseq size_ge0 size_eq0 valid_spec).
  --       + smt().
  --       + by rewrite domE H3.
  --       + by rewrite take0;have[]_[]:=H1.
  --       + smt().
  --       + smt().
  ec_auto; ec_progress
  · rw [size_format]
    have := size_ge0 p₁
    omega
  · rw [FMap.domE, ‹pref₁.get (format p₁ _) = some _›]
    simp
  · rw [take0]
    obtain ⟨-, ⟨h0, -⟩, -⟩ := ‹INV_Real _ _ _ _ _›
    exact h0
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at *
    omega

/-- EC's `lemma pr_real (D <: DISTINGUISHER{-SLCommon.C, -C, -Perm, -Redo}) &m :
Pr [ GReal(A(D)).main() @ &m : res /\ SLCommon.C.c <= max_size] =
Pr [ RealIndif(Sponge,P,DRestr(D)).main() @ &m : res]`. -/
theorem pr_real : ∀ (D <: DISTINGUISHER {-SLCommon.C, -C, -Perm, -SLCommon.Redo}),
    ∀ m : VariableAssignment,
    Pr[ SLCommon.GReal(A(D)).main () @ &m : §res ∧ §SLCommon.C.c ≤ max_size ] =
      Pr[ RealIndif(Sponge, Perm, DRestr(D)).main () @ &m : §res ] := by
  intro D _ m
  -- EC: have->:Pr [ RealIndif(Sponge, P, DRestr(D)).main() @ &m : res ] =
  --       Pr [ NIndif(Squeeze(SqueezelessSponge(P)),P,DRestr(D)).main() @ &m :
  --         res /\ C.c <= max_size ].
  --     + by rewrite eq_sym;byequiv (squeeze_squeezeless D)=>//=.
  have e1 : Pr[ RealIndif(Sponge, Perm, DRestr(D)).main () @ &m : §res ] =
      Pr[ NIndif(Squeeze(SLCommon.SqueezelessSponge(Perm)), Perm, DRestr(D)).main () @ &m :
        §res ∧ §C.c ≤ max_size ] := by
    rw [eq_comm]
    byequiv (squeeze_squeezeless D)
    ec_close
  rw [e1]
  -- EC: byequiv (equiv_sponge D)=>//=;progress;smt().
  byequiv (equiv_sponge D)
  ec_progress
  exact ⟨fun h => ⟨h.1, ‹_ ≤ max_size›⟩, fun h => ⟨h.1, le_trans ‹_› ‹_ ≤ max_size›⟩⟩

/-! ## Section `Real_Ideal`

`concl` (EC l. 1786) applies `Gconcl.Real_Ideal` to the composed distinguisher `A(D)`, with
`A_lossless` for its `D_ll`.  The pilots' `Real_Ideal` is stated for a declared module `D`, its
`D_ll` over oracles restricted against `glob D`; for `A(D)` that restriction is against
`glob (A(D))`, and only an upper bound of the footprint of an application is known (EC reads
`glob A(D) = glob D ∪ {C.c}` off the code).  This is step 4 of `notes/SHA3/TacticReview.md`
(EC's syntactic `glob`): `concl` waits for it, and with it `neg_D_concl`,
`Inefficient_Real_Ideal` and the final `Real_Ideal`. -/

section Real_Ideal

declare module D <: DISTINGUISHER {-SLCommon.C, -C, -Perm, -SLCommon.Redo, -SLCommon.F.RO,
  -SLCommon.F.FRO.m, -S, -BIRO.IRO, -BIRO2.IRO, -F2.RO, -F2.FRO.m}

-- EC's `declare axiom D_lossless`
variable (D_lossless : ∀ (F0 <: DFUNCTIONALITY {-D}), ∀ (P0 <: DPRIMITIVE {-D}),
  islossless P0.f → islossless P0.fi → islossless F0.f → islossless D(F0, P0).distinguish)

include D_lossless in
/-- EC's `lemma A_lossless (F <: SLCommon.DFUNCTIONALITY{-A(D)})
(P0 <: SLCommon.DPRIMITIVE{-A(D)}) : islossless P0.f => islossless P0.fi => islossless F.f =>
islossless A(D, F, P0).distinguish`; `{-A(D)}` is `{-D, -C}`, its globals. -/
theorem A_lossless : ∀ (F <: SLCommon.DFUNCTIONALITY {-D, -C}),
    ∀ (P0 <: SLCommon.DPRIMITIVE {-D, -C}),
    islossless P0.f → islossless P0.fi → islossless F.f →
      islossless A(D, F, P0).distinguish := by
  intro F _ P0 _ H H0 H1
  -- EC: progress;proc;inline*;sp;wp.
  phoare_proc; phoare_inline*; stmt_sp; stmt_wp
  -- EC: call(:true);auto.
  --     + exact D_lossless.
  phoare_call (@D_lossless _ ?_ _ ?_ ?_ ?_ ?_)
  · phoare_auto
  -- EC: + proc;inline*;sp;if;auto;call H;auto.
  · phoare_proc; stmt_sp; stmt_if
    · phoare_auto; phoare_call H; phoare_auto
    · phoare_auto
  -- EC: + proc;inline*;sp;if;auto;call H0;auto.
  · phoare_proc; stmt_sp; stmt_if
    · phoare_auto; phoare_call H0; phoare_auto
    · phoare_auto
  -- EC: proc;inline*;sp;if;auto;sp;if;auto.
  · phoare_proc; phoare_inline*; stmt_sp; stmt_if
    · stmt_sp; stmt_if
      -- EC: while(true)(n-i);auto.
      --     + by sp;if;auto;1:call H1;auto;smt().
      --     call H1;auto;smt().
      · stmt_wp
        phoare_while True ((§n - §i).toNat)
        · intro z; stmt_sp; stmt_if
          · phoare_call H1; phoare_auto; smt_close
          · phoare_auto; smt_close
        · phoare_call H1; phoare_auto
      · phoare_auto
    · phoare_auto

end Real_Ideal

/-! ## Section `Real_Ideal_Abs`

`Real_lossless` (EC l. 1858) calls `D` under the invariant `invm Perm.m Perm.mi` in a
`phoare … = 1` goal: `phoare_call` has the rule for lossless oracles only (GAP 12).
`Ideal_lossless` (EC l. 1887) has loops followed by sampling code, which EC's `auto` passes
(`rnd` with a lossless distribution); the `phoare` tactics have no step for code after a loop
(GAP 13).  Both are left to the batch of rule fixes. -/

section Real_Ideal_Abs

open GaudisCrypt.SHA3.Gconcl_list.Real_Ideal_Abs (Neg_D)

declare module D <: DISTINGUISHER {-SLCommon.C, -C, -Perm, -SLCommon.Redo, -SLCommon.F.RO,
  -SLCommon.F.FRO.m, -S, -BIRO.IRO, -BIRO2.IRO, -F2.RO, -F2.FRO.m}

-- EC's `declare axiom D_lossless`
variable (D_lossless : ∀ (F0 <: DFUNCTIONALITY {-D}), ∀ (P0 <: DPRIMITIVE {-D}),
  islossless P0.f → islossless P0.fi → islossless F0.f → islossless D(F0, P0).distinguish)

include D_lossless in
/-- EC's `local lemma Neg_D_lossless (F <: DFUNCTIONALITY{-Neg_D(D)})
(P <: DPRIMITIVE{-Neg_D(D)}) : islossless P.f => islossless P.fi => islossless F.f =>
islossless Neg_D(D, F, P).distinguish`; `{-Neg_D(D)}` is `{-D}`. -/
theorem Neg_D_lossless : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
    islossless P.f → islossless P.fi → islossless F.f →
      islossless Neg_D(D, F, P).distinguish := by
  intro F _ P _ H H0 H1
  -- EC: by progress;proc;inline*;call(D_lossless F P H H0 H1);auto.
  --     (EC's `inline*`: nothing to open here)
  phoare_proc
  phoare_call (D_lossless F P H H0 H1); phoare_auto

end Real_Ideal_Abs

end GaudisCrypt.SHA3.Pilot.Gconcl_list
