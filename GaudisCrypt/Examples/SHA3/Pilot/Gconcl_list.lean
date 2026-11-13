import GaudisCrypt.Examples.SHA3.Pilot.Gconcl
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl_list
import GaudisCrypt.Logic.ECProgress

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

end GaudisCrypt.SHA3.Pilot.Gconcl_list
