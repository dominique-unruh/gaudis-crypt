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

end GaudisCrypt.SHA3.Pilot.Gconcl_list
