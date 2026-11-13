import GaudisCrypt.Examples.SHA3.Sponge
import GaudisCrypt.Logic.ECGlob
import GaudisCrypt.Logic.ECConseq
import GaudisCrypt.Logic.ECProc
import GaudisCrypt.Logic.ECSim
import GaudisCrypt.Logic.ECAuto
import GaudisCrypt.Logic.ECIf
import GaudisCrypt.Logic.ECCallAbstract
import GaudisCrypt.Logic.ECInline
import GaudisCrypt.Logic.ECSeq
import GaudisCrypt.Logic.ECSp
import GaudisCrypt.Logic.ECCallEquiv
import GaudisCrypt.Logic.ECCallFrame
import GaudisCrypt.Logic.ECCallOneSided
import GaudisCrypt.Logic.ECCallUpto
import GaudisCrypt.Logic.CallSpec
import GaudisCrypt.Logic.ECWhileRel
import GaudisCrypt.Logic.ECProgress
import GaudisCrypt.Logic.DeclareModule
import GaudisCrypt.Logic.ECModuleBinders
import GaudisCrypt.Lib.EC.ListLemmas

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# The sponge construction (EasyCrypt `proof/Sponge.ec`) — EC-fidelity port, in progress

Ported so far: `Sponge_is_StdSponge` (EC l. 99), on the strict tactics, and
`Sponge_Raise_BlockSponge_f` (EC l. 1922), which was the second tactic experiment and is
described below.  The rest of the file follows in EC's order (`notes/SHA3/Mapping.md`).

## `Sponge_Raise_BlockSponge_f` in EC's form — the second tactic experiment

A procedure-level equivalence with two-sided loops, EC's `inline M.f`, `seq n m : P`, `rcondt{i}`,
`case`, `call (_ : ={glob Perm})` on a concrete module and `auto`, over the old port's
declarations (`Examples/SHA3/Sponge.lean`).  It drove `stmt_inline (M.f)`
(`Logic/ECInline.lean`), EC's `equiv_seq` positions (`Logic/ECSeq.lean`), `equiv_auto`,
`equiv_call (_ : ={glob P})` on a concrete callee, and the closers of `hoare_auto`/`equiv_auto`.

Deviations, all from the old declarations or the closers:
* the statement: `Sponge.f` and `RaiseFun.f` applied explicitly (the old module types are
  abbreviations the paths do not see through), `(bs, n)` as one parameter `x`, the old views as
  coercions;
* positions: one more statement on each side (`bs, n <- x`), a `skip` where `rcondt` left the
  branch, `RaiseFun`'s `xs <- z0` taken by `stmt_wp`; EC's `swap{2} [3..5] -2`, `swap{2} 1 1`
  and `seq 0 1` are not needed (the inlined code is already in that order);
* EC's `smt`/`progress`/`rewrite` closers: `simp_all` with the `blocks2bits` lemmas.
-/

namespace GaudisCrypt.SHA3.Pilot.Sponge

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge

variable [SLCommon.Params] [BlockSponge.Params]

/-! ## The sponge construction (EC l. 28–127)

`StdSponge`, `Sponge` and `loop_cond` are the first port's. -/

omit [BlockSponge.Params] in
/-- EC's `size_block` (the clone `Block` of `BitWord`). -/
theorem size_block (w : block) : size (ofblock w) = r := BitWord.size_word ge0_r w

/-- EC derives this inline in each of the three branches of the squeezing loop of
`Sponge_is_StdSponge` (`rewrite size_cat size_block=> -> …; by rewrite -(mulzDr r i 1) loop_cond
/#`): one more block, and the two loops' tests agree. -/
theorem size_cat_block (z : List Bool) (sa : block) (i n : ℤ) (hz : size z = r * i)
    (hi : 0 ≤ i) (hn : 0 < n) :
    size (z ++ ofblock sa) = r * (i + 1) ∧
      (size (z ++ ofblock sa) < n ↔ i + 1 < (n + r - 1) / r) := by
  have hs : size (z ++ ofblock sa) = r * (i + 1) := by rw [size_cat, size_block, hz]; ring
  exact ⟨hs, by rw [hs]; exact loop_cond (i + 1) n (by omega) (by omega)⟩

/-- EC's `equiv Sponge_is_StdSponge (P <: DPRIMITIVE): StdSponge(P).f ~ Sponge(P).f:
={glob P, bs, n} ==> ={glob P, res}`.

EC's script.  `(bs, n)` is the one parameter `x` of the first port's modules, so each side has
one more statement, `bs, n <- x` (EC's `seq 5 5` is `equiv_seq 6 6`).  The fact EC derives inline
in the three branches of the squeezing loop is `size_cat_block`. -/
theorem Sponge_is_StdSponge : ∀ (P <: DPRIMITIVE {}),
    equiv[ StdSponge(P).f (x) ~ Sponge(P).f (x) : ={glob P, x} ==> ={glob P, res} ] := by
  intro P _
  -- EC: proc; seq  5  5: (={glob P, z, sa, sc, xs, n} /\ !finished{1} /\ i{2} = 0 /\ z{1} = []).
  --     (one more statement on each side: `bs, n <- x`)
  equiv_proc
  equiv_seq 6 6 : (={glob P, z, sa, sc, xs, n} ∧ §finished{1} = false ∧ §i{2} = 0 ∧ §z{1} = [])
  -- EC: + while (={glob P, xs, sa, sc}); 2:by auto.
  --       by auto; call (: true).
  · equiv_while (={glob P, xs, sa, sc})
    · ec_auto; equiv_call (_ : ={glob P}); ec_auto
    · ec_auto
  -- EC: case: (n{1} <= 0).
  equiv_case (§n{1} ≤ 0)
  -- EC: + rcondt{1} 1=> //=; rcondf{1} 2.
  --       + by auto; smt(size_ge0).
  · stmt_rcondt{1} 1
    · intro σ₂; ec_auto
    stmt_rcondf{1} 2
    · intro σ₂; ec_auto; smt_close [size_ge0]
    -- EC: rcondf{1} 3; 1:by auto.
    stmt_rcondf{1} 3
    · intro σ₂; ec_auto
    -- EC: rcondf{2} 1.
    --     + by auto=> /> &hr /needed_blocks_non_pos /#.
    stmt_rcondf{2} 1
    · intro σ₁; ec_auto; ec_prep
      have := needed_blocks_non_pos v ‹v ≤ 0›
      omega
    -- EC: by auto=> /> &1 &2 _ n_le0; rewrite !take_le0.
    ec_auto; ec_prep
    rw [take_le0 _ _ ‹_›, take_le0 _ _ ‹_›]
  -- EC: while (   ={glob P, z, n, sa, sc}
  --            /\ (finished{1} <=> n{1} <= size z{1})
  --            /\ size z{1} = r * i{2}
  --            /\ 0 < n{1}
  --            /\ 0 <= i{2}).
  equiv_while (={glob P, z, n, sa, sc} ∧ (§finished{1} = true ↔ §n{1} ≤ size §z{1}) ∧
    size §z{1} = r * §i{2} ∧ 0 < §n{1} ∧ 0 ≤ §i{2})
  -- EC: + sp; if=> />.
  · stmt_sp; stmt_if
    -- EC: + move=> &2 i z; rewrite size_cat size_block=> -> gt0_n ge0_i /ltzNge gt_ri_n gt_i_nbl.
    --       by rewrite -(mulzDr r i 1) loop_cond /#.
    · ec_prep
      obtain ⟨-, hlt⟩ := size_cat_block _ sa₂ _ _ ‹size _ = r * _› ‹(0 : ℤ) ≤ _› ‹(0 : ℤ) < _›
      simp only [hlt]
    -- EC: + call (: true); auto=> /> &2 i z; rewrite size_cat size_block=> -> …
    --       by rewrite -(mulzDr r i 1) loop_cond /#.
    · equiv_call (_ : ={glob P}); ec_auto; ec_prep
      obtain ⟨hs, hlt⟩ := size_cat_block _ sa₂ _ _ ‹size _ = r * _› ‹(0 : ℤ) ≤ _› ‹(0 : ℤ) < _›
      rintro r₁ g₁ r₂ g₂ ⟨rfl, hg⟩
      refine ⟨⟨⟨hg, rfl, rfl⟩, by simpa using ‹size _ < _›, hs, ‹_›, by omega⟩, ?_⟩
      simp [hlt.mp ‹_›]
    -- EC: + auto=> /> &2 i z; rewrite size_cat size_block=> -> …
    --       by rewrite -(mulzDr r i 1) loop_cond /#.
    · ec_auto; ec_prep
      obtain ⟨hs, hlt⟩ := size_cat_block _ sa₂ _ _ ‹size _ = r * _› ‹(0 : ℤ) ≤ _› ‹(0 : ℤ) < _›
      refine ⟨⟨by simpa using ‹_ ≤ size _›, hs, ‹_›, by omega⟩, ?_⟩
      have : ¬ (_ + 1 < (_ + r - 1) / r) := fun h => absurd (hlt.mpr h) (not_lt.mpr ‹_ ≤ size _›)
      simp [this]
  -- EC: by auto=> /> &1 &2 _ /ltrNge gt0_n; smt(gt0_r).
  ec_auto; ec_prep
  have h0 : 0 < (n₂ + r - 1) / r :=
    (loop_cond 0 n₂ le_rfl (le_of_lt ‹_›)).mp (by simpa using ‹0 < n₂›)
  refine ⟨⟨⟨by simp [size]; omega, by simp [size], ‹_›, le_rfl⟩, by simp [h0]⟩,
    fun τ₁ τ₂ _ _ hI _ _ => ?_⟩
  obtain ⟨⟨hg, hz, hn, -, -⟩, -⟩ := hI
  exact ⟨hg, by rw [hz, hn]⟩

/-! ## `Sponge_Raise_BlockSponge_f` (EC l. 1922), the second tactic experiment -/

/-! EC's subtyping of module types, as coercions (the old port has the views, not
`module_subtype`). -/

noncomputable instance : CoeOut (PRP.StrongPRP.PRP (block × capacity)) DPRIMITIVE :=
  ⟨fun P => Indifferentiability.PRIMITIVE.view (block × capacity) (List Bool × ℤ) (List Bool) P⟩

noncomputable instance : CoeOut (PRP.StrongPRP.PRP (block × capacity)) BlockSponge.DPRIMITIVE :=
  ⟨fun P => Indifferentiability.PRIMITIVE.view (block × capacity) (List block × ℤ) (List block) P⟩

noncomputable instance : CoeOut BlockSponge.FUNCTIONALITY BlockSponge.DFUNCTIONALITY :=
  ⟨fun F => Indifferentiability.FUNCTIONALITY.view (block × capacity) (List block × ℤ)
    (List block) F⟩

/-- `BlockSponge.Sponge(Perm)` (a name: the path does not parse here). -/
noncomputable abbrev BlockSpongePerm : BlockSponge.DFUNCTIONALITY :=
  (Module.app BlockSponge.Sponge (Perm : BlockSponge.DPRIMITIVE) : BlockSponge.FUNCTIONALITY)

/-- EC's `sim` on `Perm.f ~ Perm.f` after `call (_ : ={glob Perm})`.  The two sides are `Perm.f`
behind the first port's two `PRIMITIVE.view`s (the bit sponge's and the block sponge's), which
`equiv_proc` does not open (GAP 11 of `Pilot/Gconcl_list.lean`): the views are unfolded first. -/
local macro "sim_perm_f" : tactic => `(tactic| (
  simp only [Indifferentiability.PRIMITIVE.view, Indifferentiability.PRIMITIVE.f, Perm,
    PRP.RP.RP, PRP.StrongPRP.PRP.mk, Indifferentiability.DPRIMITIVE.f.mk_simp]
  equiv_proc; sim))

/-- EC's `local lemma Sponge_Raise_BlockSponge_f : equiv[Sponge(Perm).f ~
RaiseFun(BlockSponge.Sponge(Perm)).f : ={bs, n, glob Perm} ==> ={res, glob Perm}]`, its proof EC's
(see the module docstring). -/
theorem Sponge_Raise_BlockSponge_f :
    equiv[ (Module.app Sponge.f (Perm : DPRIMITIVE)) (x) ~
      (Module.app RaiseFun.f BlockSpongePerm) (x) : ={x, glob Perm} ==> ={res, glob Perm} ] := by
  equiv_proc; stmt_inline{2} ((BlockSpongePerm).f)
  equiv_seq 5 6 : (={n, sa, sc, i, glob Perm} ∧ §xs{1} = §xs0{2} ∧ §z{1} = [] ∧ §z0{2} = [] ∧
      §n0{2} = (§n{1} + r - 1) / r ∧ valid_block §xs0{2})
  · equiv_auto; smt_close [valid_pad2blocks]
  · stmt_rcondt{2} 1
    · hoare_auto
    stmt_wp
    equiv_seq 1 1 : (={n, sa, sc, i, glob Perm} ∧ §xs{1} = §xs0{2} ∧ §z{1} = [] ∧ §z0{2} = [] ∧
        §n0{2} = (§n{1} + r - 1) / r)
    · equiv_while_raw (={n, sa, sc, i, glob Perm} ∧ §xs{1} = §xs0{2} ∧ §z{1} = [] ∧ §z0{2} = [] ∧
          §n0{2} = (§n{1} + r - 1) / r)
      case body =>
        -- EC: wp. call (_ : ={glob Perm}). sim. auto.
        stmt_wp; equiv_call (_ : ={glob Perm})
        · sim_perm_f
        equiv_auto
      case guard => intros; simp_all
      case exit => intros; simp_all
      case hpre => equiv_auto
    · equiv_while_raw (={n, sa, sc, i, glob Perm} ∧ blocks2bits §z0{2} = §z{1} ∧
          §n0{2} = (§n{1} + r - 1) / r)
      case body =>
        equiv_case (§i{1} + 1 < (§n{1} + r - 1) / r)
        · stmt_rcondt{1} 3
          · hoare_auto
          stmt_rcondt{2} 3
          · hoare_auto
          stmt_wp
          -- EC: call (_ : ={glob Perm}); first sim.
          equiv_call (_ : ={glob Perm})
          · sim_perm_f
          -- EC's `auto; progress; by rewrite -cats1 blocks2bits_cat blocks2bits_sing`
          equiv_auto; intros; simp_all [rcons, blocks2bits_cat, blocks2bits_sing]
        · stmt_rcondf{1} 3
          · hoare_auto
          stmt_rcondf{2} 3
          · hoare_auto
          equiv_auto; intros; simp_all [rcons, blocks2bits_cat, blocks2bits_sing]
      case guard => intros; simp_all
      case exit => intros; simp_all
      case hpre => equiv_auto; intros; simp_all [blocks2bits_nil]

end GaudisCrypt.SHA3.Pilot.Sponge
