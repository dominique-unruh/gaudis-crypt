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

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
-- (off at two calls of the concrete `Perm`: the call rule with EC's frame does not apply to a
-- concrete callee and the frameless rule is used, `set_option ec.strict false in`)
set_option ec.strict true

/-!
# `Sponge.ec`'s `Sponge_Raise_BlockSponge_f` in EC's form — the second tactic experiment

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
        stmt_wp; (set_option ec.strict false in equiv_call (_ : ={glob Perm})); equiv_auto
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
          set_option ec.strict false in equiv_call (_ : ={glob Perm})
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
