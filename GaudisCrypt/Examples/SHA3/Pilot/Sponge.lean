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
import GaudisCrypt.Logic.PrTactics
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.ModuleFootprint
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.ECTrans
import GaudisCrypt.Logic.ECElim

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# The sponge construction (EasyCrypt `proof/Sponge.ec`) — EC-fidelity port, in progress

Ported so far, on the strict tactics: `Sponge_is_StdSponge` (EC l. 99); the theory `HybridIRO`
up to `HybridIROEagerTrans_BlockSpongeTrans_loop` (EC l. 256–1612; l. 1188–1305, the
modules `BlockSpongeTrans`, `BlockGen` and `BlockGen_loop_direct` with its `bypr` proof, are the
first port's, E12); and `Sponge_Raise_BlockSponge_f` (EC l. 1922), which was the second tactic
experiment and is described below.  The rest of the file follows in EC's order
(`notes/SHA3/Mapping.md`).

Translation:
* the modules are the first port's (`Examples/SHA3/Sponge.lean`); a procedure takes its
  parameters as one tuple there, so a statement names them at the triple
  (`StdSponge(P).f (x) ~ …`, `HybridIROLazy.f (xs, n) ~ …`);
* the theory `HybridIRO` is a namespace; its module variables `HybridIROLazy.mp`,
  `HybridIROEager.mp` and those of the local clone `ERO` are `global_var`s, and the first port's
  modules (which take them as lens parameters) are applied at them;
* a local clone's variables are fresh for a declared module in EC; here the restriction names
  them (`-ERO.RO.m, -ERO.FRO.m`).

Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: `Perm.f` behind the first port's `PRIMITIVE.view`s is not opened by `equiv_proc`
  (GAP 11 of `Pilot/Gconcl_list.lean`): `sim_perm_f`.
* GAP 2: inside the library's `RO.sample` the callee is the library's `RO.get` itself, not the
  procedure of the module `ERO.RO`, so EC's `inline ERO.RO.get` does not name it: by index.
* GAP 3: after a call whose result is discarded, the strict `auto` does not read through the
  discarding write: `simp only [Setter.throwaway_set]` first.
* GAP 4: the abstract call asks all of `HYBRID_IRO`'s procedures, where EC's `{HI.f}` restricts
  `D` to `f`: one more goal, for `init`.  (`HybridIROLazy.init`, `.f` are declared as the module
  type's procedures of `HybridIROLazy`, the form in which a call of an oracle names them; the
  first port's own procedures are equal to them only by a rewrite.)
* GAP 5: `equiv_conseq H` leaves its two implications when the goal's conditions are not
  literally `H`'s (EC closes them): `conseq_side`.
* GAP 6: the strict `auto` runs out of recursion depth on the body of a one-sided loop whose
  invariant reads the other memory: `stmt_wp; hoare_skip`.
* GAP 7: the exit goal of a one-sided loop frames what the postcondition reads, not what the
  invariant reads; an unmodified variable that only the invariant reads is lost (`xs{1}` in
  `next_block_split_BlockSpongeTrans`, added to EC's `conseq` there).
* GAP 8: `transitivity N (P₁ ==> Q₁) (P₂ ==> Q₂)` on procedures is the rule `prhlProc_trans_ec`,
  not a tactic: the second judgment is its own lemma, and the side conditions are over the
  parameter tuples (hypotheses restated by `replace` before use).
* GAP 9: a first-port fact about a `module`-declared procedure names it `X.f.procedure`; the
  judgment syntax names `X.f`'s procedure (`BlockGen_loop_direct`, restated by a rewrite).
* GAP 10: after a loop, the guard's read of a local and the invariant's read of it can be
  different atoms for `omega` (equal by `rfl`): `le_antisymm` on the two hypotheses instead.
* GAP 11: `={bs}` in a condition of `equiv_trans` is not resolved when the two sides of the
  goal have a `bs` of different types, although the middle program's is the left one's:
  `§(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2}`.
* `call (_ : ={HybridIROEager.mp})` on the concrete `fill_in` needs its footprint, which EC reads
  off the code: `fvP_HybridIROEager_fill_in`, `fvP_BIRO_IRO_fill_in` (`@[fp_bound]`).  The
  callee's goal (EC: `if=> //; wp; rnd; auto`) is then closed by the tactic.
* EC's `alias{2} 1 with w` is not needed: the sampled block is the inlined callee's local `r`
  (two locals `bs`, `r` of different types on the two sides are read as
  `§(localVarLens "bs" (List Bool)){1}`).
* A statement that names `HIRO(…).f`'s parameters `(xs, n)` as EC does gets a warning: the module
  type `HYBRID_IRO` declares them `(x, n)`.

## `Sponge_Raise_BlockSponge_f` in EC's form — the second tactic experiment

A procedure-level equivalence with two-sided loops, EC's `inline M.f`, `seq n m : P`, `rcondt{i}`,
`case`, `call (_ : ={glob Perm})` on a concrete module and `auto`, over the old port's
declarations (`Examples/SHA3/Sponge.lean`).  It drove `stmt_inline (M.f)`
(`Logic/ECInline.lean`), EC's `equiv_seq` positions (`Logic/ECSeq.lean`), `equiv_auto`,
`equiv_call (_ : ={glob P})` on a concrete callee, and the closers of `hoare_auto`/`equiv_auto`.

Deviations, all from the old declarations or the closers:
* the statement: `(bs, n)` as one parameter `x`, named at the triple; the old views as
  coercions;
* positions: one more statement on each side (`bs, n <- x`), a `skip` where `rcondt` left the
  branch, `RaiseFun`'s `xs <- z0` taken by `stmt_wp`; EC's `swap{2} [3..5] -2`, `swap{2} 1 1`
  and `seq 0 1` are not needed (the inlined code is already in that order);
* EC's `smt`/`progress`/`rewrite` closers: `simp_all` with the `blocks2bits` lemmas.
-/

namespace GaudisCrypt.SHA3.Pilot.Sponge

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common GaudisCrypt.SHA3.Sponge
open GaudisCrypt.SHA3.Sponge.BIRO

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

/-- EC's subtyping: a `FUNCTIONALITY` where a `DFUNCTIONALITY` is expected (the first port's
view). -/
noncomputable instance : CoeOut FUNCTIONALITY DFUNCTIONALITY :=
  ⟨fun F => Indifferentiability.FUNCTIONALITY.view (block × capacity) (List Bool × ℤ)
    (List Bool) F⟩

/-! ## The theory `HybridIRO` (EC l. 256–1909) -/

namespace HybridIRO

open GaudisCrypt.SHA3.Sponge.HybridIRO (HYBRID_IRO HYBRID_IRO_DIST HybridIROExper HIRO EROExper
  RODist)

/-- EC's `HybridIROLazy.mp`. -/
global_var HybridIROLazy.mp : FMap (List block × ℤ) Bool
/-- EC's `HybridIROEager.mp`. -/
global_var HybridIROEager.mp : FMap (List block × ℤ) Bool

/-- EC's `HybridIROLazy`, at its type `HYBRID_IRO`. -/
noncomputable abbrev HybridIROLazy : HYBRID_IRO :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROLazy.asHI HybridIROLazy.mp
-- (`init` and `f` as the module type's procedures of `HybridIROLazy`: the form in which a call
-- of an oracle `HI.f` names them)
noncomputable abbrev HybridIROLazy.init := HYBRID_IRO.init HybridIROLazy
noncomputable abbrev HybridIROLazy.f := HYBRID_IRO.f HybridIROLazy
noncomputable abbrev HybridIROLazy.fill_in :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROLazy.fill_in HybridIROLazy.mp

/-- EC's `HybridIROEager`, at its type `HYBRID_IRO`. -/
noncomputable abbrev HybridIROEager : HYBRID_IRO :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEager.asHI HybridIROEager.mp
noncomputable abbrev HybridIROEager.init := HYBRID_IRO.init HybridIROEager
noncomputable abbrev HybridIROEager.f := HYBRID_IRO.f HybridIROEager
noncomputable abbrev HybridIROEager.fill_in :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEager.fill_in HybridIROEager.mp

/-! EC's `local clone import PROM.FullRO as ERO with type in_t <- block list * int,
type out_t <- bool, op dout _ <- dbool, type d_in_t <- unit, type d_out_t <- bool`: the clone's
module variables are `global_var`s (the first port's are lens parameters). -/

namespace ERO
export GaudisCrypt.SHA3.Sponge.HybridIRO.ERO (dout RO_T RO_Distinguisher)
/-- The clone's module variable `ERO.RO.m`. -/
global_var RO.m : FMap (List block × ℤ) Bool
/-- The clone's module variable `ERO.FRO.m`. -/
global_var FRO.m : FMap (List block × ℤ) (Bool × flag)
noncomputable abbrev RO := PROM.FullRO.RO.asRO (List block × ℤ) Bool dout RO.m
noncomputable abbrev LRO := PROM.FullRO.LRO (List block × ℤ) Bool dout RO.m
end ERO

set_option hygiene false in
/-- The two implications `equiv_conseq H` leaves when the goal's conditions are not literally
`H`'s (EC's `conseq H` closes them itself): equal arguments give equal parameters; the rest by
simplification.  (GAP 5.) -/
local macro "conseq_side" : tactic => `(tactic| first
  | (rintro a₁ g₁ a₂ g₂ ⟨rfl, h⟩; intros; exact ⟨⟨rfl, rfl⟩, h⟩)
  | (intros; simp_all; done))

section

-- (the local clone `ERO`'s variables are fresh for `D` in EC; here `D`'s restriction names them)
declare module D <: HYBRID_IRO_DIST {-HybridIROEager, -HybridIROLazy, -ERO.RO.m, -ERO.FRO.m}

/-- EC's `local lemma LRO_RO (D <: ERO.RO_Distinguisher{-ERO.RO, -ERO.FRO}) &m :
Pr[EROExper(LRO, D).main() @ &m : res] = Pr[EROExper(ERO.RO, D).main() @ &m : res]`. -/
theorem LRO_RO : ∀ (D <: ERO.RO_Distinguisher {-ERO.RO.m, -ERO.FRO.m}),
    ∀ m : VariableAssignment,
    Pr[ EROExper(ERO.LRO, D).main () @ &m : §res ] =
      Pr[ EROExper(ERO.RO, D).main () @ &m : §res ] := by
  intro D _ m
  -- EC: byequiv=> //; proc.
  byequiv; equiv_proc
  -- EC: seq 1 1 : (={glob D, ERO.RO.m}); first sim.
  equiv_seq 1 1 : (={glob D, ERO.RO.m})
  · sim
  -- EC: by symmetry; call (FullEager.RO_LRO_D D _); auto; rewrite dbool_ll.
  equiv_sym
  equiv_call (PROM.FullRO.FullEager.RO_LRO_D (List block × ℤ) Bool Unit Bool ERO.dout ERO.FRO.m
    (fun _ => dbool_ll) ERO.RO.m D (by ec_module) (by fp_disjoint))
  ec_auto

/-- EC's `local lemma HybridIROLazy_HIRO_LRO_init : equiv[HybridIROLazy.init ~ HIRO(LRO).init :
true ==> HybridIROLazy.mp{1} = ERO.RO.m{2}]`. -/
theorem HybridIROLazy_HIRO_LRO_init :
    equiv[ HybridIROLazy.init ~ HIRO(ERO.LRO).init :
      True ==> §HybridIROLazy.mp{1} = §ERO.RO.m{2} ] := by
  -- EC: proc; inline*; auto.
  equiv_proc; stmt_inline*; ec_auto

/-- EC's `local lemma HybridIROLazy_fill_in_LRO_get : equiv[HybridIROLazy.fill_in ~ LRO.get :
(xs, i){1} = x{2} /\ HybridIROLazy.mp{1} = ERO.RO.m{2} ==>
={res} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}]`. -/
theorem HybridIROLazy_fill_in_LRO_get :
    equiv[ HybridIROLazy.fill_in (xs, i) ~ ERO.LRO.get (x) :
      (§xs{1}, §i{1}) = §x{2} ∧ §HybridIROLazy.mp{1} = §ERO.RO.m{2} ==>
      ={res} ∧ §HybridIROLazy.mp{1} = §ERO.RO.m{2} ] := by
  -- EC: proc=> /=.
  --     case ((dom HybridIROLazy.mp{1}) (xs{1}, i{1})).
  equiv_proc
  equiv_case (FMap.dom §HybridIROLazy.mp{1} (§xs{1}, §i{1}))
  -- EC: rcondf{1} 1; first auto. rcondf{2} 2; first auto.
  --     rnd{2}; auto; progress; apply dbool_ll.
  · stmt_rcondf{1} 1
    · intro σ₂; ec_auto
    stmt_rcondf{2} 2
    · intro σ₁; ec_auto
    equiv_rnd{2}; ec_auto; ec_progress
    exact (is_lossless_iff_expected _).mp dbool_ll
  -- EC: rcondt{1} 1; first auto. rcondt{2} 2; first auto.
  --     wp; rnd; auto.
  · stmt_rcondt{1} 1
    · intro σ₂; ec_auto
    stmt_rcondt{2} 2
    · intro σ₁; ec_auto
    stmt_wp; equiv_rnd; ec_auto

/-- EC's `local lemma HybridIROLazy_HIRO_LRO_f : equiv[HybridIROLazy.f ~ HIRO(LRO).f :
={xs, n} /\ HybridIROLazy.mp{1} = ERO.RO.m{2} ==> ={res} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}]`. -/
theorem HybridIROLazy_HIRO_LRO_f :
    equiv[ HybridIROLazy.f (xs, n) ~ HIRO(ERO.LRO).f (xs, n) :
      ={xs, n} ∧ §HybridIROLazy.mp{1} = §ERO.RO.m{2} ==>
      ={res} ∧ §HybridIROLazy.mp{1} = §ERO.RO.m{2} ] := by
  -- EC: proc; inline LRO.sample; sp=> /=.
  equiv_proc; stmt_inline{2} (ERO.LRO.sample); stmt_sp
  -- EC: if=> //.
  stmt_if
  · ec_close
  rotate_left
  · ec_auto
  -- EC: while{2} (true) (m{2} - i{2}).
  --     progress; auto; progress; smt().
  equiv_while{2} (True) ((§m{2} - §i{2}).toNat)
  · while_ll_phoare
    intro σ₁
    ec_auto
  · intro σ₁ z
    ec_auto
  -- EC: while (={xs, n, i, bs} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}).
  --     wp; call HybridIROLazy_fill_in_LRO_get; auto.
  equiv_while (={xs, n, i, bs} ∧ §HybridIROLazy.mp{1} = §ERO.RO.m{2})
  · stmt_wp; equiv_call HybridIROLazy_fill_in_LRO_get; ec_auto
  -- EC: auto; progress; smt().
  ec_auto

/-- EC's `local lemma HIRO_RO_HybridIROEager_init : equiv[HIRO(ERO.RO).init ~ HybridIROEager.init :
true ==> ={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem HIRO_RO_HybridIROEager_init :
    equiv[ HIRO(ERO.RO).init ~ HybridIROEager.init :
      True ==> ={res} ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2} ] := by
  -- EC: proc; inline*; auto.
  equiv_proc; stmt_inline*; ec_auto

/-- EC's `local lemma RO_get_HybridIROEager_fill_in : equiv[ERO.RO.get ~ HybridIROEager.fill_in :
x{1} = (xs, i){2} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem RO_get_HybridIROEager_fill_in :
    equiv[ ERO.RO.get (x) ~ HybridIROEager.fill_in (xs, i) :
      §x{1} = (§xs{2}, §i{2}) ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2} ==>
      ={res} ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2} ] := by
  -- EC: proc=> /=.
  --     case (dom HybridIROEager.mp{2} (xs{2}, i{2})).
  equiv_proc
  equiv_case (FMap.dom §HybridIROEager.mp{2} (§xs{2}, §i{2}))
  -- EC: rcondf{1} 2; first auto. rcondf{2} 1; first auto.
  --     rnd{1}; auto; progress; apply dbool_ll.
  · stmt_rcondf{1} 2
    · intro σ₂; ec_auto
    stmt_rcondf{2} 1
    · intro σ₁; ec_auto
    equiv_rnd{1}; ec_auto; ec_progress
    exact (is_lossless_iff_expected _).mp dbool_ll
  -- EC: rcondt{1} 2; first auto. rcondt{2} 1; first auto.
  --     wp; rnd; auto.
  · stmt_rcondt{1} 2
    · intro σ₂; ec_auto
    stmt_rcondt{2} 1
    · intro σ₁; ec_auto
    stmt_wp; equiv_rnd; ec_auto

/-- EC's `local lemma RO_sample_HybridIROEager_fill_in :
equiv[ERO.RO.sample ~ HybridIROEager.fill_in :
x{1} = (xs, i){2} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem RO_sample_HybridIROEager_fill_in :
    equiv[ ERO.RO.sample (x) ~ HybridIROEager.fill_in (xs, i) :
      §x{1} = (§xs{2}, §i{2}) ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2} ==>
      §ERO.RO.m{1} = §HybridIROEager.mp{2} ] := by
  -- EC: proc=> /=; inline ERO.RO.get; sp.
  --     case (dom HybridIROEager.mp{2} (xs{2}, i{2})).
  --     (GAP 2: inside the library's `RO.sample` the callee is the library's `RO.get` itself,
  --     not `ERO.RO`'s procedure, so EC's path does not name it: inlined by index)
  equiv_proc; stmt_inline{1} 0; stmt_sp
  equiv_case (FMap.dom §HybridIROEager.mp{2} (§xs{2}, §i{2}))
  -- EC: rcondf{1} 2; first auto. rcondf{2} 1; first auto.
  --     rnd{1}; auto; progress; apply dbool_ll.
  · stmt_rcondf{1} 2
    · intro σ₂; ec_auto
    stmt_rcondf{2} 1
    · intro σ₁; ec_auto
    equiv_rnd{1}; ec_auto; ec_progress
    exact (is_lossless_iff_expected _).mp dbool_ll
  -- EC: rcondt{1} 2; first auto. rcondt{2} 1; first auto.
  --     wp; rnd; auto.
  · stmt_rcondt{1} 2
    · intro σ₂; ec_auto
    stmt_rcondt{2} 1
    · intro σ₁; ec_auto
    stmt_wp; equiv_rnd; ec_auto

/-- EC's `local lemma HIRO_RO_HybridIROEager_f : equiv[HIRO(ERO.RO).f ~ HybridIROEager.f :
={xs, n} /\ ERO.RO.m{1} = HybridIROEager.mp{2} ==>
={res} /\ ERO.RO.m{1} = HybridIROEager.mp{2}]`. -/
theorem HIRO_RO_HybridIROEager_f :
    equiv[ HIRO(ERO.RO).f (xs, n) ~ HybridIROEager.f (xs, n) :
      ={xs, n} ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2} ==>
      ={res} ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2} ] := by
  -- EC: proc; first sp=> /=.
  --     if=> //.
  equiv_proc; stmt_sp
  stmt_if
  · ec_close
  rotate_left
  · ec_auto
  -- EC: while (={i, m, xs} /\ ERO.RO.m{1} = HybridIROEager.mp{2}).
  --     wp; call RO_sample_HybridIROEager_fill_in; auto.
  equiv_while (={i, m, xs} ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2})
  --     (GAP 3: both calls discard their results, and the strict `auto` does not read through
  --     the discarding write: `Setter.throwaway_set` first)
  · stmt_wp; equiv_call RO_sample_HybridIROEager_fill_in
    simp only [Setter.throwaway_set]
    ec_auto
  -- EC: while (={i, n, xs, bs} /\ ERO.RO.m{1} = HybridIROEager.mp{2}).
  --     wp; call RO_get_HybridIROEager_fill_in; auto.
  equiv_while (={i, n, xs, bs} ∧ §ERO.RO.m{1} = §HybridIROEager.mp{2})
  · stmt_wp; equiv_call RO_get_HybridIROEager_fill_in; ec_auto
  -- EC: auto.
  ec_auto

/-- EC's `local lemma Exper_HybridIROLazy_LRO &m :
Pr[HybridIROExper(HybridIROLazy, D).main() @ &m : res] =
Pr[EROExper(LRO, RODist).main() @ &m : res]`. -/
theorem Exper_HybridIROLazy_LRO (m : VariableAssignment) :
    Pr[ HybridIROExper(HybridIROLazy, D).main () @ &m : §res ] =
      Pr[ EROExper(ERO.LRO, RODist(D)).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline*; wp.
  byequiv; equiv_proc; stmt_inline*; stmt_wp
  -- EC: seq 1 1 : (={glob D} /\ HybridIROLazy.mp{1} = ERO.RO.m{2}); first auto.
  --     call (_ : HybridIROLazy.mp{1} = ERO.RO.m{2}).
  --     (GAP 4: the rule asks all of `HYBRID_IRO`'s procedures, EC's `{HI.f}` only `f`: one
  --     more goal, for `init`)
  equiv_call (_ : §HybridIROLazy.mp{1} = §ERO.RO.m{2})
  · equiv_conseq HybridIROLazy_HIRO_LRO_init <;> conseq_side
  -- EC: conseq HybridIROLazy_HIRO_LRO_f.
  · equiv_conseq HybridIROLazy_HIRO_LRO_f <;> conseq_side
  -- EC: auto.
  --     (GAP 14 of `Pilot/Gconcl_list.lean`: `glob D` past the initialization)
  ec_auto
  simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
  ec_close

/-- EC's `local lemma Exper_RO_HybridIROEager &m :
Pr[EROExper(ERO.RO, RODist).main() @ &m : res] =
Pr[HybridIROExper(HybridIROEager, D).main() @ &m : res]`. -/
theorem Exper_RO_HybridIROEager (m : VariableAssignment) :
    Pr[ EROExper(ERO.RO, RODist(D)).main () @ &m : §res ] =
      Pr[ HybridIROExper(HybridIROEager, D).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline*; wp.
  byequiv; equiv_proc; stmt_inline*; stmt_wp
  -- EC: seq 1 1 : (={glob D} /\ ERO.RO.m{1} = HybridIROEager.mp{2}); first auto.
  --     call (_ : ERO.RO.m{1} = HybridIROEager.mp{2}).
  equiv_call (_ : §ERO.RO.m{1} = §HybridIROEager.mp{2})
  · equiv_conseq HIRO_RO_HybridIROEager_init <;> conseq_side
  -- EC: conseq HIRO_RO_HybridIROEager_f.
  · equiv_conseq HIRO_RO_HybridIROEager_f <;> conseq_side
  -- EC: auto.
  ec_auto
  simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
  ec_close

-- EC reads `RODist`'s globals off its code (for `LRO_RO`'s restriction)
attribute [local fp_bound] GaudisCrypt.SHA3.Sponge.HybridIRO.fvP_RODist_le

/-- EC's `lemma HybridIROExper_Lazy_Eager' &m :
Pr[HybridIROExper(HybridIROLazy, D).main() @ &m : res] =
Pr[HybridIROExper(HybridIROEager, D).main() @ &m : res]`. -/
theorem HybridIROExper_Lazy_Eager' (m : VariableAssignment) :
    Pr[ HybridIROExper(HybridIROLazy, D).main () @ &m : §res ] =
      Pr[ HybridIROExper(HybridIROEager, D).main () @ &m : §res ] := by
  -- EC: by rewrite (Exper_HybridIROLazy_LRO &m) (LRO_RO RODist &m) (Exper_RO_HybridIROEager &m).
  rw [Exper_HybridIROLazy_LRO D m, @LRO_RO _ _ (RODist D) ⟨by fp_finite, by fp_disjoint⟩ m,
    Exper_RO_HybridIROEager D m]

end

/-- EC's `lemma HybridIROExper_Lazy_Eager (D <: HYBRID_IRO_DIST{-HybridIROEager, -HybridIROLazy})
&m : Pr[HybridIROExper(HybridIROLazy, D).main() @ &m : res] =
Pr[HybridIROExper(HybridIROEager, D).main() @ &m : res]`; the local clone `ERO`'s variables in
`D`'s restriction (fresh in EC). -/
theorem HybridIROExper_Lazy_Eager :
    ∀ (D <: HYBRID_IRO_DIST {-HybridIROEager, -HybridIROLazy, -ERO.RO.m, -ERO.FRO.m}),
    ∀ m : VariableAssignment,
    Pr[ HybridIROExper(HybridIROLazy, D).main () @ &m : §res ] =
      Pr[ HybridIROExper(HybridIROEager, D).main () @ &m : §res ] := by
  -- EC: by apply (HybridIROExper_Lazy_Eager' D &m).
  intro D _ m
  exact HybridIROExper_Lazy_Eager' D m

/-! ### Raising and lowering hybrid IROs; the lazy invariant (EC l. 553–763)

`RaiseHybridIRO`, `LowerHybridIRO`, `lazy_invar` and its lemmas are the first port's. -/

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO lazy_invar lazy_invar0
  lazy_invar_mem_pad2blocks_l2r lazy_invar_mem_pad2blocks_r2l lazy_invar_vb lazy_invar_lookup_eq
  lazy_invar_upd_mem_dom_iff lazy_invar_upd2_vb lazy_invar_upd_lu_eq)

omit [BlockSponge.Params] in
/-- EC derives this inline (`have {2}<- := unpadBlocksK xs0{2}; first by rewrite (some_oget
(unpad_blocks xs0{2}))`): a valid block list is the padding of what it unpads to. -/
theorem pad2blocks_unpad_blocks (xs : List block) (h : valid_block xs) :
    pad2blocks (oget (unpad_blocks xs)) = xs := by
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp h
  have := unpadBlocksK xs
  rw [hy] at this ⊢
  exact this

/-- EC's `lemma LowerFun_IRO_HybridIROLazy_f :
equiv[LowerFun(IRO).f ~ LowerHybridIRO(HybridIROLazy).f :
={xs, n} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2} ==>
={res} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2}]`.

EC's script; where EC passes the first assignments by `seq 0 1 … ; first auto`, `sp` takes all of
them, so the conditionals EC reaches by position (`rcondt{1} 3`, `rcondt{2} 4`, `rcondt{1} 7`)
are first. -/
theorem LowerFun_IRO_HybridIROLazy_f :
    equiv[ LowerFun(IRO.asF).f (x) ~ LowerHybridIRO(HybridIROLazy).f (x) :
      ={x} ∧ lazy_invar §IRO.mp{1} §HybridIROLazy.mp{2} ==>
      ={res} ∧ lazy_invar §IRO.mp{1} §HybridIROLazy.mp{2} ] := by
  -- EC: proc=> /=; inline HybridIROLazy.f.
  equiv_proc; stmt_inline{2} (HybridIROLazy.f)
  -- EC: seq 0 1 : (={n} /\ xs{1} = xs0{2} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2}); first auto.
  --     case (valid_block xs{1}).
  stmt_sp
  equiv_case (valid_block §xs{1})
  -- EC: rcondt{1} 3; first auto. rcondt{2} 4; first auto.
  --     (after `sp`, the two conditionals are first)
  · stmt_rcondt{1} 1
    · intro σ₂; ec_auto
    stmt_rcondt{2} 1
    · intro σ₁; ec_auto
    -- EC: inline*. rcondt{1} 7; first auto.
    stmt_inline*; stmt_sp
    stmt_rcondt{1} 1
    · intro σ₂; ec_auto
    -- EC: seq 6 3 :
    --       (={i, n0} /\ bs{1} = bs0{2} /\
    --        lazy_invar IRO.mp{1} HybridIROLazy.mp{2} /\
    --        pad2blocks x{1} = xs0{2}).
    --     auto; progress.
    --       have {2}<- := unpadBlocksK xs0{2}; first
    --         by rewrite (some_oget (unpad_blocks xs0{2})).
    --     wp.
    --     while
    --       (={i, n0} /\ bs{1} = bs0{2} /\
    --        lazy_invar IRO.mp{1} HybridIROLazy.mp{2} /\
    --        pad2blocks x{1} = xs0{2}).
    --     (EC's `i`, `n0`, `bs`, `x` on the left are our `i0`, `n1`, `bs`, `x0`)
    stmt_wp
    equiv_while (§i0{1} = §i{2} ∧ §n1{1} = §n0{2} ∧ §bs{1} = §bs0{2} ∧
      lazy_invar §IRO.mp{1} §HybridIROLazy.mp{2} ∧ pad2blocks §x0{1} = §xs0{2})
    -- EC: sp; auto.
    --     if.
    · stmt_sp; stmt_if
      -- EC: progress;
      --       [by apply (lazy_invar_mem_pad2blocks_l2r IRO.mp{1}
      --                  HybridIROLazy.mp{2} x{1} i{2}) |
      --        by apply (lazy_invar_mem_pad2blocks_r2l IRO.mp{1}
      --                  HybridIROLazy.mp{2} x{1} i{2})].
      · ec_prep
        simp only [Bool.not_not]
        exact decide_eq_decide.mpr ⟨lazy_invar_mem_pad2blocks_l2r _ _ _ _ ‹_›,
          lazy_invar_mem_pad2blocks_r2l _ _ _ _ ‹_›⟩
      -- EC: wp; rnd; auto=> |> &1 &2 inv i_lt_n0 xi_notin_m r _.
      --     rewrite !get_set_sameE //=; split=> [bs n|].
      --     + exact/(lazy_invar_upd_mem_dom_iff _ _ _ _ _ _ _ inv).
      --     split=> [xs n|bs n].
      --     + by move=>/(lazy_invar_upd2_vb _ _ _ _ _ _ _ inv).
      --     by move=>/(lazy_invar_upd_lu_eq _ _ _ _ _ _ _ inv).
      · ec_auto; ec_prep
        refine ⟨by rw [FMap.get_set_sameE, FMap.get_set_sameE],
          fun bs n => lazy_invar_upd_mem_dom_iff _ _ _ _ _ _ _ ‹_›,
          fun xs n h => lazy_invar_upd2_vb _ _ _ _ _ _ _ ‹_› h,
          fun bs n h => lazy_invar_upd_lu_eq _ _ _ _ _ _ _ ‹_› h⟩
      -- EC: auto; progress [-delta].
      --     by rewrite (lazy_invar_lookup_eq IRO.mp{1} HybridIROLazy.mp{2} x{1} i{2}).
      · ec_auto; ec_prep
        exact ⟨by rw [lazy_invar_lookup_eq _ _ _ _ ‹_› (by simpa using ‹decide _ = !false›)], ‹_›⟩
    -- EC: auto.
    ec_auto; ec_prep
    refine ⟨⟨⟨rfl, ‹_›, pad2blocks_unpad_blocks _ ‹_›⟩, rfl⟩, fun τ₁ τ₂ _ _ hI _ _ => ?_⟩
    obtain ⟨-, -, hbs, hinv, -⟩ := hI
    exact ⟨by rw [hbs], hinv⟩
  -- EC: rcondf{1} 3; first auto. rcondf{2} 4; first auto.
  --     auto; progress; by rewrite bits2blocks_nil.
  · stmt_rcondf{1} 1
    · intro σ₂; ec_auto
    stmt_rcondf{2} 1
    · intro σ₁; ec_auto
    ec_auto; ec_prep
    exact ⟨bits2blocks_nil.symm, ‹_›⟩

/-- EC's `lemma IRO_RaiseHybridIRO_HybridIROLazy_f :
equiv[IRO.f ~ RaiseHybridIRO(HybridIROLazy).f :
={n} /\ x{1} = bs{2} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2} ==>
={res} /\ lazy_invar IRO.mp{1} HybridIROLazy.mp{2}]`. -/
theorem IRO_RaiseHybridIRO_HybridIROLazy_f :
    equiv[ IRO.f (xn) ~ RaiseHybridIRO(HybridIROLazy).f (x) :
      §xn{1} = §x{2} ∧ lazy_invar §IRO.mp{1} §HybridIROLazy.mp{2} ==>
      ={res} ∧ lazy_invar §IRO.mp{1} §HybridIROLazy.mp{2} ] := by
  -- EC: proc=> /=; inline*.
  equiv_proc; stmt_inline*; stmt_sp
  -- EC: rcondt{1} 3; first auto.
  --     rcondt{2} 5; first auto; progress; apply valid_pad2blocks.
  --     (after `sp`, the two conditionals are first)
  stmt_rcondt{1} 1
  · intro σ₂; ec_auto
  stmt_rcondt{2} 1
  · intro σ₁; ec_auto; ec_prep
    exact valid_pad2blocks _
  -- EC: seq 2 4 :
  --       (={i, n} /\ n{1} = n0{2} /\ xs{2} = pad2blocks x{1} /\ bs{1} = bs0{2} /\
  --        lazy_invar IRO.mp{1} HybridIROLazy.mp{2}); first auto.
  --     wp.
  --     while
  --       (={i, n} /\ n{1} = n0{2} /\ xs{2} = pad2blocks x{1} /\ bs{1} = bs0{2} /\
  --        lazy_invar IRO.mp{1} HybridIROLazy.mp{2}).
  stmt_wp
  equiv_while (={i, n} ∧ §n{1} = §n0{2} ∧ §xs{2} = pad2blocks §(localVarLens "x" (List Bool)){1} ∧
    §bs{1} = §bs0{2} ∧ lazy_invar §IRO.mp{1} §HybridIROLazy.mp{2})
  -- EC: wp; sp.
  --     if.
  · stmt_sp; stmt_if
    -- EC: progress;
    --       [by apply (lazy_invar_mem_pad2blocks_l2r IRO.mp{1}
    --                  HybridIROLazy.mp{2} x{1} i{2}) |
    --        by apply (lazy_invar_mem_pad2blocks_r2l IRO.mp{1}
    --                  HybridIROLazy.mp{2} x{1} i{2})].
    · ec_prep
      simp only [Bool.not_not]
      exact decide_eq_decide.mpr ⟨lazy_invar_mem_pad2blocks_l2r _ _ _ _ ‹_›,
        lazy_invar_mem_pad2blocks_r2l _ _ _ _ ‹_›⟩
    -- EC: wp; rnd; auto=> |> &1 &2 inv i_lt_n0 xi_notin_m r _.
    --     rewrite !get_set_sameE=> //=; split=> [bs n|].
    --     + exact/(lazy_invar_upd_mem_dom_iff _ _ _ _ _ _ _ inv).
    --     split=> [xs n|bs n].
    --     + by move=>/(lazy_invar_upd2_vb _ _ _ _ _ _ _ inv).
    --     by move=>/(lazy_invar_upd_lu_eq _ _ _ _ _ _ _ inv).
    · ec_auto; ec_prep
      refine ⟨by rw [FMap.get_set_sameE, FMap.get_set_sameE],
        fun bs n => lazy_invar_upd_mem_dom_iff _ _ _ _ _ _ _ ‹_›,
        fun xs n h => lazy_invar_upd2_vb _ _ _ _ _ _ _ ‹_› h,
        fun bs n h => lazy_invar_upd_lu_eq _ _ _ _ _ _ _ ‹_› h⟩
    -- EC: auto; progress [-delta];
    --       by rewrite (lazy_invar_lookup_eq IRO.mp{1} HybridIROLazy.mp{2} x{1} i{2}).
    · ec_auto; ec_prep
      exact ⟨by rw [lazy_invar_lookup_eq _ _ _ _ ‹_› (by simpa using ‹decide _ = !false›)], ‹_›⟩
  -- EC: auto.
  ec_auto

/-- EC's `lemma Lower_HybridIROEager_f :
equiv[LowerHybridIRO(HybridIROEager).f ~ HybridIROEager.f :
={xs, HybridIROEager.mp} /\ n{1} * r = n{2} ==>
res{1} = bits2blocks res{2} /\ ={HybridIROEager.mp}]`. -/
theorem Lower_HybridIROEager_f :
    equiv[ LowerHybridIRO(HybridIROEager).f (x) ~ HybridIROEager.f (xs, n) :
      (§x{1}).1 = §xs{2} ∧ ={HybridIROEager.mp} ∧ (§x{1}).2 * r = §n{2} ==>
      §res{1} = bits2blocks §res{2} ∧ ={HybridIROEager.mp} ] := by
  -- EC: proc=> /=; inline*.
  equiv_proc; stmt_inline*
  -- EC: seq 5 3 :
  --       (={i, HybridIROEager.mp} /\ xs0{1} = xs{2} /\
  --        bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\ m{2} = n{2}).
  --     auto; progress; first 2 by rewrite needed_blocks_prod_r.
  equiv_seq 5 3 : (={i, HybridIROEager.mp} ∧ §xs0{1} = §xs{2} ∧ §bs0{1} = §bs{2} ∧
    §n0{1} = §n{2} ∧ §m{1} = §n0{1} ∧ §m{2} = §n{2})
  · ec_auto; ec_prep
    rw [needed_blocks_prod_r]
    exact ⟨rfl, rfl⟩
  -- EC: if=> //; wp.
  stmt_if
  · ec_close
  rotate_left
  · ec_auto
  stmt_wp
  -- EC: while
  --       (={i, HybridIROEager.mp} /\ xs0{1} = xs{2} /\
  --        bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\
  --        m{2} = n{2}).
  --     sp; wp; if=> //; wp; rnd; auto.
  equiv_while (={i, HybridIROEager.mp} ∧ §xs0{1} = §xs{2} ∧ §bs0{1} = §bs{2} ∧
    §n0{1} = §n{2} ∧ §m{1} = §n0{1} ∧ §m{2} = §n{2})
  · stmt_sp; stmt_if
    · ec_close
    all_goals ec_auto
  -- EC: while
  --       (={i, HybridIROEager.mp} /\ xs0{1} = xs{2} /\
  --        bs0{1} = bs{2} /\ n0{1} = n{2} /\ m{1} = n0{1} /\
  --        m{2} = n{2})=> //.
  --     sp; wp; if=> //; wp; rnd; auto.
  equiv_while (={i, HybridIROEager.mp} ∧ §xs0{1} = §xs{2} ∧ §bs0{1} = §bs{2} ∧
    §n0{1} = §n{2} ∧ §m{1} = §n0{1} ∧ §m{2} = §n{2})
  · stmt_sp; stmt_if
    · ec_close
    all_goals ec_auto
  -- EC: auto.
  ec_auto

open GaudisCrypt.SHA3.Sponge.HybridIRO (eager_invar block_bits_all_in_dom block_bits_all_out_dom
  block_bits_dom_all_in_or_out eager_eq_except eager_eq_except_mem_iff
  eager_eq_except_upd1_eq_in eager_eq_except_upd2_eq_in eager_eq_except_maps_eq
  block_bits_dom_first_in_imp_all_in block_bits_dom_first_out_imp_all_out)

/-! ### `HybridIROEagerTrans` (EC l. 904–1186)

The module is the first port's, applied at `HybridIROEager.mp`. -/

noncomputable abbrev HybridIROEagerTrans.next_block :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEagerTrans.next_block HybridIROEager.mp
noncomputable abbrev HybridIROEagerTrans.next_block_split :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEagerTrans.next_block_split HybridIROEager.mp
noncomputable abbrev HybridIROEagerTrans.loop :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEagerTrans.loop HybridIROEager.mp

set_option maxHeartbeats 4000000 in
-- one declaration: two cases, three loops with their invariants
/-- EC's `lemma HybridIROEagerTrans_next_block_split :
equiv[HybridIROEagerTrans.next_block ~ HybridIROEagerTrans.next_block_split :
={i, m, xs, bs, HybridIROEager.mp} /\ m{1} = i{1} + r /\ size bs{1} = i{1} /\
block_bits_dom_all_in_or_out xs{1} i{1} HybridIROEager.mp{1} ==> ={res, HybridIROEager.mp}]`.

EC's script for the program steps.  The goals EC closes by `progress` and a list of `smt`s (the
invariants of the three loops) are closed by hand, each in one block: the conjuncts by `omega`
and the `eager_eq_except` lemmas, the two quantified ones by cases on the updated key. -/
theorem HybridIROEagerTrans_next_block_split :
    equiv[ HybridIROEagerTrans.next_block (xs, i, m, bs) ~
      HybridIROEagerTrans.next_block_split (xs, i, m, bs) :
      ={i, m, xs, bs, HybridIROEager.mp} ∧ §m{1} = §i{1} + r ∧ size §bs{1} = §i{1} ∧
        block_bits_dom_all_in_or_out §xs{1} §i{1} §HybridIROEager.mp{1} ==>
      ={res, HybridIROEager.mp} ] := by
  -- EC: proc=> /=.
  --     case (dom HybridIROEager.mp{2} (xs{2}, i{2})).
  equiv_proc
  equiv_case (FMap.dom §HybridIROEager.mp{2} (§xs{2}, §i{2}))
  -- EC: rcondt{2} 1; first auto.
  · stmt_rcondt{2} 1
    · intro σ₁; ec_auto
    -- EC: conseq
    --       (_ :
    --        ={i, m, xs, bs, HybridIROEager.mp} /\ i{1} <= m{1} /\
    --        (forall (j : int),
    --         i{1} <= j < m{1} =>
    --         dom HybridIROEager.mp{1} (xs{1}, j)) ==>
    --        _).
    --     progress; smt(gt0_r).
    equiv_conseq (: ={i, m, xs, bs, HybridIROEager.mp} ∧ §i{1} ≤ §m{1} ∧
      (∀ j : ℤ, §i{1} ≤ j ∧ j < §m{1} → FMap.dom §HybridIROEager.mp{1} (§xs{1}, j)) ==> _)
    case pre =>
      ec_prep
      exact ⟨by have := gt0_r; omega,
        fun j hj => block_bits_dom_first_in_imp_all_in _ _ _ ‹_› ‹_› j hj⟩
    -- EC: while
    --       (={i, m, xs, bs, HybridIROEager.mp} /\ i{1} <= m{1} /\
    --        (forall (j : int),
    --         i{1} <= j < m{1} =>
    --         dom HybridIROEager.mp{1} (xs{1}, j))).
    equiv_while (={i, m, xs, bs, HybridIROEager.mp} ∧ §i{1} ≤ §m{1} ∧
      (∀ j : ℤ, §i{1} ≤ j ∧ j < §m{1} → FMap.dom §HybridIROEager.mp{1} (§xs{1}, j)))
    -- EC: wp; inline*.
    --     rcondf{1} 3; first auto; smt().
    --     auto; smt().
    --     (after `sp`, the conditional is first)
    · stmt_wp; stmt_inline*; stmt_sp
      stmt_rcondf{1} 1
      · intro σ₂; ec_auto
      ec_auto; ec_prep
      have h : ∀ j : ℤ, i₂ ≤ j ∧ j < m₂ → FMap.dom mp₂ (xs₂, j) := by assumption
      exact ⟨rfl, by omega, fun j hj => h j ⟨by omega, hj.2⟩⟩
    -- EC: auto.
    · ec_auto
  -- EC: rcondf{2} 1; first auto.
  --     sp; exists* i{1}; elim*=> i'.
  · stmt_rcondf{2} 1
    · intro σ₁; ec_auto
    stmt_sp
    equiv_exists* §i{1}
    intro i'
    -- EC: conseq
    --       (_ :
    --        ={i, m, xs, bs, HybridIROEager.mp} /\ i{1} = i' /\
    --        i' + r = m{1} /\ size bs{1} = i' /\ cs{2} = [] /\ j{2} = 0 /\
    --        (forall (j : int),
    --         i' <= j < i' + r =>
    --         ! dom HybridIROEager.mp{1} (xs{1}, j)) ==>
    --        _).
    --     progress; smt(gt0_r).
    equiv_conseq (: ={i, m, xs, bs, HybridIROEager.mp} ∧ §i{1} = i' ∧ i' + r = §m{1} ∧
      size §bs{1} = i' ∧ §cs{2} = [] ∧ §j{2} = 0 ∧
      (∀ j : ℤ, i' ≤ j ∧ j < i' + r → ¬ FMap.dom §HybridIROEager.mp{1} (§xs{1}, j)) ==> _)
    case pre =>
      ec_prep
      exact fun j hj => block_bits_dom_first_out_imp_all_out _ _ _ ‹_› ‹_› j hj
    -- EC: seq 1 2 :
    --       (={m, xs} /\ i{2} = i' /\ i{1} = i' + r /\ bs{1} = bs{2} /\
    --        size bs{1} = i' + r /\ m{1} = i' + r /\
    --        (forall (k : int),
    --         i' <= k < i' + r =>
    --         HybridIROEager.mp{1}.[(xs{1}, k)] = Some(nth true bs{1} k)) /\
    --        eager_eq_except xs{1} i' (i' + r) HybridIROEager.mp{1} HybridIROEager.mp{2}).
    equiv_seq 1 2 : (={m, xs} ∧ §i{2} = i' ∧ §i{1} = i' + r ∧ §bs{1} = §bs{2} ∧
      size §bs{1} = i' + r ∧ §m{1} = i' + r ∧
      (∀ k : ℤ, i' ≤ k ∧ k < i' + r →
        FMap.get §HybridIROEager.mp{1} (§xs{1}, k) = some (nth true §bs{1} k)) ∧
      eager_eq_except §xs{1} i' (i' + r) §HybridIROEager.mp{1} §HybridIROEager.mp{2})
    -- EC: wp.
    --     while
    --       (={m, xs} /\ i{2} = i' /\ m{1} = i' + r /\ i' <= i{1} <= i' + r /\
    --        0 <= j{2} <= r /\ i{1} - i' = j{2} /\
    --        size bs{1} = i{1} /\ bs{1} = bs{2} ++ cs{2} /\
    --        (forall (k : int),
    --         i' <= k < i{1} =>
    --         HybridIROEager.mp{1}.[(xs{1}, k)] = Some(nth true bs{1} k)) /\
    --        (forall (k : int),
    --         i{1} <= k < i' + r =>
    --         ! dom HybridIROEager.mp{1} (xs{1}, k)) /\
    --        eager_eq_except xs{1} i' (i' + r) HybridIROEager.mp{1} HybridIROEager.mp{2}).
    · stmt_wp
      equiv_while (={m, xs} ∧ §i{2} = i' ∧ §m{1} = i' + r ∧ i' ≤ §i{1} ∧ §i{1} ≤ i' + r ∧
        0 ≤ §(localVarLens "j" ℤ){2} ∧ §(localVarLens "j" ℤ){2} ≤ r ∧
        §i{1} - i' = §(localVarLens "j" ℤ){2} ∧
        size §bs{1} = §i{1} ∧ §bs{1} = §bs{2} ++ §cs{2} ∧
        (∀ k : ℤ, i' ≤ k ∧ k < §i{1} →
          FMap.get §HybridIROEager.mp{1} (§xs{1}, k) = some (nth true §bs{1} k)) ∧
        (∀ k : ℤ, §i{1} ≤ k ∧ k < i' + r → ¬ FMap.dom §HybridIROEager.mp{1} (§xs{1}, k)) ∧
        eager_eq_except §xs{1} i' (i' + r) §HybridIROEager.mp{1} §HybridIROEager.mp{2})
      -- EC: inline*; rcondt{1} 3; first auto; smt().
      --     sp; wp; rnd; skip; progress.
      · stmt_inline*; stmt_sp
        stmt_rcondt{1} 1
        · intro σ₂; ec_auto
        --     (EC's thirteen `progress` goals: the invariant's conjuncts after one more bit)
        ec_auto
        rintro m₁ xs₁ i₁ bs₁ mp₁ xs0₁ i0₁ m₂ xs₂ i₂ j₂ bs₂ cs₂ mp₂
          ⟨⟨⟨⟨rfl, rfl⟩, rfl, hm, h1, h2, hj0, hjr, hij, hsz, hbs, hA, hB, hE⟩, hlt, -⟩, hx⟩ a -
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        simp only [decide_eq_true_eq] at hlt
        have hg : oget ((mp₁.set (xs0₁, i0₁) a).get (xs0₁, i0₁)) = a := by
          rw [FMap.get_set_sameE]; rfl
        rw [hg]
        refine ⟨⟨⟨rfl, rfl⟩, rfl, hm, by omega, by omega, by omega, by omega, by omega,
          by rw [size_rcons, hsz], by subst hbs; simp [rcons], fun k hk => ?_, fun k hk hd => ?_,
          eager_eq_except_upd1_eq_in _ _ _ _ _ _ _ hE h1 (by omega)⟩,
          decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩⟩
        · rw [FMap.get_setE, nth_rcons, hsz]
          by_cases hki : k = i0₁
          · subst hki; simp
          · have hlt' : k < i0₁ := by omega
            rw [if_neg (by simp [hki]), if_pos hlt']
            exact hA k ⟨hk.1, hlt'⟩
        · rw [FMap.mem_set] at hd
          rcases hd with hd | hd
          · exact hB k ⟨by omega, hk.2⟩ hd
          · have : k = i0₁ := by simpa using hd
            omega
      -- EC: skip; progress; smt(gt0_r cats0 size_cat).
      · ec_auto
        rintro i₁ m₁ xs₁ bs₁ mp₁ cs₁ i₂ m₂ xs₂ bs₂ mp₂ cs₂ j₂
          ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, hm, hsz, rfl, rfl, hN⟩
        have hr := gt0_r
        refine ⟨⟨⟨⟨rfl, rfl⟩, rfl, hm.symm, le_rfl, by omega, le_rfl, by omega, by omega, hsz,
          (cats0 _).symm, fun k hk => absurd hk.2 (not_lt.mpr hk.1), hN, fun _ _ _ => rfl⟩,
          decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩⟩,
          fun τ₁ τ₂ _ _ hI hg1 hg2 => ?_⟩
        obtain ⟨hmx, hi2, hm1, h1, h2, -, -, hij, hsz', hbs', hA, -, hE⟩ := hI
        simp only [decide_eq_false_iff_not, not_lt] at hg1
        have hi : (localVarLens "i" ℤ).get τ₁ = i₁ + r := by omega
        exact ⟨hmx, hi2, hi, hbs', by rw [hsz', hi], hm1, fun k hk => hA k ⟨hk.1, by omega⟩, hE⟩
    -- EC: conseq
    --       (_ :
    --        ={xs, bs, m} /\ i{2} = i' /\ i{1} = i' + r /\ m{1} = i' + r /\
    --        size bs{1} = i' + r /\
    --        (forall (k : int),
    --         i' <= k < i' + r =>
    --         HybridIROEager.mp{1}.[(xs{1}, k)] = Some (nth true bs{1} k)) /\
    --        eager_eq_except xs{1} i' (i' + r)
    --                        HybridIROEager.mp{1} HybridIROEager.mp{2} ==>
    --        _)=> //.
    --     while{2}
    --       (={xs, bs, m} /\ i' <= i{2} <= i' + r /\ i{1} = i' + r /\
    --        m{1} = i' + r /\ size bs{1} = i' + r /\
    --        (forall (k : int),
    --         i' <= k < i{2} =>
    --         HybridIROEager.mp{1}.[(xs{1}, k)] = HybridIROEager.mp{2}.[(xs{1}, k)]) /\
    --        (forall (k : int),
    --         i{2} <= k < i' + r =>
    --         HybridIROEager.mp{1}.[(xs{1}, k)] = Some (nth true bs{1} k)) /\
    --        eager_eq_except xs{1} i' (i' + r)
    --                        HybridIROEager.mp{1} HybridIROEager.mp{2})
    --       (m{2} - i{2}).
    · equiv_while{2} (={xs, bs, m} ∧ i' ≤ §i{2} ∧ §i{2} ≤ i' + r ∧ §i{1} = i' + r ∧
        §m{1} = i' + r ∧ size §bs{1} = i' + r ∧
        (∀ k : ℤ, i' ≤ k ∧ k < §i{2} →
          FMap.get §HybridIROEager.mp{1} (§xs{1}, k) = FMap.get §HybridIROEager.mp{2} (§xs{1}, k)) ∧
        (∀ k : ℤ, §i{2} ≤ k ∧ k < i' + r →
          FMap.get §HybridIROEager.mp{1} (§xs{1}, k) = some (nth true §bs{1} k)) ∧
        eager_eq_except §xs{1} i' (i' + r) §HybridIROEager.mp{1} §HybridIROEager.mp{2})
        ((§m{2} - §i{2}).toNat)
      -- EC: progress; auto; progress;
      --       [smt() | smt(gt0_r) | smt(get_setE) | smt() |
      --        by apply eager_eq_except_upd2_eq_in | smt()].
      · while_ll_phoare
        intro σ₁
        ec_auto
      · intro σ₁ z
        ec_auto
        rintro xs bs m i mp ⟨⟨⟨rfl, rfl, rfl⟩, hi1, hi2, hI1, hM1, hsz, hA, hB, hE⟩, hlt, hz⟩
        simp only [decide_eq_true_eq] at hlt
        refine ⟨⟨⟨rfl, rfl, rfl⟩, by omega, by omega, hI1, hM1, hsz, fun k hk => ?_,
          fun k hk => hB k ⟨by omega, hk.2⟩,
          eager_eq_except_upd2_eq_in _ _ _ _ _ _ _ hE hi1 (by omega)⟩, by omega⟩
        rw [FMap.get_setE]
        split_ifs with h
        · have hk' : k = i := by have := h; simp at this; omega
          subst hk'
          exact hB k ⟨le_rfl, by omega⟩
        · exact hA k ⟨hk.1, lt_of_le_of_ne (by omega) fun e => h (by rw [e])⟩
      -- EC: skip; progress;
      --       [smt(gt0_r) | smt() | smt() | smt() | smt(eager_eq_except_maps_eq)].
      ec_auto
      rintro m₁ xs₁ i₁ bs₁ mp₁ m₂ xs₂ i₂ bs₂ mp₂ ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, hsz, hm, hB, hE⟩
      have hr := gt0_r
      refine ⟨⟨⟨rfl, rfl, rfl⟩, le_rfl, by omega, rfl, hm, hsz,
        fun k hk => absurd hk.2 (not_lt.mpr hk.1), hB, hE⟩,
        fun τ hbs ⟨⟨hx, hb, hmm⟩, h1, h2, _, _, _, hA, _, hE'⟩ hg => ?_⟩
      simp only [decide_eq_false_iff_not, not_lt] at hg
      have hi : (localVarLens "i" ℤ).get τ = i₂ + r := by omega
      exact ⟨by rw [← hb, hi],
        eager_eq_except_maps_eq _ _ _ true _ _ (by omega) hE' fun k hk => hA k ⟨hk.1, by omega⟩⟩

/-! ### `HybridIROEagerTrans.next_block` and `BlockSpongeTrans.next_block` (EC l. 1188–1505)

EC l. 1188–1305 (`BlockSpongeTrans`, `Prog`, `PrLoopSnoc_sample`, `iter_mul_one_half_pos`,
`BlockGen`, `BlockGen_loop_direct`) are the first port's. -/

open GaudisCrypt.SHA3.Sponge.HybridIRO (eager_inv_imp_block_bits_dom eager_inv_mem_dom1
  eager_inv_not_mem_dom1 eager_invar_eq_except_upd1 BlockSpongeTrans BlockGen BlockGen_loop_direct)

omit [BlockSponge.Params] in
/-- EC's `mkblockK` (the clone `Block` of `BitWord`). -/
theorem mkblockK (w : block) : mkblock (ofblock w) = w := BitWord.mkwordK w

omit [BlockSponge.Params] in
/-- EC's `ofblockK` (the clone `Block` of `BitWord`). -/
theorem ofblockK (s : List Bool) (h : size s = r) : ofblock (mkblock s) = s :=
  BitWord.ofwordK s h

omit [BlockSponge.Params] in
/-- A block's bits, all `r` of them (EC: `size_block`, `take_size`). -/
theorem take_r_ofblock (w : block) : take r (ofblock w) = ofblock w := by
  have h := take_size (ofblock w)
  rwa [size_block] at h

omit [SLCommon.Params] [BlockSponge.Params] in
/-- EC's `nth_change_dfl` (`List.ec`; to move to `Lib/EC/ListLemmas.lean` with the next batch). -/
theorem nth_change_dfl {α : Type} (x0 x1 : α) (s : List α) (n : ℤ) (h : 0 ≤ n ∧ n < size s) :
    nth x1 s n = nth x0 s n := by
  unfold nth size at *
  have hn : n.toNat < s.length := by omega
  simp [h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

/-- EC's `lemma BlockGen_loop_direct : equiv[BlockGen.loop ~ BlockGen.direct : true ==> ={res}]`
(EC l. 1283).  The proof is the first port's (EC: `bypr`, which has no rule here, E12); this is
its statement in EC's form, for `call BlockGen_loop_direct`.  (GAP 9: the first port names a
`module`-declared procedure `X.f.procedure`, the judgment syntax `X.f`'s procedure.) -/
theorem BlockGen_loop_direct_ec :
    equiv[ BlockGen.loop ~ BlockGen.direct : True ==> ={res} ] := by
  have h := BlockGen_loop_direct
  rw [← show Module.Proc.procedure BlockGen.loop = BlockGen.loop.procedure from
      Module.procedure_proc _,
    ← show Module.Proc.procedure BlockGen.direct = BlockGen.direct.procedure from
      Module.procedure_proc _] at h
  exact h

set_option maxHeartbeats 8000000 in
-- one declaration: two cases, two one-sided loops and the two `transitivity{2}` steps
/-- The second judgment of EC's `transitivity HybridIROEagerTrans.next_block_split …` in
`HybridIROEagerTrans_BlockSpongeTrans_next_block` (EC l. 1332–1505: `proc=> /=; inline*; sp; wp.`
to `qed`).  It is its own lemma because procedure-level transitivity is a rule here, not a tactic
(GAP 8). -/
theorem next_block_split_BlockSpongeTrans (i2 : ℤ) :
    equiv[ HybridIROEagerTrans.next_block_split (xs, i, m, bs) ~
      BlockSpongeTrans.next_block (x, i, bs) :
      i2 = §i{2} ∧ 0 ≤ §i{2} ∧ §xs{1} = §x{2} ∧ §i{1} = §i{2} * r ∧ §m{1} - §i{1} = r ∧
        size §bs{2} = i2 ∧ §bs{1} = blocks2bits §bs{2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      (§res{1}).1 = blocks2bits (§res{2}).1 ∧ (§res{1}).2 = (§res{2}).2 * r ∧
        (§res{2}).2 = i2 + 1 ∧ size (§res{2}).1 = i2 + 1 ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ] := by
  -- EC: proc=> /=; inline*; sp; wp.
  equiv_proc; stmt_inline*; stmt_sp; stmt_wp
  -- EC: case (dom BlockSponge.BIRO.IRO.mp{2} (x0{2}, n{2})).
  equiv_case (FMap.dom §BlockSponge.BIRO.IRO.mp{2} (§x0{2}, §n{2}))
  -- EC: rcondf{2} 1; first auto.
  --     rcondt{1} 1; first auto; progress [-delta].
  --     have bb_all_in :
  --       block_bits_all_in_dom x{m} (size bs{m} * r) HybridIROEager.mp{hr}
  --       by apply (eager_inv_mem_dom1 BlockSponge.BIRO.IRO.mp{m}).
  --     smt(gt0_r).
  · stmt_rcondf{2} 1
    · intro σ₁; ec_auto
    stmt_rcondt{1} 1
    · intro σ₂; ec_auto; ec_prep
      exact eager_inv_mem_dom1 _ _ _ _ ‹_› ‹_› _ ⟨le_rfl, by have := gt0_r; omega⟩
    -- EC: simplify; exists* i{1}; elim*=> i1; exists* bs{1}; elim*=> bs1.
    equiv_exists* §i{1}, §(localVarLens "bs" (List Bool)){1}
    intro i1 bs1
    -- EC: conseq
    --       (_ :
    --        i1 = i{1} /\ 0 <= i2 /\ i1 = i2 * r /\ m{1} - i1 = r /\
    --        bs1 = bs{1} /\ size bs{2} = i2 /\ size bs1 = i1 /\
    --        bs1 = blocks2bits bs{2} /\
    --        dom BlockSponge.BIRO.IRO.mp{2} (xs{1}, i2) /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --        bs{1} =
    --        blocks2bits (rcons bs{2} (oget BlockSponge.BIRO.IRO.mp{2}.[(xs{1}, i2)])) /\
    --        i{1} = (i2 + 1) * r /\ size bs{2} = i2 /\ size bs{1} = (i2 + 1) * r /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1});
    --       [progress; smt(size_blocks2bits) | progress; by rewrite size_rcons | idtac].
    equiv_conseq (: i1 = §i{1} ∧ 0 ≤ i2 ∧ i1 = i2 * r ∧ §m{1} - i1 = r ∧
      bs1 = §(localVarLens "bs" (List Bool)){1} ∧
      size §(localVarLens "bs" (List block)){2} = i2 ∧ size bs1 = i1 ∧
      bs1 = blocks2bits §(localVarLens "bs" (List block)){2} ∧
      FMap.dom §BlockSponge.BIRO.IRO.mp{2} (§xs{1}, i2) ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      §(localVarLens "bs" (List Bool)){1} = blocks2bits (rcons §(localVarLens "bs" (List block)){2}
        (oget (FMap.get §BlockSponge.BIRO.IRO.mp{2} (§xs{1}, i2)))) ∧
      §i{1} = (i2 + 1) * r ∧ size §(localVarLens "bs" (List block)){2} = i2 ∧
      size §(localVarLens "bs" (List Bool)){1} = (i2 + 1) * r ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    case pre =>
      ec_prep
      exact ⟨‹_›, ‹_›, by rw [size_blocks2bits, mul_comm], ‹_›, ‹_›⟩
    case post =>
      ec_prep
      exact ⟨rfl, size_rcons _ _, ‹_›⟩
    -- EC: while{1}
    --       (i1 <= i{1} <= m{1} /\ i1 = i2 * r /\ size bs{1} = i{1} /\ m{1} - i1 = r /\
    --        bs{1} =
    --        bs1 ++
    --        take (i{1} - i1)
    --             (ofblock (oget(BlockSponge.BIRO.IRO.mp{2}.[(xs{1}, i2)]))) /\
    --        dom BlockSponge.BIRO.IRO.mp{2} (xs{1}, i2) /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
    --       (m{1} - i{1}).
    equiv_while{1} (i1 ≤ §i{1} ∧ §i{1} ≤ §m{1} ∧ i1 = i2 * r ∧
      size §(localVarLens "bs" (List Bool)){1} = §i{1} ∧ §m{1} - i1 = r ∧
      §(localVarLens "bs" (List Bool)){1} = bs1 ++ take (§i{1} - i1)
        (ofblock (oget (FMap.get §BlockSponge.BIRO.IRO.mp{2} (§xs{1}, i2)))) ∧
      FMap.dom §BlockSponge.BIRO.IRO.mp{2} (§xs{1}, i2) ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
      ((§m{1} - §i{1}).toNat)
    · while_ll_phoare
      intro σ₂
      ec_auto
    · intro σ₂ z
      --     (GAP 6: the invariant reads the right memory; the strict `auto` loops on it, so
      --     `wp` and the plain `skip`)
      stmt_wp; hoare_skip
      rintro i m bs xs mp ⟨⟨h1, h2, h3, hsz, hm, hbs, hd, ei⟩, hlt, hz⟩
      simp only [decide_eq_true_eq] at hlt
      subst h3
      have hget := (ei.1 xs i2 hd).2 i ⟨by omega, by rw [add_mul]; omega⟩
      refine ⟨⟨by omega, by omega, rfl, by rw [size_rcons, hsz], hm, ?_, hd, ei⟩, by omega⟩
      rw [hget, oget_some, show i + 1 - i2 * r = i - i2 * r + 1 by ring,
        take_nth false _ _ ⟨by omega, by rw [size_block]; omega⟩, hbs]
      simp [rcons]
    ec_auto
    rintro i₁ m₁ bs₁ xs₁ mpE mpI bs₂ mp₂ ⟨rfl, hi2, h3, hm, rfl, hsz2, hsz1, hb, hd, ei⟩
    have hr := gt0_r
    refine ⟨⟨le_rfl, by omega, h3, hsz1, hm, by rw [sub_self, take0, cats0], hd, ei⟩,
      fun τ hfr hI hg => ?_⟩
    obtain ⟨hx, -, -⟩ := hfr
    obtain ⟨t1, t2, -, tsz, tm, tbs, td, tei⟩ := hI
    simp only [decide_eq_false_iff_not, not_lt] at hg
    -- (GAP 10: the guard's read of `i` and the invariant's are different atoms for `omega`)
    have hi := (le_antisymm t2 hg).trans (sub_eq_iff_eq_add'.mp tm)
    have hr' : (i2 + 1) * r = i1 + r := by rw [add_mul, one_mul, ← h3]
    refine ⟨?_, by rw [hi, hr'], hsz2, by rw [tsz, hi, hr'], tei⟩
    rw [tbs, hi, show i1 + r - i1 = r by ring, take_r_ofblock, hb, hx]
    simp [rcons, blocks2bits_cat, blocks2bits_sing]
  -- EC: rcondt{2} 1; first auto. rcondf{1} 1; first auto; progress [-delta].
  --     have bb_all_not_in :
  --       block_bits_all_out_dom x{m} (size bs{m} * r) HybridIROEager.mp{hr}
  --       by apply (eager_inv_not_mem_dom1 BlockSponge.BIRO.IRO.mp{m}).
  --     smt(gt0_r).
  · stmt_rcondt{2} 1
    · intro σ₁; ec_auto
    stmt_rcondf{1} 1
    · intro σ₂; ec_auto; ec_prep
      exact eager_inv_not_mem_dom1 _ _ _ _ ‹_› ‹_› ‹_› _ ⟨le_rfl, by have := gt0_r; omega⟩
    -- EC: simplify.
    --     conseq
    --       (_ :
    --        x0{2} = x{2} /\ n{2} = i{2} /\ i2 = i{2} /\ 0 <= i{2} /\ xs{1} = x{2} /\
    --        i{1} = i{2} * r /\ m{1} - i{1} = r /\ size bs{2} = i2 /\
    --        bs{1} = blocks2bits bs{2} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --        _)=> //.
    --     alias{2} 1 with w.
    --     seq 3 1 :
    --       (xs{1} = x0{2} /\ n{2} = i2 /\ i{2} = i2 /\ 0 <= i2 /\
    --        i{1} = i2 * r /\ m{1} - i{1} = r /\ size bs{2} = i2 /\
    --        size cs{1} = r /\ mkblock cs{1} = w{2} /\ bs{1} = blocks2bits bs{2} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
    --     (EC's `w` names the sampled block; here it is the callee's local `r`)
    equiv_seq 3 1 : (§xs{1} = §x0{2} ∧ §n{2} = i2 ∧ §i{2} = i2 ∧ 0 ≤ i2 ∧ §i{1} = i2 * r ∧
      §m{1} - §i{1} = r ∧ size §(localVarLens "bs" (List block)){2} = i2 ∧ size §cs{1} = r ∧
      mkblock §cs{1} = §(localVarLens "r" block){2} ∧
      §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    -- EC: conseq (_ : true ==> cs{1} = ofblock w{2}); first
    --       progress; [by rewrite size_block | by rewrite mkblockK].
    · equiv_conseq (: True ==> §cs{1} = ofblock §(localVarLens "r" block){2})
      case pre => ec_close
      case post =>
        ec_prep
        exact ⟨rfl, rfl, ‹_›, ‹_›, size_block _, mkblockK _, ‹_›⟩
      -- EC: transitivity{2}
      --       { w <@ BlockGen.loop(); }
      --       (true ==> cs{1} = ofblock w{2})
      --       (true ==> ={w})=> //.
      equiv_trans{2} { var w : block; w <- call (BlockGen.loop).procedure (); }
        (True ==> §cs{1} = ofblock §w{2}) (True ==> §w{1} = §(localVarLens "r" block){2})
      · exact fun σ _ => ⟨σ, trivial⟩
      · intro τ₁ τ τ₂ h1 h2; rw [h1, h2]
      -- EC: inline BlockGen.loop; sp; wp.
      --     while (={j, cs} /\ 0 <= j{1} <= r /\ size cs{1} = j{1}).
      --     wp; rnd; skip; progress; smt(size_ge0 size_rcons).
      --     skip; progress.
      --     smt(gt0_r).
      --     have sz_cs_R_eq_r : size cs_R = r by smt().
      --     by rewrite ofblockK.
      · stmt_inline{2} (BlockGen.loop); stmt_sp; stmt_wp
        equiv_while (={j} ∧ §cs{1} = §cs0{2} ∧ 0 ≤ §j{1} ∧ §j{1} ≤ r ∧ size §cs{1} = §j{1})
        · ec_auto
          rintro j₁ cs₁ j₂ cs0₂ ⟨⟨rfl, rfl, h0, hr, hs⟩, hg, -⟩ a -
          have hg' := of_decide_eq_true hg
          exact ⟨⟨rfl, rfl, by omega, by omega, by rw [size_rcons, hs]⟩, rfl⟩
        ec_auto
        rintro j₁ cs₁ cs0₁ j₂ cs0₂ cs₂ ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
        refine ⟨⟨⟨rfl, rfl, le_refl _, ge0_r, rfl⟩, rfl⟩, ?_⟩
        intro τ₁ τ₂ _ _ hI hg _
        obtain ⟨-, hcs, -, hr, hs⟩ := hI
        have hg' := of_decide_eq_false hg
        rw [← hcs, ofblockK _ (by omega)]
      -- EC: transitivity{2}
      --       { w <@ BlockGen.direct(); }
      --       (true ==> ={w})
      --       (true ==> ={w})=> //.
      --     call BlockGen_loop_direct; auto.
      --     inline BlockGen.direct; sim.
      · equiv_trans{2} { var w : block; w <- call (BlockGen.direct).procedure (); }
          (True ==> ={w}) (True ==> §w{1} = §(localVarLens "r" block){2})
        · exact fun σ _ => ⟨σ, trivial⟩
        · intro τ₁ τ τ₂ h1 h2; rw [h1, h2]
        · equiv_call (_ : True ==> ={res})
          · exact BlockGen_loop_direct_ec
          · ec_auto
        · stmt_inline{1} (BlockGen.direct)
          ec_auto
    -- EC: wp; simplify; sp; elim*=> bs_l.
    --     exists* HybridIROEager.mp{1}; elim*=> mp1; exists* i{1}; elim*=> i1.
    · stmt_wp; stmt_sp; equiv_elim* => bs_l
      equiv_exists* §HybridIROEager.mp{1}, §i{1}; intro mp1 i1
      -- EC: conseq
      --       (_ :
      --        xs{1} = x0{2} /\ 0 <= i2 /\ i{1} = i1 /\ i1 = i2 * r /\
      --        m{1} - i1 = r /\
      --        bs{1} = blocks2bits bs{2} ++ ofblock w{2} /\ size bs{2} = i2 /\
      --        size bs{1} = i1 + r /\ mp1 = HybridIROEager.mp{1} /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
      --        bs{1} = blocks2bits bs{2} ++ ofblock w{2} /\
      --        i{1} = (i2 + 1) * r /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2}.[(x0{2}, i2) <- w{2}]
      --                    HybridIROEager.mp{1}).
      equiv_conseq (: §xs{1} = §x0{2} ∧ 0 ≤ i2 ∧ §i{1} = i1 ∧ i1 = i2 * r ∧ §m{1} - i1 = r ∧
          §(localVarLens "bs" (List Bool)){1} =
            blocks2bits §(localVarLens "bs" (List block)){2} ++
              ofblock §(localVarLens "r" block){2} ∧
          size §(localVarLens "bs" (List block)){2} = i2 ∧
          size §(localVarLens "bs" (List Bool)){1} = i1 + r ∧ mp1 = §HybridIROEager.mp{1} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §(localVarLens "bs" (List Bool)){1} =
            blocks2bits §(localVarLens "bs" (List block)){2} ++
              ofblock §(localVarLens "r" block){2} ∧
          §i{1} = (i2 + 1) * r ∧
          eager_invar (FMap.set §BlockSponge.BIRO.IRO.mp{2} (§x0{2}, i2)
            §(localVarLens "r" block){2}) §HybridIROEager.mp{1} ∧ §xs{1} = §x0{2})
      --     (GAP 7: the last conjunct is not EC's.  The one-sided loop's exit goal frames what
      --     the postcondition reads, not what the invariant reads, and the invariant's `xs{1}`
      --     has to be the initial one)
      -- EC: progress;
      --       [by rewrite ofblockK | rewrite size_cat size_blocks2bits /#].
      case pre =>
        ec_prep
        refine ⟨by assumption, by assumption, ?_, ?_, by assumption⟩
        · rw [ofblockK _ (by assumption)]
        · rw [size_cat, size_blocks2bits, mul_comm, (by assumption : size cs₁ = r)]
      -- EC: progress;
      --       [by rewrite -cats1 blocks2bits_cat blocks2bits_sing get_set_sameE
      --                   oget_some ofblockK |
      --        by rewrite size_rcons].
      case post =>
        ec_prep
        simp only [FMap.get_set_sameE, oget_some]
        exact ⟨by simp [rcons, blocks2bits_cat, blocks2bits_sing], size_rcons _ _, by assumption⟩
      -- EC: while{1}
      --       (0 <= i1 /\ m{1} - i1 = r /\ size bs{1} = i1 + r /\
      --        i1 <= i{1} <= m{1} /\
      --        eager_eq_except xs{1} i1 (i1 + r) mp1 HybridIROEager.mp{1} /\
      --        (forall (j : int),
      --         i1 <= j < i{1} =>
      --         HybridIROEager.mp{1}.[(xs{1}, j)] = Some(nth false bs{1} j)))
      --       (m{1} - i{1}).
      equiv_while{1} (0 ≤ i1 ∧ §m{1} - i1 = r ∧
        size §(localVarLens "bs" (List Bool)){1} = i1 + r ∧ i1 ≤ §i{1} ∧ §i{1} ≤ §m{1} ∧
        eager_eq_except §xs{1} i1 (i1 + r) mp1 §HybridIROEager.mp{1} ∧
        (∀ j : ℤ, i1 ≤ j ∧ j < §i{1} → FMap.get §HybridIROEager.mp{1} (§xs{1}, j) =
          some (nth false §(localVarLens "bs" (List Bool)){1} j)))
        ((§m{1} - §i{1}).toNat)
      -- EC: progress; auto.
      · while_ll_phoare
        intro σ₂
        ec_auto
      -- EC: move=> |> &hr ge0_i1 m_min_i1_eq_r sz_bs_eq_i1_plus_r il_le_i _ ee mp_ran_eq lt_im.
      --     split. split; first smt().
      --     split; first smt(eager_eq_except_upd2_eq_in).
      --     move=> j i1_le_j j_lt_i_add1.
      --     case: (i{hr} = j)=> [-> | ne_ij].
      --     rewrite get_setE /=; smt(nth_onth onth_nth).
      --     rewrite get_setE.
      --     have -> /= : (xs{hr}, j) <> (xs{hr}, i{hr}) by smt().
      --     rewrite mp_ran_eq /#.
      --     smt().
      · intro σ₂ z
        ec_auto
        rintro m bs i xs mp ⟨⟨h0, hm, hsz, hi1, him, ee, hran⟩, hlt, hz⟩
        simp only [decide_eq_true_eq] at hlt
        refine ⟨⟨h0, hm, hsz, by omega, by omega,
          eager_eq_except_upd2_eq_in _ _ _ _ _ _ _ ee hi1 (by omega), fun j hj => ?_⟩, by omega⟩
        rw [FMap.get_setE]
        split_ifs with h
        · obtain rfl : j = i := (Prod.mk.inj h).2
          rw [nth_change_dfl false true _ _ ⟨by omega, by omega⟩]
        · have hne : j ≠ i := fun e => h (by rw [e])
          exact hran j ⟨hj.1, by omega⟩
      -- EC: skip=>
      --       &1 &2 [# -> ge0_i2 -> i1_eq_i2_tim_r m_min_i1_eq_r
      --       bs1_eq sz_bs2_eq_i2 sz_bs1_eq_i1_add_r -> ei].
      --     have ge0_i1 : 0 <= i1 by rewrite i1_eq_i2_tim_r divr_ge0 // ge0_r.
      --     split. split=> //. split; first smt(ge0_r).
      --     split; first smt(). split; smt(ge0_r).
      --     move=> mp_L i_L.
      --     split; first smt().
      --     move=> not_i_L_lt_m [# _ _ _ i1_le_i_L i_L_le_m ee mp_L_ran_eq].
      --     split; first smt().
      --     split; first smt().
      --     apply (eager_invar_eq_except_upd1 BlockSponge.BIRO.IRO.mp{2}
      --            HybridIROEager.mp{1} mp_L x0{2} i2 w{2})=> //.
      --     by rewrite mulzDl /= -i1_eq_i2_tim_r.
      --     move=> j j_ran.
      --     rewrite mp_L_ran_eq 1:/#; congr; rewrite bs1_eq nth_cat.
      --     have -> : size(blocks2bits bs{2}) = i2 * r
      --       by rewrite size_blocks2bits /#.
      --     have -> // : j < i2 * r = false by smt().
      ec_auto
      rintro xs₁ i₁ m₁ bs₁ mpE bs₁1 r₁ x0₁ mpI x0₂ bs₂ r₂ mp₂
        ⟨rfl, hi2, rfl, h3, hm, hb, hsz2, hsz1, rfl, ei⟩
      have hr := gt0_r
      have h0 : 0 ≤ i₁ := by rw [h3]; exact mul_nonneg hi2 ge0_r
      have hr' : (i2 + 1) * r = i₁ + r := by rw [add_mul, one_mul, ← h3]
      refine ⟨⟨h0, hm, hsz1, le_rfl, by omega, fun _ _ _ => rfl, fun j hj => by omega⟩,
        fun τ hfr hI hg => ?_⟩
      obtain ⟨hbs, -, -, -, hx, -⟩ := hfr
      obtain ⟨-, tm, -, t1, t2, tee, tran⟩ := hI
      simp only [decide_eq_false_iff_not, not_lt] at hg
      -- (GAP 10, as in the first case)
      have hi := (le_antisymm t2 hg).trans (sub_eq_iff_eq_add'.mp tm)
      refine ⟨hbs.trans hb, by rw [hr', hi], ?_, hx⟩
      refine eager_invar_eq_except_upd1 mp₂ _ _ _ i2 r₂ hi2 ei ?_ fun j hj => ?_
      · rw [← h3, hr', ← hx]; exact tee
      · rw [← h3, hr'] at hj
        rw [← hx, tran j ⟨hj.1, by rw [hi]; exact hj.2⟩, hbs, hb, nth_cat, size_blocks2bits, hsz2,
          if_neg (by rw [mul_comm, ← h3]; omega), mul_comm r i2]

/-- EC's `lemma HybridIROEagerTrans_BlockSpongeTrans_next_block (i2 : int)` (EC l. 1307).

EC: `transitivity HybridIROEagerTrans.next_block_split (…) (…)=> //.`, the rule
`prhlProc_trans_ec` here (GAP 8): its two side conditions (EC's `exists HybridIROEager.mp{1}
(x{2}, i{1}, m{1}, blocks2bits bs{2})`, and the postconditions composed), then
`HybridIROEagerTrans_next_block_split` and `next_block_split_BlockSpongeTrans`. -/
theorem HybridIROEagerTrans_BlockSpongeTrans_next_block (i2 : ℤ) :
    equiv[ HybridIROEagerTrans.next_block (xs, i, m, bs) ~
      BlockSpongeTrans.next_block (x, i, bs) :
      i2 = §i{2} ∧ 0 ≤ §i{2} ∧ §xs{1} = §x{2} ∧ §i{1} = §i{2} * r ∧ §m{1} - §i{1} = r ∧
        §bs{1} = blocks2bits §bs{2} ∧ size §bs{2} = §i{2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      (§res{1}).1 = blocks2bits (§res{2}).1 ∧ (§res{1}).2 = (§res{2}).2 * r ∧
        (§res{2}).2 = i2 + 1 ∧ size (§res{2}).1 = i2 + 1 ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ] := by
  refine prhlProc_trans_ec ?_ ?_ HybridIROEagerTrans_next_block_split
    (next_block_split_BlockSpongeTrans i2)
  -- EC: move=> |> &1 &2 ge0_i2 -> i1_eq_i2_tim_r m_min_i1_eq_r -> sz_bs_eq_i2 ei.
  --     exists HybridIROEager.mp{1} (x{2}, i{1}, m{1}, blocks2bits bs{2})=> |>.
  --     split; first smt().
  --     split; first smt(size_blocks2bits).
  --     apply
  --       (eager_inv_imp_block_bits_dom BlockSponge.BIRO.IRO.mp{2}
  --        HybridIROEager.mp{1} x{2} i{1})=> //.
  --     rewrite i1_eq_i2_tim_r mulr_ge0 // ge0_r.
  --     rewrite i1_eq_i2_tim_r dvdz_mull dvdzz.
  · rintro ⟨xs, i, m, bs⟩ g₁ ⟨x, i', bs'⟩ g₂ ⟨rfl, h0, hx, hi, hm, hbs, hsz, ei⟩
    replace h0 : 0 ≤ i2 := h0
    replace hx : xs = x := hx
    replace hi : i = i2 * r := hi
    replace hm : m - i = r := hm
    replace hbs : bs = blocks2bits bs' := hbs
    replace hsz : size bs' = i2 := hsz
    refine ⟨(x, i, m, blocks2bits bs'), g₁, ⟨⟨rfl, rfl, hx, hbs, rfl⟩, ?_, ?_, ?_⟩,
      rfl, h0, rfl, hi, hm, hsz, rfl, ei⟩
    · exact (sub_eq_iff_eq_add'.mp hm)
    · change size bs = i
      rw [hbs, size_blocks2bits, hsz, hi, mul_comm]
    · exact hx ▸ eager_inv_imp_block_bits_dom _ _ x i (by rw [hi]; exact mul_nonneg h0 ge0_r)
        ⟨i2, by rw [hi, mul_comm]⟩ ei
  · rintro r₁ g₁ r' g r₂ g₂ ⟨rfl, hmp⟩ ⟨h1, h2, h3, h4, ei⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [hmp]; exact ei
  -- EC: apply HybridIROEagerTrans_next_block_split.
  --     (the second judgment is `next_block_split_BlockSpongeTrans` above)

/-! ### `HybridIROEagerTrans.loop` and `BlockSpongeTrans.loop` (EC l. 1507–1612) -/

omit [BlockSponge.Params] in
/-- `HybridIROEager.fill_in` touches `HybridIROEager.mp`.  Not an EC lemma (EC reads a concrete
module's globals off its code, for `call (_ : ={HybridIROEager.mp})`). -/
@[fp_bound] theorem fvP_HybridIROEager_fill_in :
    FVP.fvP HybridIROEager.fill_in ≤ HybridIROEager.mp.footprint := by
  fp_module HybridIROEager.mp

omit [BlockSponge.Params] in
/-- `BlockSponge.BIRO.IRO.fill_in` touches `BlockSponge.BIRO.IRO.mp`.  Not an EC lemma (as
`fvP_HybridIROEager_fill_in`). -/
@[fp_bound] theorem fvP_BIRO_IRO_fill_in :
    FVP.fvP BlockSponge.BIRO.IRO.fill_in ≤ BlockSponge.BIRO.IRO.mp.footprint := by
  fp_module BlockSponge.BIRO.IRO.mp

omit [BlockSponge.Params] in
/-- The guard that EC's `splitwhile{1} 3 : (i < (n - 1) * r)` leaves on the first loop, at
`n = n' + 1`. -/
private theorem splitwhile_guard (i n : ℤ) :
    (decide (i < (n + 1) * r) && decide (i < (n + 1 - 1) * r)) = decide (i < n * r) := by
  have hr := gt0_r
  rw [add_sub_cancel_right]
  by_cases h : i < n * r
  · have h1 : i < (n + 1) * r := by rw [add_mul, one_mul]; omega
    simp [h, h1]
  · simp [h]

set_option maxHeartbeats 8000000 in
-- one declaration: an induction, four `transitivity` steps and four loops
/-- EC's `lemma HybridIROEagerTrans_BlockSpongeTrans_loop (n' : int)` (EC l. 1507).

EC's script.  `elim n'` is `induction n', ge0_n' using Int.le_induction`, after `proc` as in EC,
so the hypothesis is about the two bodies and `conseq IH` fits.  A middle memory (EC's
`exists HybridIROEager.mp{1} n' xs{2}`) is one side's memory with `n` set, and `simp_reads`
reads through it.  The callee goals of `call (_ : ={HybridIROEager.mp})` and
`call (_ : ={BlockSponge.BIRO.IRO.mp})` (EC: `if=> //; wp; rnd; auto`) are closed by the
tactic; EC's `smt`s on the split loop's guard are `splitwhile_guard`. -/
theorem HybridIROEagerTrans_BlockSpongeTrans_loop (n' : ℤ) :
    equiv[ HybridIROEagerTrans.loop (n, xs) ~ BlockSpongeTrans.loop (n, xs) :
      ={xs, n} ∧ n' = §n{1} ∧ 0 ≤ n' ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      (§res{1}).1 = n' * r ∧ (§res{2}).1 = n' ∧ size (§res{2}).2 = n' ∧
        (§res{1}).2 = blocks2bits (§res{2}).2 ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ] := by
  -- EC: case (0 <= n'); last first=> [not_ge0_n' | ge0_n'].
  by_cases ge0_n' : 0 ≤ n'
  swap
  -- EC: proc=> /=; exfalso.
  · equiv_proc; equiv_exfalso
    exact fun _ _ h => ge0_n' h.2.2.1
  -- EC: proc=> /=.
  --     move: ge0_n'; elim n'=> [| n' ge0_n' IH].
  equiv_proc
  induction n', ge0_n' using Int.leInduction with
  -- EC: sp. rcondf{1} 1; auto. rcondf{2} 1; auto.
  | base =>
    stmt_sp
    stmt_rcondf{1} 1
    · intro σ₂; ec_auto
      intro xs n mp i bs h
      obtain ⟨⟨⟨⟨⟨-, rfl, -⟩, rfl⟩, -⟩, -⟩, -⟩ := h
      simp
    stmt_rcondf{2} 1
    · intro σ₁; ec_auto
    ec_auto
    rintro xs₁ n₁ mp₁ i₁ bs₁ xs₂ n₂ mp₂ i₂ bs₂ ⟨⟨⟨⟨⟨⟨-, -⟩, -, ei⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨(zero_mul _).symm, rfl, by simp [size], by simp [blocks2bits], ei⟩
  | succ n' ge0_n' IH =>
    -- EC: splitwhile{1} 3 : (i < (n - 1) * r); splitwhile{2} 3 : (i < n - 1).
    stmt_splitwhile{1} 3 : §i < (§n - 1) * r
    stmt_splitwhile{2} 3 : §i < §n - 1
    -- EC: seq 3 3 :
    --       (={xs, n} /\ n{1} = n' + 1 /\ i{1} = n' * r /\ i{2} = n' /\
    --        size bs{2} = n' /\ bs{1} = blocks2bits bs{2} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
    equiv_seq 3 3 : (={xs, n} ∧ §n{1} = n' + 1 ∧ §i{1} = n' * r ∧ §i{2} = n' ∧
      size §(localVarLens "bs" (List block)){2} = n' ∧
      §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    -- EC: conseq
    --       (_ :
    --        ={xs, n} /\ n' + 1 = n{1} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --        i{1} = n' * r /\ i{2} = n' /\ size bs{2} = n' /\
    --        bs{1} = blocks2bits bs{2} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
    · equiv_conseq (: ={xs, n} ∧ n' + 1 = §n{1} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §i{1} = n' * r ∧ §i{2} = n' ∧ size §(localVarLens "bs" (List block)){2} = n' ∧
          §(localVarLens "bs" (List Bool)){1} =
            blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
      case pre => ec_close
      case post => ec_close
      -- EC: transitivity{1}
      --       { i <- 0; bs <- [];
      --         while (i < n * r) {
      --           b <@ HybridIROEager.fill_in(xs, i);
      --           bs <- rcons bs b;
      --           i <- i + 1;
      --         }
      --       }
      --       (={xs, HybridIROEager.mp} /\ n{1} = n' + 1 /\ n{2} = n' ==>
      --        ={bs, i, HybridIROEager.mp})
      --       (={xs} /\ n{1} = n' /\ n{2} = n' + 1 /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
      --        i{1} = n' * r /\ i{2} = n' /\ size bs{2} = n' /\
      --        bs{1} = blocks2bits bs{2} /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
      equiv_trans{1} {
          i <- 0; bs <- [];
          while (decide ($i < $n * r)) {
            b <- call (HybridIROEager.fill_in).procedure ($xs, $i);
            bs <- rcons $bs $b;
            i <- $i + 1;
          } }
        (={xs, HybridIROEager.mp} ∧ §n{1} = n' + 1 ∧ §n{2} = n' ==>
          §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧
          ={i, HybridIROEager.mp})
        (={xs} ∧ §n{1} = n' ∧ §n{2} = n' + 1 ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §i{1} = n' * r ∧ §i{2} = n' ∧ size §(localVarLens "bs" (List block)){2} = n' ∧
          §(localVarLens "bs" (List Bool)){1} =
            blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
      -- EC: progress; exists HybridIROEager.mp{1} n' xs{2}=> //.
      · rintro σ₁ σ₂ ⟨⟨hxs, hn⟩, hn', ei⟩
        refine ⟨(localVarLens "n" ℤ).set n' σ₁, ?_⟩
        simp_reads
        exact ⟨hn'.symm, hxs, hn.symm.trans hn'.symm, ei⟩
      · intro τ₁ τ τ₂ ⟨h1, h2, h3⟩ ⟨k1, k2, k3, k4, k5⟩
        exact ⟨h2.trans k1, k2, k3, h1.trans k4, h3 ▸ k5⟩
      -- EC: while (={xs, i, bs, HybridIROEager.mp} /\ n{1} = n' + 1 /\ n{2} = n').
      --     wp. call (_ : ={HybridIROEager.mp}). if=> //; wp; rnd; auto.
      --     skip; progress; smt(ge0_r).
      --     auto; smt().
      · clear IH
        equiv_while (={xs, i, bs, HybridIROEager.mp} ∧ §n{1} = n' + 1 ∧ §n{2} = n')
        · stmt_wp
          equiv_call (_ : ={HybridIROEager.mp})
          ec_auto
          rintro xs₁ i₁ bs₁ mp₁ n₁ xs₂ i₂ bs₂ mp₂ n₂ ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, -⟩
          refine ⟨⟨rfl, rfl⟩, ?_⟩
          rintro r₁ g₁ r₂ g₂ ⟨rfl, hmp⟩
          exact ⟨⟨⟨rfl, rfl, rfl, hmp⟩, rfl, rfl⟩, splitwhile_guard _ _⟩
        ec_auto
        rintro xs₁ mp₁ n₁ xs₂ mp₂ n₂ ⟨⟨rfl, rfl⟩, rfl, rfl⟩
        refine ⟨⟨⟨⟨rfl, rfl⟩, rfl, rfl⟩, ?_⟩,
          fun τ₁ τ₂ ⟨⟨_, hi, hbs, hmp⟩, _, _⟩ _ _ => ⟨hbs, hi, hmp⟩⟩
        exact splitwhile_guard _ _
      -- EC: transitivity{2}
      --       { i <- 0; bs <- [];
      --         while (i < n) {
      --           b <@ BlockSponge.BIRO.IRO.fill_in(xs, i);
      --           bs <- rcons bs b;
      --           i <- i + 1;
      --         }
      --       }
      --       (={xs, n} /\ n{1} = n' /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
      --        i{1} = n' * r /\ i{2} = n' /\ size bs{2} = n' /\
      --        bs{1} = blocks2bits bs{2} /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
      --       (={xs,BlockSponge.BIRO.IRO.mp} /\ n{1} = n' /\ n{2} = n' + 1 ==>
      --        ={i, bs, BlockSponge.BIRO.IRO.mp})=> //.
      · equiv_trans{2} {
            i <- 0; bs <- [];
            while (decide ($i < $n)) {
              b <- call (BlockSponge.BIRO.IRO.fill_in).procedure ($xs, $i);
              bs <- rcons $bs $b;
              i <- $i + 1;
            } }
          (={xs, n} ∧ §n{1} = n' ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
            §i{1} = n' * r ∧ §i{2} = n' ∧ size §(localVarLens "bs" (List block)){2} = n' ∧
            §(localVarLens "bs" (List Bool)){1} =
              blocks2bits §(localVarLens "bs" (List block)){2} ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
          (={xs, BlockSponge.BIRO.IRO.mp} ∧ §n{1} = n' ∧ §n{2} = n' + 1 ==>
            §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
            ={i, BlockSponge.BIRO.IRO.mp})
        -- EC: progress; exists BlockSponge.BIRO.IRO.mp{2} n{1} xs{2}=> //.
        · rintro σ₁ σ₂ ⟨hxs, hn, hn', ei⟩
          refine ⟨(localVarLens "n" ℤ).set n' σ₂, ?_⟩
          simp_reads
          exact ⟨⟨⟨hxs, hn⟩, hn, ei⟩, hn'⟩
        · intro τ₁ τ τ₂ ⟨k1, k2, k3, k4, k5⟩ ⟨h1, h2, h3⟩
          exact ⟨k1, k2.symm.trans h2 |>.symm, h1 ▸ k3, h1 ▸ k4, h3 ▸ k5⟩
        -- EC: conseq IH=> //.
        · equiv_conseq IH
          · ec_close
          · ec_close
        -- EC: while
        --       (={xs, bs, i, BlockSponge.BIRO.IRO.mp} /\ n{1} = n' /\ n{2} = n' + 1).
        --     wp. call (_ : ={BlockSponge.BIRO.IRO.mp}). if=> //; wp; rnd; auto.
        --     auto; smt().
        --     auto; smt().
        · clear IH
          equiv_while (={xs, i, BlockSponge.BIRO.IRO.mp} ∧
            §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
            §n{1} = n' ∧ §n{2} = n' + 1)
          · stmt_wp
            equiv_call (_ : ={BlockSponge.BIRO.IRO.mp})
            ec_auto
          ec_auto
    clear IH
    -- EC: unroll{2} 1. rcondt{2} 1; first auto; progress; smt().
    stmt_unroll{2} 1
    stmt_rcondt{2} 1
    · intro σ₁; ec_auto
    -- EC: rcondf{2} 4. auto. call (_ : true). if=> //. auto.
    stmt_rcondf{2} 4
    · intro σ₁
      stmt_wp
      hoare_call (: True ==> True)
      · hoare_proc; ec_auto
      · ec_auto
    -- EC: transitivity{1}
    --       { (bs, i) <@ HybridIROEagerTrans.next_block(xs, i, (n' + 1) * r, bs); }
    --       (={xs, i, bs, HybridIROEager.mp} /\ n{1} = n' + 1 ==>
    --        ={i, bs, HybridIROEager.mp})
    --       (={xs} /\ i{1} = n' * r /\ i{2} = n' /\
    --        size bs{2} = n' /\ bs{1} = blocks2bits bs{2} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --        i{1} = (n' + 1) * r /\ i{2} = n' + 1 /\ size bs{2} = n' + 1 /\
    --        bs{1} = blocks2bits bs{2} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
    equiv_trans{1} {
        bs, i <- call (HybridIROEagerTrans.next_block).procedure ($xs, $i, (n' + 1) * r, $bs); }
      (={xs, i, HybridIROEager.mp} ∧
        §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧
        §n{1} = n' + 1 ==>
        ={i, HybridIROEager.mp} ∧
        §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2})
      (={xs} ∧ §i{1} = n' * r ∧ §i{2} = n' ∧ size §(localVarLens "bs" (List block)){2} = n' ∧
        §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
        §i{1} = (n' + 1) * r ∧ §i{2} = n' + 1 ∧
        size §(localVarLens "bs" (List block)){2} = n' + 1 ∧
        §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    -- EC: progress;
    --       exists HybridIROEager.mp{1} (blocks2bits bs{2}) (size bs{2} * r) xs{2}=> //.
    · rintro σ₁ σ₂ ⟨⟨hxs, hn⟩, hn1, hi1, hi2, hsz, hbs, ei⟩
      exact ⟨σ₁, ⟨⟨rfl, rfl, rfl⟩, rfl, hn1⟩, hxs, hi1, hi2, hsz, hbs, ei⟩
    · rintro τ₁ τ τ₂ ⟨⟨h1, h2⟩, h3⟩ ⟨k1, k2, k3, k4, k5⟩
      exact ⟨h1.trans k1, k2, k3, h3.trans k4, h2 ▸ k5⟩
    -- EC: inline HybridIROEagerTrans.next_block; sp; wp.
    --     while
    --       (xs{1} = xs0{2} /\ i{1} = i0{2} /\ n{1} = n' + 1 /\
    --        m{2} = (n' + 1) * r /\ bs{1} = bs0{2} /\
    --        ={HybridIROEager.mp}).
    --     wp. call (_ : ={HybridIROEager.mp}). if=> //; wp; rnd; auto.
    --     auto. auto.
    · stmt_inline{2} (HybridIROEagerTrans.next_block); stmt_sp; stmt_wp
      equiv_while (§xs{1} = §xs0{2} ∧ §i{1} = §i0{2} ∧ §n{1} = n' + 1 ∧ §m{2} = (n' + 1) * r ∧
        §(localVarLens "bs" (List Bool)){1} = §bs0{2} ∧ ={HybridIROEager.mp})
      · stmt_wp
        equiv_call (_ : ={HybridIROEager.mp})
        ec_auto
      ec_auto
    -- EC: transitivity{2}
    --       { (bs, i) <@ BlockSpongeTrans.next_block(xs, i, bs); }
    --       (={xs} /\ i{1} = n' * r /\ i{2} = n' /\
    --       size bs{2} = n' /\ bs{1} = blocks2bits bs{2} /\
    --       eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --       i{1} = (n' + 1) * r /\ i{2} = n' + 1 /\ size bs{2} = n' + 1 /\
    --       bs{1} = blocks2bits bs{2} /\
    --       eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
    --       (={xs, bs, i, BlockSponge.BIRO.IRO.mp} ==>
    --        ={xs, bs, i, BlockSponge.BIRO.IRO.mp})=> //.
    · equiv_trans{2} {
          bs, i <- call (BlockSpongeTrans.next_block).procedure ($xs, $i, $bs); }
        (={xs} ∧ §i{1} = n' * r ∧ §i{2} = n' ∧ size §(localVarLens "bs" (List block)){2} = n' ∧
          §(localVarLens "bs" (List Bool)){1} =
            blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §i{1} = (n' + 1) * r ∧ §i{2} = n' + 1 ∧
          size §(localVarLens "bs" (List block)){2} = n' + 1 ∧
          §(localVarLens "bs" (List Bool)){1} =
            blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
        (={xs, i, BlockSponge.BIRO.IRO.mp} ∧
          §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ==>
          ={xs, i, BlockSponge.BIRO.IRO.mp} ∧
          §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2})
      -- EC: progress; exists BlockSponge.BIRO.IRO.mp{2} bs{2} (size bs{2}) xs{2}=> //.
      · rintro σ₁ σ₂ ⟨hxs, hi1, hi2, hsz, hbs, ei⟩
        exact ⟨σ₂, ⟨hxs, hi1, hi2, hsz, hbs, ei⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
      · rintro τ₁ τ τ₂ ⟨k1, k2, k3, k4, k5⟩ ⟨⟨-, h2, h3⟩, h4⟩
        exact ⟨k1, h2 ▸ k2, h4 ▸ k3, h4 ▸ k4, h3 ▸ k5⟩
      -- EC: call (HybridIROEagerTrans_BlockSpongeTrans_next_block n').
      --     skip; progress; smt().
      · equiv_call (HybridIROEagerTrans_BlockSpongeTrans_next_block n')
        ec_auto
        rintro xs₁ i₁ bs₁ mp₁ xs₂ i₂ bs₂ mp₂ ⟨rfl, rfl, rfl, hsz, rfl, ei⟩
        refine ⟨⟨rfl, ge0_n', rfl, rfl, by ring, rfl, hsz, ei⟩, ?_⟩
        rintro r₁ g₁ r₂ g₂ ⟨h1, h2, h3, h4, h5⟩
        exact ⟨by rw [h2, h3], h3, h4, h1, h5⟩
      -- EC: inline BlockSpongeTrans.next_block.
      --     wp; sp. call (_ : ={BlockSponge.BIRO.IRO.mp}). if=> //; wp; rnd; skip; smt().
      --     auto.
      · stmt_inline{1} (BlockSpongeTrans.next_block)
        stmt_wp; stmt_sp
        equiv_call (_ : ={BlockSponge.BIRO.IRO.mp})
        ec_auto

end HybridIRO

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

/-- `BlockSponge.Sponge(Perm)`, as `stmt_inline` names the callee. -/
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
    equiv[ Sponge(Perm).f (x) ~ RaiseFun(BlockSponge.Sponge(Perm)).f (x) :
      ={x, glob Perm} ==> ={res, glob Perm} ] := by
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
