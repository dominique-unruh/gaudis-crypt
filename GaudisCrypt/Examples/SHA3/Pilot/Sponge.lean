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

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

/-!
# The sponge construction (EasyCrypt `proof/Sponge.ec`) — EC-fidelity port, in progress

Ported so far, on the strict tactics: `Sponge_is_StdSponge` (EC l. 99); the theory `HybridIRO`
up to `Lower_HybridIROEager_f` (EC l. 256–900); and `Sponge_Raise_BlockSponge_f`
(EC l. 1922), which was the second tactic experiment and is described below.  The rest of the
file follows in EC's order (`notes/SHA3/Mapping.md`).

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
