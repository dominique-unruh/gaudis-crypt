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
import GaudisCrypt.Logic.ByPrEquiv
import GaudisCrypt.Logic.PHoareRnd
import GaudisCrypt.Logic.ECWhile
import GaudisCrypt.Logic.ModuleFootprint
import GaudisCrypt.Syntax.PrSyntax
import GaudisCrypt.Logic.ECTrans
import GaudisCrypt.Logic.ECElim
import GaudisCrypt.Logic.ECConseqHoare
import GaudisCrypt.Logic.ECProcInv
import GaudisCrypt.Logic.ModuleComp
import GaudisCrypt.Examples.SHA3.BlockSponge
import GaudisCrypt.Lib.EC.PROM
import GaudisCrypt.Lib.EC.DList
import GaudisCrypt.Lib.EC.Int
import GaudisCrypt.Logic.PRHLWp
import GaudisCrypt.Logic.LoopTransform
import GaudisCrypt.Examples.SHA3.IndifferentiabilityCalls
import GaudisCrypt.Logic.SyntacticFrame
import GaudisCrypt.Logic.ConcreteFootprint
import GaudisCrypt.Logic.FootprintSolver

/-!
# The sponge construction (EasyCrypt `proof/Sponge.ec`) — EC-fidelity port

Ported on the strict tactics: `Sponge_is_StdSponge` (EC l. 99); the whole theory `HybridIRO`
(EC l. 256–1909; l. 1188–1282, the modules `BlockSpongeTrans` and `BlockGen`, are the first
port's);
`Sponge_Raise_BlockSponge_f` (EC l. 1922), which was the second tactic experiment and is
described below; and the final section with `conclusion` (EC l. 1913–2163).

Translation:
* the modules are the first port's (section `FirstPort` below); a procedure takes its
  parameters as one tuple there, so a statement names them at the triple
  (`StdSponge(P).f (x) ~ …`, `HybridIROLazy.f (xs, n) ~ …`);
* the theory `HybridIRO` is a namespace; its module variables `HybridIROLazy.mp`,
  `HybridIROEager.mp` and those of the local clone `ERO` are `global_var`s;
* a local clone's variables are fresh for a declared module in EC; here the restriction names
  them (`-ERO.RO.m, -ERO.FRO.m`).

Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1 (closed 2026-11-17): a procedure of a module of one clone's module type, read at
  another clone's (`LowerDist(Dist)` hands `BlockSponge`'s primitive to the bit sponge's
  `Dist`), is opened by `equiv_proc` as EC's `proc` does.
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
* GAP 7 (closed 2026-11-21): the exit goal of a one-sided loop framed what the postcondition
  reads, not what the invariant reads (`xs{1}` in `next_block_split_BlockSpongeTrans`, added to
  EC's `conseq` there); its frame now has both.
* GAP 8: `transitivity N (P₁ ==> Q₁) (P₂ ==> Q₂)` on procedures is the rule `prhlProc_trans_ec`,
  not a tactic: the second judgment is its own lemma, and the side conditions are over the
  parameter tuples (hypotheses restated by `replace` before use).
* GAP 9 (closed 2026-11-18): `BlockGen_loop_direct` is EC's `bypr` proof, no longer the first
  port's restated by a rewrite.
* GAP 10: after a loop, the guard's read of a local and the invariant's read of it can be
  different atoms for `omega` (equal by `rfl`): `le_antisymm` on the two hypotheses instead.
* GAP 11: `={bs}` in a condition of `equiv_trans` is not resolved when the two sides of the
  goal have a `bs` of different types, although the middle program's is the left one's:
  `§(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2}`.
* `call (_ : ={HybridIROEager.mp})` on the concrete `fill_in` needs its footprint, which EC reads
  off the code: `fvP_HybridIROEager_fill_in`, `fvP_BIRO_IRO_fill_in` (`@[fp_bound]`).  The
  callee's goal (EC: `if=> //; wp; rnd; auto`) is then closed by the tactic.
* GAP 12: the strict `auto` and `equiv_skip` run out of recursion depth on a goal whose
  conditions have `bs{1} = take n1 bs{2}` next to `={bs}` (the exit of the loop pair after
  `splitwhile{2} 1 : i < n1` in `HybridIROEager_f_BlockIRO_f`): `prhlStmt_skip` and the
  implication by hand.
* GAP 13: `sim` does not pass an inlined call that copies its parameters and has a loop
  (`inline HybridIROEagerTrans.next_block; sim`): the `while` rule, as in the loop lemma.
* A middle program of `transitivity` is over the variables the goal mentions, not the whole
  memory: where EC's condition names a variable that neither side reads any more
  (`n{2} = n1 %/ r`), the conjunct is dropped; an inlined parameter keeps its name when the
  caller no longer reads one of that name (EC's `n0` is `n`).
* `equiv_conseq H` on procedures states `post` without the precondition, where EC keeps it:
  `equiv_conseq_pre H` (`Logic/ECConseqHoare.lean`) where the proof needs it.  `exists*` on a
  procedure judgment reads the declared parameter names (`§x{1}` for `HybridIROEager.f`'s
  `xs`).  A side goal about parameters and results is over their tuple types: introduce them
  at the plain types (`rintro ⟨xs, (n : ℤ)⟩ … (r₁ : List Bool)`), restate the hypotheses by
  `replace`, and `change` the goal, before `rw` or `omega`.
* EC's `alias{2} 1 with w` is not needed: the sampled block is the inlined callee's local `r`
  (two locals `bs`, `r` of different types on the two sides are read as
  `§(localVarLens "bs" (List Bool)){1}`).
* A statement that names `HIRO(…).f`'s parameters `(xs, n)` as EC does gets a warning: the module
  type `HYBRID_IRO` declares them `(x, n)`.
* GAP 14 (exception E2): EC's module type `SIMULATOR` lists the oracles of each procedure
  (`init { }`, `f {F.f}`, `fi {F.f}`); `declare module` knows them only for a functor with one
  procedure.  The final section states them as a hypothesis (`BlockSim_rep`, the first port's
  `SIMULATOR.Representable`).  From it: `BlockSim_init_call` for EC's `call (_ : true)` on
  `BlockSim(F).init`, and EC's `proc (I)` on `BlockSim(F).f`, `.fi` by `equiv_proc (I)`
  (`Logic/ECProcInv.lean`) with the first port's rules `SIMULATOR.call_f`, `call_fi` tagged
  `@[proc_inv]`.
  EC's `swap` past `BlockSim(F).init` has no footprint to check (the oracle list is known for
  the procedure's behaviour, not for its code): the call's invariant says what the swap would
  (`equiv_call (_ : ={glob Dist, glob BlockSim} ∧ §HybridIROLazy.mp{2} = FMap.empty)`, the rule
  `SIMULATOR.call_init`).
* GAP 15: `sim` finds no equality set for a call of `Dist` whose oracles are the same on both
  sides when the precondition's equalities are a `glob` region and a variable
  (`={glob Dist, glob BlockSim, HybridIROLazy.mp}`): the call with EC's set
  (`equiv_call (_ : ={glob BlockSim} ∧ §mp{1} = §mp{2})`), the simulator's oracles by
  `equiv_proc (I)` and `sim`, the concrete one by a judgment `={x, mp} ==> ={res, mp}` (`sim`)
  under `equiv_conseq_frame`.
* EC's `call (_ : P ==> Q). proc (I)=> //.` on the declared `Dist` is one step,
  `equiv_call (_ : ={glob BlockSim} ∧ I)` (the `={…} ∧` without parentheses); the implication
  that EC proves next (`progress; apply lazy_invar0`) is then in the last goal, with the code
  before the call.
* EC's `conseq H` where the goal keeps a `glob` that `H` does not mention: `equiv_conseq_frame H`
  (`Logic/ECProcInv.lean`), which frames what the procedures do not write and closes the two
  implications when they are trivial; a section's module that `H`'s procedures do not name is
  given (`RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f BlockSim`).
* The frames need the footprints of the first port's concrete modules (`@[fp_bound]` lemmas
  before the final section, each by `fp_module`).  Two traps: `omit [BlockSponge.Params]` on such
  a lemma makes `fp_module` fail on a procedure that calls another one (the first port's
  unfolding lemma takes the instance), and a bound stated after `include R` takes `R` as an
  argument and is not found.

## `Sponge_Raise_BlockSponge_f` in EC's form — the second tactic experiment

A procedure-level equivalence with two-sided loops, EC's `inline M.f`, `seq n m : P`, `rcondt{i}`,
`case`, `call (_ : ={glob Perm})` on a concrete module and `auto`, over the old port's
declarations (section `FirstPort` below).  It drove `stmt_inline (M.f)`
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

section FirstPort

/-!
## Declarations of the first port

Definitions and plain lemmas of the first port of this file (2026-10/11) that the proofs below
use; its program-logic proofs are gone.

The first port's translation notes (some mention declarations that went with its proofs):
* `clone include Indifferentiability with type p <- block * capacity, type f_in <- bool list *
  int, type f_out <- bool list rename … "Indif" as "Experiment" …` is the abbreviations below.
* `clone import IRO as BIRO with type from <- bool list, type to <- bool, op valid <-
  valid_toplevel, op dto <- dbool` is the namespace `BIRO`; EasyCrypt's unqualified `IRO` is
  `BIRO.IRO`.
* Procedures whose EasyCrypt parameters `(bs, n)` are the module type's single parameter take that
  pair and name its components, as in `BlockSponge`.  `HYBRID_IRO.f` is not a functionality: it
  keeps its two parameters.
* `LowerDist(D, F) = D(RaiseFun(F))` is used as `LowerDist(Dist) : BlockSponge.DISTINGUISHER`:
  `D` is a Lean parameter, and the alias is wrapped in a call (exception E5).  `RaiseSim(S, F) =
  S(LowerFun(F))` is the composite `Module.comp S LowerFun`.
* The abstract theory `HybridIRO` is the namespace `HybridIRO`.  Its modules' variables
  (`HybridIROLazy.mp`, `HybridIROEager.mp`) are lens parameters, as for every generic theory.
* Variables of *local* clones (`ERO` in `HybridIRO`, `HIRO` in the last section) are lens
  parameters of the local declarations that mention them, with hypotheses that they are fresh
  for the section's modules; the non-local results do not mention them (exception E6).
* EasyCrypt's `proc distinguish()` is a `RO_Distinguisher`, whose procedure takes `unit`; here
  `RODist`'s `distinguish` takes that `Unit` parameter.
-/

-- EasyCrypt names the module `Sponge` like its file (`Sponge.Sponge`); kept (exception E1)
set_option linter.dupNamespace false

namespace GaudisCrypt.SHA3.Sponge

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common

variable [SLCommon.Params] [BlockSponge.Params]

/-! ## Indifferentiability: `clone include Indifferentiability with type p <- block * capacity,
type f_in <- bool list * int, type f_out <- bool list rename [module] "Indif" as "Experiment"
[module] "GReal" as "RealIndif" [module] "GIdeal" as "IdealIndif"` -/

abbrev PRIMITIVE := Indifferentiability.PRIMITIVE (block × capacity) (List Bool × ℤ) (List Bool)
abbrev DPRIMITIVE := Indifferentiability.DPRIMITIVE (block × capacity) (List Bool × ℤ) (List Bool)
abbrev FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY (block × capacity) (List Bool × ℤ) (List Bool)
abbrev DFUNCTIONALITY :=
  Indifferentiability.DFUNCTIONALITY (block × capacity) (List Bool × ℤ) (List Bool)
abbrev CONSTRUCTION :=
  Indifferentiability.CONSTRUCTION (block × capacity) (List Bool × ℤ) (List Bool)
abbrev SIMULATOR := Indifferentiability.SIMULATOR (block × capacity) (List Bool × ℤ) (List Bool)
abbrev DISTINGUISHER :=
  Indifferentiability.DISTINGUISHER (block × capacity) (List Bool × ℤ) (List Bool)
noncomputable abbrev Experiment :=
  Indifferentiability.Indif (block × capacity) (List Bool × ℤ) (List Bool)
noncomputable abbrev RealIndif :=
  Indifferentiability.GReal (block × capacity) (List Bool × ℤ) (List Bool)
noncomputable abbrev IdealIndif :=
  Indifferentiability.GIdeal (block × capacity) (List Bool × ℤ) (List Bool)

/-- EC's subtyping `PRIMITIVE <: DPRIMITIVE` (its `f`, `fi`). -/
module_subtype PRIMITIVE <: DPRIMITIVE

/-- EC's subtyping `FUNCTIONALITY <: DFUNCTIONALITY` (its `f`). -/
module_subtype FUNCTIONALITY <: DFUNCTIONALITY

/-- `BlockSponge`'s `PRIMITIVE` where the bit sponge's `DPRIMITIVE` is expected (one module type in
EC: both are `Indifferentiability`'s at `block * capacity`). -/
module_subtype BlockSponge.PRIMITIVE <: DPRIMITIVE

/-! ## The ideal functionality: `clone import IRO as BIRO with type from <- bool list,
type to <- bool, op valid <- valid_toplevel, op dto <- dbool` -/

namespace BIRO
/-- `op valid <- valid_toplevel`, as a test. -/
def valid (bs : List Bool) : Bool := decide (valid_toplevel bs)
abbrev IRO_T := IRO.IRO_T Bool (List Bool)
/-- The clone's module variable `BIRO.IRO.mp`. -/
global_var IRO.mp : FMap (List Bool × ℤ) Bool
noncomputable abbrev IRO := IRO.IRO Bool (List Bool) valid dbool IRO.mp
noncomputable abbrev IRO.init := GaudisCrypt.SHA3.IRO.IRO.init Bool (List Bool) valid dbool IRO.mp
noncomputable abbrev IRO.fill_in :=
  GaudisCrypt.SHA3.IRO.IRO.fill_in Bool (List Bool) valid dbool IRO.mp
noncomputable abbrev IRO.f := GaudisCrypt.SHA3.IRO.IRO.f Bool (List Bool) valid dbool IRO.mp
/-- `BIRO.IRO` as the functionality it is used as (its procedures `init` and `f`). -/
noncomputable def IRO.asF : FUNCTIONALITY :=
  Indifferentiability.FUNCTIONALITY.mk (block × capacity) (List Bool × ℤ) (List Bool)
    { init := IRO.init, f := IRO.f }
end BIRO

/-! ## The sponge construction -/

module StdSponge using (P : DPRIMITIVE) {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, z : List Bool, sa : block, sc : capacity, finished : Bool,
      xs : List block;
    bs, n <- $x;
    z <- [];
    sa, sc <- (b0, Capacity.c0);
    finished <- false;
    xs <- pad2blocks $bs;
    -- absorption
    while (!(List.isEmpty $xs)) {
      sa, sc <- call P.f (($sa +^ head b0 $xs, $sc));
      xs <- behead $xs;
    }
    -- squeezing
    while (!$finished) {
      z <- $z ++ ofblock $sa;
      if (decide (size $z < $n)) {
        sa, sc <- call P.f (($sa, $sc));
      } else {
        finished <- true;
      }
    }
    return take $n $z
  };
}

module Sponge using (P : DPRIMITIVE) : FUNCTIONALITY {
  proc init () : Unit {
    return ()
  };
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, z : List Bool, sa : block, sc : capacity, i : ℤ, xs : List block;
    bs, n <- $x;
    z <- [];
    sa, sc <- (b0, Capacity.c0);
    i <- 0;
    xs <- pad2blocks $bs;
    -- absorption
    while (!(List.isEmpty $xs)) {
      sa, sc <- call P.f (($sa +^ head b0 $xs, $sc));
      xs <- behead $xs;
    }
    -- squeezing
    while ($i < ($n + r - 1) / r) {
      z <- $z ++ ofblock $sa;
      i <- $i + 1;
      if ($i < ($n + r - 1) / r) {
        sa, sc <- call P.f (($sa, $sc));
      }
    }
    return take $n $z
  };
}

theorem loop_cond (i n : ℤ) : 0 ≤ i → 0 ≤ n → (r * i < n ↔ i < (n + r - 1) / r) := by
  intro _ _
  have hr := gt0_r
  rw [← Int.add_one_le_iff (b := (n + r - 1) / r), Int.le_ediv_iff_mul_le hr]
  constructor <;> intro h <;> nlinarith

/-! ## Simulator and distinguisher constructions -/

module LowerFun using (F : DFUNCTIONALITY) : BlockSponge.DFUNCTIONALITY {
  proc f (x : List block × ℤ) : (List block) {
    var xs : List block, n : ℤ, cs : List Bool, obs : Option (List Bool), ys : List block;
    xs, n <- $x;
    ys <- [];
    obs <- unpad_blocks $xs;
    if (decide ($obs ≠ none)) {
      cs <- call F.f ((oget $obs, $n * r)); -- size cs = n * r
      ys <- bits2blocks $cs; -- size ys = n
    }
    return $ys
  };
}

module RaiseFun using (F : BlockSponge.DFUNCTIONALITY) : DFUNCTIONALITY {
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, xs : List block;
    bs, n <- $x;
    xs <- call F.f ((pad2blocks $bs, ($n + r - 1) / r));
    return take $n (blocks2bits $xs)
  };
}

-- EC's `LowerDist(D : DISTINGUISHER, F : BlockSponge.DFUNCTIONALITY) = D(RaiseFun(F))`, with `D`
-- a Lean parameter so that `LowerDist D` is a `BlockSponge.DISTINGUISHER`; the alias is wrapped
-- in a call (exception E5)
set_option linter.gaudisCrypt.using false in
module LowerDist (D : DISTINGUISHER)
    using (F : BlockSponge.DFUNCTIONALITY, P : BlockSponge.DPRIMITIVE) {
  proc distinguish () : Bool {
    var b : Bool;
    b <- call D(RaiseFun(F), P).distinguish ();
    return $b
  };
}

/-- `module RaiseSim (S : BlockSponge.SIMULATOR, F : DFUNCTIONALITY) = S(LowerFun(F))`, used as
`RaiseSim(S) : SIMULATOR`. -/
noncomputable def RaiseSim (S : BlockSponge.SIMULATOR) : SIMULATOR := Module.comp S LowerFun

/-! ## The abstract theory of hybrid IROs (`abstract theory HybridIRO`)

Hybrid IROs map a block list and an index to a bit.  The theory has no parameters and is cloned
once (`HIRO`, in the last section): its declarations are the clone's. -/

namespace HybridIRO

moduletype HYBRID_IRO {
  -- initialization
  proc init () -> Unit;
  -- hashing block lists, giving `n` bits
  proc f (x : List block, n : ℤ) -> (List Bool);
}

/-- `module type HYBRID_IRO_DIST (HI : HYBRID_IRO) = { proc distinguish() : bool {HI.f} }`:
distinguisher for hybrid IROs. -/
abbrev HYBRID_IRO_DIST := HYBRID_IRO →ₘ procmod () → Bool

/-- The oracle procedure a `HYBRID_IRO_DIST` may call (EasyCrypt's `{HI.f}`): `HI.f`.  The hole of
its representation (`Module.Representable`, exception E2). -/
abbrev HYBRID_IRO_DIST.holes : HoleSigs := .cons (procsig (List block, ℤ) -> (List Bool)) .empty

-- Experiments for hybrid IROs
module HybridIROExper using (HI : HYBRID_IRO, D : HYBRID_IRO_DIST) {
  proc main () : Bool {
    var b : Bool;
    _ <- call HI.init ();
    b <- call D(HI).distinguish ();
    return $b
  };
}

/-- EC's `HybridIROLazy.mp`. -/
global_var HybridIROLazy.mp : FMap (List block × ℤ) Bool

-- Lazy implementation of hybrid IROs (EC: `module HybridIROLazy : HYBRID_IRO`; it has more
-- procedures than `HYBRID_IRO`, so no type annotation: `HybridIROLazy.asHI` is its view)
module HybridIROLazy {
  proc init () : Unit {
    HybridIROLazy.mp <- (FMap.empty : FMap (List block × ℤ) Bool);
    return ()
  };
  proc fill_in (xs : List block, i : ℤ) : Bool {
    var r : Bool;
    if (!(decide (FMap.dom ($HybridIROLazy.mp : FMap (List block × ℤ) Bool) ($xs, $i)))) {
      r <$ dbool;
      HybridIROLazy.mp <- FMap.set $HybridIROLazy.mp ($xs, $i) $r;
    }
    return oget (FMap.get $HybridIROLazy.mp ($xs, $i))
  };
  proc f (xs : List block, n : ℤ) : (List Bool) {
    var b : Bool, bs : List Bool, i : ℤ;
    i <- 0;
    bs <- [];
    if (decide (valid_block $xs)) {
      while ($i < $n) {
        b <- call HybridIROLazy.fill_in ($xs, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    }
    return $bs
  };
}

/-- `HybridIROLazy` at its type `HYBRID_IRO`. -/
noncomputable def HybridIROLazy.asHI : HYBRID_IRO :=
  HYBRID_IRO.mk { init := HybridIROLazy.init, f := HybridIROLazy.f }

/-- EC's `HybridIROEager.mp`. -/
global_var HybridIROEager.mp : FMap (List block × ℤ) Bool

-- Eager implementation of hybrid IROs: the lazy one, except that `f` also fills in the bits up to
-- the next multiple of `r` (EC: `module HybridIROEager : HYBRID_IRO`; no type annotation, as for
-- `HybridIROLazy`)
module HybridIROEager {
  proc init () : Unit {
    HybridIROEager.mp <- (FMap.empty : FMap (List block × ℤ) Bool);
    return ()
  };
  proc fill_in (xs : List block, i : ℤ) : Bool {
    var r : Bool;
    if (!(decide (FMap.dom ($HybridIROEager.mp : FMap (List block × ℤ) Bool) ($xs, $i)))) {
      r <$ dbool;
      HybridIROEager.mp <- FMap.set $HybridIROEager.mp ($xs, $i) $r;
    }
    return oget (FMap.get $HybridIROEager.mp ($xs, $i))
  };
  proc f (xs : List block, n : ℤ) : (List Bool) {
    var b : Bool, bs : List Bool, m : ℤ, i : ℤ;
    m <- ($n + r - 1) / r * r; -- eager part
    i <- 0;
    bs <- [];
    if (decide (valid_block $xs)) {
      while ($i < $n) {
        b <- call HybridIROEager.fill_in ($xs, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
      while ($i < $m) { -- eager part
        _ <- call HybridIROEager.fill_in ($xs, $i);
        i <- $i + 1;
      }
    }
    return $bs
  };
}

/-- `HybridIROEager` at its type `HYBRID_IRO`. -/
noncomputable def HybridIROEager.asHI : HYBRID_IRO :=
  HYBRID_IRO.mk { init := HybridIROEager.init, f := HybridIROEager.f }

/-! ### Lazy = eager: EasyCrypt's section with `declare module D <: HYBRID_IRO_DIST
{-HybridIROEager, -HybridIROLazy}`

`local clone import PROM.FullRO as ERO with type in_t <- block list * int, type out_t <- bool,
op dout _ <- dbool, type d_in_t <- unit, type d_out_t <- bool`: the namespace `ERO` of
`PROM.FullRO` at the clone's types, its module variables `global_var`s. -/

namespace ERO
noncomputable abbrev dout : List block × ℤ → SubProbability Bool := fun _ => dbool
abbrev RO_T := PROM.FullRO.RO_T (List block × ℤ) Bool
abbrev RO_Distinguisher := PROM.FullRO.RO_Distinguisher (List block × ℤ) Bool Unit Bool
noncomputable abbrev RO_ext := PROM.FullRO.RO_ext (List block × ℤ) Bool
/-- The clone's module variable `ERO.RO.m`. -/
global_var RO.m : FMap (List block × ℤ) Bool
/-- The clone's module variable `ERO.FRO.m`. -/
global_var FRO.m : FMap (List block × ℤ) (Bool × flag)
noncomputable abbrev RO := PROM.FullRO.RO.asRO (List block × ℤ) Bool dout RO.m
noncomputable abbrev LRO := PROM.FullRO.LRO (List block × ℤ) Bool dout RO.m
end ERO

section LazyEager

module EROExper using (O : ERO.RO_T, D : ERO.RO_Distinguisher) {
  proc main () : Bool {
    var b : Bool;
    _ <- call O.init ();
    b <- call D(O).distinguish (());
    return $b
  };
}

-- Make a hybrid IRO out of a random oracle (EC's local `HIRO(RO : ERO.RO) : HYBRID_IRO`)
module HIRO using (RO : ERO.RO_T) : HYBRID_IRO {
  proc init () : Unit {
    _ <- call RO.init ();
    return ()
  };
  proc f (xs : List block, n : ℤ) : (List Bool) {
    var b : Bool, bs : List Bool, m : ℤ, i : ℤ;
    m <- ($n + r - 1) / r * r;
    i <- 0;
    bs <- [];
    if (decide (valid_block $xs)) {
      while ($i < $n) {
        b <- call RO.get (($xs, $i));
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
      while ($i < $m) {
        _ <- call RO.sample (($xs, $i));
        i <- $i + 1;
      }
    }
    return $bs
  };
}

-- Make a distinguisher for random oracles out of `HIRO` and `D` (EC's local `RODist(RO : ERO.RO)`,
-- with the section's `D` a Lean parameter; its `distinguish` takes `RO_Distinguisher`'s `unit`)
set_option linter.gaudisCrypt.using false in
module RODist (D : HYBRID_IRO_DIST) using (RO : ERO.RO_T) {
  proc distinguish (_x : Unit) : Bool {
    var b : Bool;
    b <- call (Module.app D (Module.app HIRO RO)) ();
    return $b
  };
}

local notation "E" => FVP.fvpInductiveFunctionGS.evalMexpr

omit [BlockSponge.Params] in
/-- `HIRO` has no globals of its own. -/
theorem fvP_HIRO : FVP.fvP HIRO = ⊥ := by
  refine le_antisymm ?_ bot_le
  show E HIRO.expression ≤ ⊥
  unfold HIRO
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_pair, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  refine sup_le ?_ ?_
  · unfold HIRO.init
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_var,
      evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)
  · unfold HIRO.f
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_snd,
      evalMexpr_var, evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)

/-- `RODist(D)` touches what `D` does. -/
theorem fvP_RODist_le (D : HYBRID_IRO_DIST) : FVP.fvP (RODist D) ≤ FVP.fvP D := by
  show E (RODist D).expression ≤ E D.expression
  unfold RODist
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  unfold RODist.distinguish
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_var, evalMexpr_unit,
    sup_bot_eq]
  refine sup_le ((evalMexpr_procWithHoles_le _).trans
    (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)) (sup_le le_rfl ?_)
  exact (show E HIRO.expression = ⊥ from fvP_HIRO).le.trans bot_le

end LazyEager

section Hybrid

-- Turn a hybrid IRO implementation (lazy or eager) into the top-level ideal functionality
module RaiseHybridIRO using (HI : HYBRID_IRO) : FUNCTIONALITY {
  proc init () : Unit {
    _ <- call HI.init ();
    return ()
  };
  proc f (x : List Bool × ℤ) : (List Bool) {
    var bs : List Bool, n : ℤ, cs : List Bool;
    bs, n <- $x;
    cs <- call HI.f (pad2blocks $bs, $n);
    return $cs
  };
}

-- Turn a hybrid IRO implementation (lazy or eager) into the lower-level ideal distinguisher
-- functionality
module LowerHybridIRO using (HI : HYBRID_IRO) : BlockSponge.DFUNCTIONALITY {
  proc f (x : List block × ℤ) : (List block) {
    var xs : List block, n : ℤ, bs : List Bool, ys : List block;
    xs, n <- $x;
    bs <- call HI.f ($xs, $n * r);
    ys <- bits2blocks $bs;
    return $ys
  };
}

/-- Invariant relating the maps of `BIRO.IRO` and `HybridIROLazy`. -/
def lazy_invar (mp1 : FMap (List Bool × ℤ) Bool) (mp2 : FMap (List block × ℤ) Bool) : Prop :=
  (∀ (bs : List Bool) (n : ℤ), FMap.dom mp1 (bs, n) ↔ FMap.dom mp2 (pad2blocks bs, n)) ∧
  (∀ (xs : List block) (n : ℤ), FMap.dom mp2 (xs, n) → valid_block xs) ∧
  (∀ (bs : List Bool) (n : ℤ), FMap.dom mp1 (bs, n) →
    oget (FMap.get mp1 (bs, n)) = oget (FMap.get mp2 (pad2blocks bs, n)))

theorem lazy_invar0 : lazy_invar FMap.empty FMap.empty :=
  ⟨fun _ _ => iff_of_false (FMap.mem_empty _) (FMap.mem_empty _),
    fun _ _ h => absurd h (FMap.mem_empty _), fun _ _ h => absurd h (FMap.mem_empty _)⟩

theorem lazy_invar_mem_pad2blocks_l2r (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (i : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp1 (bs, i) → FMap.dom mp2 (pad2blocks bs, i) :=
  fun li h => (li.1 bs i).mp h

theorem lazy_invar_mem_pad2blocks_r2l (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (i : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp2 (pad2blocks bs, i) → FMap.dom mp1 (bs, i) :=
  fun li h => (li.1 bs i).mpr h

theorem lazy_invar_vb (mp1 : FMap (List Bool × ℤ) Bool) (mp2 : FMap (List block × ℤ) Bool)
    (xs : List block) (n : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp2 (xs, n) → valid_block xs :=
  fun li h => li.2.1 xs n h

theorem lazy_invar_lookup_eq (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (n : ℤ) :
    lazy_invar mp1 mp2 → FMap.dom mp1 (bs, n) →
    oget (FMap.get mp1 (bs, n)) = oget (FMap.get mp2 (pad2blocks bs, n)) :=
  fun li h => li.2.2 bs n h

theorem lazy_invar_upd_mem_dom_iff (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs cs : List Bool) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 →
    (FMap.dom (FMap.set mp1 (bs, n) b) (cs, m) ↔
      FMap.dom (FMap.set mp2 (pad2blocks bs, n) b) (pad2blocks cs, m)) := by
  intro li
  rw [FMap.mem_set, FMap.mem_set, li.1 cs m]
  simp only [Prod.mk.injEq]
  constructor
  · rintro (h | ⟨rfl, rfl⟩) <;> simp_all
  · rintro (h | ⟨h1, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨pad2blocks_inj h1, rfl⟩

theorem lazy_invar_upd2_vb (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs : List Bool) (xs : List block) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 → FMap.dom (FMap.set mp2 (pad2blocks bs, n) b) (xs, m) →
    valid_block xs := by
  intro li h
  rcases (FMap.mem_set _ _ _ _).mp h with h | h
  · exact li.2.1 xs m h
  · simp only [Prod.mk.injEq] at h
    rw [h.1]; exact valid_pad2blocks bs

theorem lazy_invar_upd_lu_eq (mp1 : FMap (List Bool × ℤ) Bool)
    (mp2 : FMap (List block × ℤ) Bool) (bs cs : List Bool) (n m : ℤ) (b : Bool) :
    lazy_invar mp1 mp2 → FMap.dom (FMap.set mp1 (bs, n) b) (cs, m) →
    oget (FMap.get (FMap.set mp1 (bs, n) b) (cs, m)) =
      oget (FMap.get (FMap.set mp2 (pad2blocks bs, n) b) (pad2blocks cs, m)) := by
  intro li h
  rw [FMap.get_setE, FMap.get_setE]
  by_cases hc : (cs, m) = (bs, n)
  · simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp
  · have hp : (pad2blocks cs, m) ≠ (pad2blocks bs, n) := fun h' => hc (by
      simp only [Prod.mk.injEq] at h' ⊢; exact ⟨pad2blocks_inj h'.1, h'.2⟩)
    rw [if_neg hc, if_neg hp]
    rcases (FMap.mem_set _ _ _ _).mp h with h | h
    · exact li.2.2 cs m h
    · exact absurd h hc

/-- Invariant relating the maps of `BlockSponge.BIRO.IRO` and `HybridIROEager`. -/
def eager_invar (mp1 : FMap (List block × ℤ) block) (mp2 : FMap (List block × ℤ) Bool) : Prop :=
  (∀ (xs : List block) (i : ℤ), FMap.dom mp1 (xs, i) →
    0 ≤ i ∧
    ∀ (j : ℤ), i * r ≤ j ∧ j < (i + 1) * r →
      FMap.get mp2 (xs, j) = some (nth false (ofblock (oget (FMap.get mp1 (xs, i)))) (j - i * r))) ∧
  (∀ (xs : List block) (j : ℤ), FMap.dom mp2 (xs, j) → FMap.dom mp1 (xs, j / r))

def block_bits_all_in_dom (xs : List block) (i : ℤ) (mp : FMap (List block × ℤ) Bool) : Prop :=
  ∀ (j : ℤ), i ≤ j ∧ j < i + r → FMap.dom mp (xs, j)

def block_bits_all_out_dom (xs : List block) (i : ℤ) (mp : FMap (List block × ℤ) Bool) : Prop :=
  ∀ (j : ℤ), i ≤ j ∧ j < i + r → ¬ FMap.dom mp (xs, j)

def block_bits_dom_all_in_or_out (xs : List block) (i : ℤ) (mp : FMap (List block × ℤ) Bool) :
    Prop :=
  block_bits_all_in_dom xs i mp ∨ block_bits_all_out_dom xs i mp

omit [BlockSponge.Params] in
/-- `j / r = i` for `j` in the `i`th block of bits.  Not an EC lemma (EC: `divzDl`,
`divz_small`). -/
theorem div_r_eq {i j : ℤ} (h1 : i * r ≤ j) (h2 : j < (i + 1) * r) : j / r = i := by
  have hr := gt0_r
  have a := (Int.le_ediv_iff_mul_le hr).mpr h1
  have b := (Int.ediv_lt_iff_lt_mul hr).mpr h2
  omega

theorem eager_inv_mem_mp1_ge0 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp1 (xs, i) → 0 ≤ i :=
  fun ei h => (ei.1 xs i h).1

theorem eager_inv_mem_mp2_ge0 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (j : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp2 (xs, j) → 0 ≤ j := by
  intro ei h
  have := (ei.1 xs (j / r) (ei.2 xs j h)).1
  simpa using (Int.le_ediv_iff_mul_le gt0_r).mp this

theorem eager_invar0 : eager_invar FMap.empty FMap.empty :=
  ⟨fun _ _ h => absurd h (FMap.mem_empty _), fun _ _ h => absurd h (FMap.mem_empty _)⟩

theorem eager_inv_imp_block_bits_dom (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    0 ≤ i → r ∣ i → eager_invar mp1 mp2 → block_bits_dom_all_in_or_out xs i mp2 := by
  intro _ hdvd ei
  obtain ⟨k, rfl⟩ := hdvd
  rw [mul_comm]
  by_cases h : FMap.dom mp1 (xs, k)
  · left
    intro j hj
    rw [FMap.domE, (ei.1 xs k h).2 j ⟨hj.1, by nlinarith [hj.2]⟩]
    simp
  · right
    intro j hj hd
    have := ei.2 xs j hd
    rw [div_r_eq hj.1 (by nlinarith [hj.2])] at this
    exact h this

theorem eager_inv_mem_dom1 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → FMap.dom mp1 (xs, i) → block_bits_all_in_dom xs (i * r) mp2 := by
  intro ei h j hj
  rw [FMap.domE, (ei.1 xs i h).2 j ⟨hj.1, by nlinarith [hj.2]⟩]
  simp

theorem eager_inv_not_mem_dom1 (mp1 : FMap (List block × ℤ) block)
    (mp2 : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) :
    eager_invar mp1 mp2 → 0 ≤ i → ¬ FMap.dom mp1 (xs, i) →
    block_bits_all_out_dom xs (i * r) mp2 := by
  intro ei _ h j hj hd
  have := ei.2 xs j hd
  rw [div_r_eq hj.1 (by nlinarith [hj.2])] at this
  exact h this

theorem block_bits_dom_first_in_imp_all_in (xs : List block) (i : ℤ)
    (mp : FMap (List block × ℤ) Bool) :
    block_bits_dom_all_in_or_out xs i mp → FMap.dom mp (xs, i) →
    block_bits_all_in_dom xs i mp := by
  rintro (h | h) hd
  · exact h
  · exact absurd hd (h i ⟨le_rfl, by have := gt0_r; omega⟩)

theorem block_bits_dom_first_out_imp_all_out (xs : List block) (i : ℤ)
    (mp : FMap (List block × ℤ) Bool) :
    block_bits_dom_all_in_or_out xs i mp → ¬ FMap.dom mp (xs, i) →
    block_bits_all_out_dom xs i mp := by
  rintro (h | h) hd
  · exact absurd (h i ⟨le_rfl, by have := gt0_r; omega⟩) hd
  · exact h

-- Module needed for applying the transitivity tactic in connection with `HybridIROEager`
module HybridIROEagerTrans {
  -- getting the next block of bits; assuming `m = i + r` and `size bs = i`
  proc next_block (xs : List block, i : ℤ, m : ℤ, bs : List Bool) : (List Bool × ℤ) {
    var b : Bool;
    while ($i < $m) {
      b <- call HybridIROEager.fill_in ($xs, $i);
      bs <- rcons $bs $b;
      i <- $i + 1;
    }
    return ($bs, $i)
  };
  -- `next_block` split into cases; assuming `m = i + r`, `size bs = i` and
  -- `block_bits_dom_all_in_or_out xs i HybridIROEager.mp`
  proc next_block_split (xs : List block, i : ℤ, m : ℤ, bs : List Bool) : (List Bool × ℤ) {
    var b : Bool, j : ℤ, cs : List Bool;
    if (decide (FMap.dom ($HybridIROEager.mp : FMap (List block × ℤ) Bool) ($xs, $i))) {
      while ($i < $m) {
        b <- oget (FMap.get ($HybridIROEager.mp : FMap (List block × ℤ) Bool) ($xs, $i));
        bs <- rcons $bs $b;
        i <- $i + 1;
      }
    } else {
      j <- 0;
      cs <- [];
      while ($j < r) {
        b <$ dbool;
        cs <- rcons $cs $b;
        j <- $j + 1;
      }
      bs <- $bs ++ $cs;
      while ($i < $m) {
        HybridIROEager.mp <- FMap.set $HybridIROEager.mp ($xs, $i) (nth true $bs $i);
        i <- $i + 1;
      }
    }
    return ($bs, $i)
  };
  -- loop getting `n * r` bits of hash
  proc loop (n : ℤ, xs : List block) : (ℤ × List Bool) {
    var b : Bool, i : ℤ, bs : List Bool;
    i <- 0;
    bs <- [];
    while ($i < $n * r) {
      b <- call HybridIROEager.fill_in ($xs, $i);
      bs <- rcons $bs $b;
      i <- $i + 1;
    }
    return ($i, $bs)
  };
}

/-- Two maps are the same except (perhaps) on a range of bits for a single block list. -/
def eager_eq_except (xs : List block) (i j : ℤ) (mp1 mp2 : FMap (List block × ℤ) Bool) : Prop :=
  ∀ (ys : List block) (k : ℤ), ys ≠ xs ∨ k < i ∨ j ≤ k → FMap.get mp1 (ys, k) = FMap.get mp2 (ys, k)

theorem eager_eq_except_mem_iff (xs ys : List block) (i j k : ℤ)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → ys ≠ xs ∨ k < i ∨ j ≤ k →
    (FMap.dom mp1 (ys, k) ↔ FMap.dom mp2 (ys, k)) := by
  intro h hk
  rw [FMap.domE, FMap.domE, h ys k hk]

theorem eager_eq_except_upd1_eq_in (xs : List block) (i j k : ℤ) (y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → i ≤ k → k < j →
    eager_eq_except xs i j (FMap.set mp1 (xs, k) y) mp2 := by
  intro h hik hkj ys l hl
  rw [FMap.get_setE,
    if_neg (by rintro ⟨⟩; rcases hl with h' | h' | h' <;> first | exact h' rfl | omega),
    h ys l hl]

theorem eager_eq_except_upd2_eq_in (xs : List block) (i j k : ℤ) (y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    eager_eq_except xs i j mp1 mp2 → i ≤ k → k < j →
    eager_eq_except xs i j mp1 (FMap.set mp2 (xs, k) y) := by
  intro h hik hkj ys l hl
  rw [FMap.get_setE,
    if_neg (by rintro ⟨⟩; rcases hl with h' | h' | h' <;> first | exact h' rfl | omega),
    h ys l hl]

theorem eager_eq_except_maps_eq (xs : List block) (i j : ℤ) (_y : Bool)
    (mp1 mp2 : FMap (List block × ℤ) Bool) :
    i ≤ j → eager_eq_except xs i j mp1 mp2 →
    (∀ (k : ℤ), i ≤ k ∧ k < j → FMap.get mp1 (xs, k) = FMap.get mp2 (xs, k)) → mp1 = mp2 := by
  intro _ h hr
  refine (FMap.fmap_eqP _ _).mp fun ⟨ys, k⟩ => ?_
  by_cases hys : ys = xs
  · subst hys
    by_cases hk : i ≤ k ∧ k < j
    · exact hr k hk
    · exact h ys k (Or.inr (by omega))
  · exact h ys k (Or.inl hys)

theorem eager_invar_eq_except_upd1 (mp1 : FMap (List block × ℤ) block)
    (mp2 mp2' : FMap (List block × ℤ) Bool) (xs : List block) (i : ℤ) (y : block) :
    0 ≤ i → eager_invar mp1 mp2 → eager_eq_except xs (i * r) ((i + 1) * r) mp2 mp2' →
    (∀ (j : ℤ), i * r ≤ j ∧ j < (i + 1) * r →
      FMap.get mp2' (xs, j) = some (nth false (ofblock y) (j - i * r))) →
    eager_invar (FMap.set mp1 (xs, i) y) mp2' := by
  intro hi ei ee hran
  have hr := gt0_r
  refine ⟨fun ys k hd => ?_, fun ys j hd => ?_⟩
  · by_cases hyk : (ys, k) = (xs, i)
    · simp only [Prod.mk.injEq] at hyk
      obtain ⟨rfl, rfl⟩ := hyk
      refine ⟨hi, fun j hj => ?_⟩
      rw [FMap.get_set_sameE]
      exact hran j hj
    · have hd1 : FMap.dom mp1 (ys, k) := ((FMap.mem_set _ _ _ _).mp hd).resolve_right hyk
      obtain ⟨hk, hb⟩ := ei.1 ys k hd1
      refine ⟨hk, fun j hj => ?_⟩
      rw [FMap.get_setE, if_neg hyk, ← hb j hj]
      refine (ee ys j ?_).symm
      by_cases hys : ys = xs
      · subst hys
        have hki : k ≠ i := fun h => hyk (by rw [h])
        rcases lt_or_gt_of_ne hki with hlt | hgt
        · exact Or.inr (Or.inl (by nlinarith [hj.2]))
        · exact Or.inr (Or.inr (by nlinarith [hj.1]))
      · exact Or.inl hys
  · rw [FMap.mem_set]
    by_cases hex : ys ≠ xs ∨ j < i * r ∨ (i + 1) * r ≤ j
    · left
      apply ei.2
      rw [FMap.domE] at hd ⊢
      rwa [ee ys j hex]
    · right
      simp only [ne_eq, not_or, not_not, not_lt] at hex
      obtain ⟨rfl, h1, h2⟩ := hex
      rw [div_r_eq h1 (by omega)]

-- Module needed for applying the transitivity tactic in connection with `BlockSponge.BIRO.IRO`
module BlockSpongeTrans {
  -- getting the next block; assumes `size bs = i`
  proc next_block (x : List block, i : ℤ, bs : List block) : (List block × ℤ) {
    var b : block;
    b <- call BlockSponge.BIRO.IRO.fill_in ($x, $i);
    bs <- rcons $bs $b;
    i <- $i + 1;
    return ($bs, $i)
  };
  -- loop getting `n` blocks
  proc loop (n : ℤ, xs : List block) : (ℤ × List block) {
    var b : block, i : ℤ, bs : List block;
    i <- 0;
    bs <- [];
    while ($i < $n) {
      b <- call BlockSponge.BIRO.IRO.fill_in ($xs, $i);
      bs <- rcons $bs $b;
      i <- $i + 1;
    }
    return ($i, $bs)
  };
}

/-! `clone Program as Prog with type t = bool, op d = {0,1}` (the `Program` abstract theory of
`DList`) -/

namespace Prog
noncomputable abbrev LoopSnoc.sample := DList.Program.LoopSnoc.sample Bool dbool
end Prog

theorem PrLoopSnoc_sample (m : VariableAssignment) (bs : List Bool) :
    (Procedure.Pr Prog.LoopSnoc.sample.procedure r m (fun res _ => res = bs) : ENNReal) =
      (dlist dbool r).1 {bs} :=
  -- EC: `Sample_LoopSnoc_eq` then `pr_Sample`, together `LoopSnoc.pr_sample`
  DList.Program.LoopSnoc.pr_sample Bool dbool r m bs

theorem iter_mul_one_half_pos (n : ℤ) :
    0 < n → iter n ((1 / 2 : ℝ) * ·) 1 = (((2 ^ n.toNat : ℤ) : ℝ))⁻¹ := by
  intro _
  have h : ∀ k : ℕ, ((1 / 2 : ℝ) * ·)^[k] 1 = ((2 : ℝ) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ]; field_simp
  simp only [iter, h]
  push_cast
  rfl

-- Module for adapting `PrLoopSnoc_sample` to block generation
module BlockGen {
  proc loop () : block {
    var b : Bool, j : ℤ, cs : List Bool;
    j <- 0;
    cs <- [];
    while ($j < r) {
      b <$ dbool;
      cs <- rcons $cs $b;
      j <- $j + 1;
    }
    return mkblock $cs
  };
  proc direct () : block {
    var w : block;
    w <$ bdistr;
    return $w
  };
}

end Hybrid

end HybridIRO

/-! ## The main result: EasyCrypt's section with `declare module BlockSim <: BlockSponge.SIMULATOR
{-IRO, -BlockSponge.BIRO.IRO}` and `declare module Dist <: DISTINGUISHER {-Perm, -BlockSim, -IRO,
-BlockSponge.BIRO.IRO}`

`local clone HybridIRO as HIRO`: the clone is local, so its module variables
`HIRO.HybridIROLazy.mp`, `HIRO.HybridIROEager.mp` are the lens parameters `HIRO_Lazy_mp`,
`HIRO_Eager_mp` of the local declarations that mention them, fresh by hypothesis (`HIRO_fresh`,
exception E6).  `HIRO.X` is `HybridIRO.X` at these lenses. -/

section Main

/-! ### The ideal side -/

-- Make a hybrid IRO distinguisher from `BlockSim` and `Dist` (`HI.f` is used by `BlockSim`, and
-- by `HIRO.RaiseHybridIRO`; `HI.init` is unused).  EC's local
-- `(HybridIRODist : HIRO.HYBRID_IRO_DIST) (HI : HIRO.HYBRID_IRO)`, with the section's `BlockSim`,
-- `Dist` Lean parameters.
set_option linter.gaudisCrypt.using false in
module HybridIRODist (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER)
    using (HI : HybridIRO.HYBRID_IRO) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call BlockSim(HybridIRO.LowerHybridIRO(HI)).init ();
    b <- call Dist(HybridIRO.RaiseHybridIRO(HI),
      BlockSim(HybridIRO.LowerHybridIRO(HI))).distinguish ();
    return $b
  };
}

local notation "E" => FVP.fvpInductiveFunctionGS.evalMexpr

omit [BlockSponge.Params] in
/-- `LowerHybridIRO` has no globals of its own. -/
theorem fvP_LowerHybridIRO : FVP.fvP HybridIRO.LowerHybridIRO = ⊥ := by
  refine le_antisymm ?_ bot_le
  show E HybridIRO.LowerHybridIRO.expression ≤ ⊥
  unfold HybridIRO.LowerHybridIRO
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  unfold HybridIRO.LowerHybridIRO.f
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_snd, evalMexpr_var,
    evalMexpr_unit, sup_bot_eq]
  exact (evalMexpr_procWithHoles_le _).trans
    (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)

omit [BlockSponge.Params] in
/-- `RaiseHybridIRO` has no globals of its own. -/
theorem fvP_RaiseHybridIRO : FVP.fvP HybridIRO.RaiseHybridIRO = ⊥ := by
  refine le_antisymm ?_ bot_le
  show E HybridIRO.RaiseHybridIRO.expression ≤ ⊥
  unfold HybridIRO.RaiseHybridIRO
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs]
  refine sup_le ?_ ?_
  · unfold HybridIRO.RaiseHybridIRO.init
    show E (ModuleExpression.app _ _) ≤ ⊥
    simp only [evalMexpr_app, evalMexpr_var, sup_bot_eq]
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_var,
      evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)
  · unfold HybridIRO.RaiseHybridIRO.f
    show E (ModuleExpression.app _ _) ≤ ⊥
    simp only [evalMexpr_app, evalMexpr_var, sup_bot_eq]
    refine (evalMexpr_toModule_le _ _).trans ?_
    simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_snd, evalMexpr_var,
      evalMexpr_unit, sup_bot_eq]
    exact (evalMexpr_procWithHoles_le _).trans
      (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)

/-- `HybridIRODist` touches what `BlockSim` and `Dist` do. -/
theorem fvP_HybridIRODist_le (BlockSim : BlockSponge.SIMULATOR) (Dist : DISTINGUISHER) :
    FVP.fvP (HybridIRODist BlockSim Dist) ≤ FVP.fvP BlockSim ⊔ FVP.fvP Dist := by
  show E (HybridIRODist BlockSim Dist).expression ≤ E BlockSim.expression ⊔ E Dist.expression
  unfold HybridIRODist
  refine (evalMexpr_toModule_le _ _).trans ?_
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_var, sup_bot_eq]
  unfold HybridIRODist.distinguish
  refine (evalMexpr_toModule_le _ _).trans ?_
  have hL : E HybridIRO.LowerHybridIRO.expression = ⊥ := fvP_LowerHybridIRO
  have hR : E HybridIRO.RaiseHybridIRO.expression = ⊥ := fvP_RaiseHybridIRO
  simp only [evalMexpr_abs, evalMexpr_app, evalMexpr_pair, evalMexpr_fst, evalMexpr_snd,
    evalMexpr_var, evalMexpr_unit, sup_bot_eq, hL, hR]
  refine sup_le ((evalMexpr_procWithHoles_le _).trans
    (FVP.fvP_proc_le_of_localsOnly _ (by locals_only) (by locals_only) _)) ?_
  exact sup_le le_sup_left (sup_le le_sup_right (sup_le bot_le (sup_le le_sup_left le_sup_left)))

end Main

end GaudisCrypt.SHA3.Sponge

end FirstPort

-- strict mode: a tactic fallback is an error (`notes/SHA3/TacticReview.md`, step 3)
set_option ec.strict true

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
    stmt_rcondf{1} 3; on_goals 1 => (intro σ₂; ec_auto)
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

export GaudisCrypt.SHA3.Sponge.HybridIRO (HybridIROLazy.mp HybridIROEager.mp)

/-- EC's `HybridIROLazy`, at its type `HYBRID_IRO`. -/
noncomputable abbrev HybridIROLazy : HYBRID_IRO :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROLazy.asHI
-- (`init` and `f` as the module type's procedures of `HybridIROLazy`: the form in which a call
-- of an oracle `HI.f` names them)
noncomputable abbrev HybridIROLazy.init := HYBRID_IRO.init HybridIROLazy
noncomputable abbrev HybridIROLazy.f := HYBRID_IRO.f HybridIROLazy
noncomputable abbrev HybridIROLazy.fill_in :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROLazy.fill_in

/-- EC's `HybridIROEager`, at its type `HYBRID_IRO`. -/
noncomputable abbrev HybridIROEager : HYBRID_IRO :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEager.asHI
noncomputable abbrev HybridIROEager.init := HYBRID_IRO.init HybridIROEager
noncomputable abbrev HybridIROEager.f := HYBRID_IRO.f HybridIROEager
noncomputable abbrev HybridIROEager.fill_in :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEager.fill_in

/-! EC's `local clone import PROM.FullRO as ERO with type in_t <- block list * int,
type out_t <- bool, op dout _ <- dbool, type d_in_t <- unit, type d_out_t <- bool`: the namespace
`ERO` of the section `FirstPort`. -/

namespace ERO
export GaudisCrypt.SHA3.Sponge.HybridIRO.ERO (dout RO_T RO_Distinguisher RO.m FRO.m RO LRO)
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
  equiv_call (PROM.FullRO.FullEager.RO_LRO_D (List block × ℤ) Bool ERO.dout ERO.FRO.m
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
  --     (GAP 14 of `SmartCounter/Gconcl_list.lean`: `glob D` past the initialization)
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

The module is declared in the section `FirstPort`. -/

noncomputable abbrev HybridIROEagerTrans.next_block :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEagerTrans.next_block
noncomputable abbrev HybridIROEagerTrans.next_block_split :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEagerTrans.next_block_split
noncomputable abbrev HybridIROEagerTrans.loop :=
  GaudisCrypt.SHA3.Sponge.HybridIRO.HybridIROEagerTrans.loop

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

EC l. 1188–1282 (`BlockSpongeTrans`, `Prog`, `PrLoopSnoc_sample`, `iter_mul_one_half_pos`,
`BlockGen`) are the first port's. -/

open GaudisCrypt.SHA3.Sponge.HybridIRO (eager_inv_imp_block_bits_dom eager_inv_mem_dom1
  eager_inv_not_mem_dom1 eager_invar_eq_except_upd1 BlockSpongeTrans BlockGen PrLoopSnoc_sample)

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
(EC l. 1269). -/
theorem BlockGen_loop_direct :
    equiv[ BlockGen.loop ~ BlockGen.direct : True ==> ={res} ] := by
  -- EC: bypr res{1} res{2}=> // &1 &2 w.
  --     (`w` is `w0`: `BlockGen.direct` has a local `w`, which a tactic's argument would read)
  bypr (res{1}) (res{2})
  intro a1 m1 a2 m2 w0 _
  -- EC: have -> : Pr[BlockGen.direct() @ &2 : res = w] = 1%r / (2 ^ r)%r.
  have h2 : Pr[ BlockGen.direct () @ &m2 : §res = w0 ] = 1 / 2 ^ r.toNat := by
    -- EC: byphoare=> //.
    --     proc; rnd; skip; progress.
    byphoare (: True ==> _)
    phoare_proc; phoare_rnd (pred1 w0); phoare_auto
    -- EC: rewrite DBlock.dunifinE.
    --     have -> : (transpose (=) w) = (pred1 w) by rewrite /pred1.
    --     by rewrite DBlock.Support.enum_spec block_card.
    refine ⟨?_, fun v _ => pred1E w0 v⟩
    rw [mu_pred1, mu1, bdistr]
    erw [BitWord.dunifin1E]
    simp
  -- EC: have -> :
  --       Pr[BlockGen.loop() @ &1 : res = w] =
  --       Pr[Prog.LoopSnoc.sample(r) @ &1 : res = ofblock w].
  have h1 : Pr[ BlockGen.loop () @ &m1 : §res = w0 ] =
      Pr[ HybridIRO.Prog.LoopSnoc.sample (r) @ &m1 : §res = ofblock w0 ] := by
    -- EC: byequiv=> //; proc.
    byequiv
    equiv_proc
    -- EC: seq 2 2 :
    --       (r = n{2} /\ j{1} = i{2} /\ j{1} = 0 /\
    --        cs{1} = l{2} /\ cs{1} = []);
    --       first auto.
    equiv_seq 2 2 : (r = §n{2} ∧ §j{1} = §i{2} ∧ §j{1} = 0 ∧ §cs{1} = §l{2} ∧ §cs{1} = [])
    · equiv_auto
    -- EC: while
    --       (r = n{2} /\ j{1} = i{2} /\ cs{1} = l{2} /\ j{1} <= r /\
    --        size cs{1} = j{1}).
    equiv_while (r = §n{2} ∧ §j{1} = §i{2} ∧ §cs{1} = §l{2} ∧ §j{1} ≤ r ∧ size §cs{1} = §j{1})
    -- EC: wp; rnd; skip.
    --     progress; smt(cats1 gt0_r size_rcons).
    · stmt_wp; equiv_rnd; equiv_skip
      intro j₁ cs₁ n₂ i₂ l₂ ⟨⟨hn, hj, hcs, hle, hsz⟩, hlt, _⟩ a _
      subst hn hj hcs
      simp only [decide_eq_true_eq] at hlt
      have : size (rcons cs₁ a) = size cs₁ + 1 := by simp [size, rcons]
      exact ⟨⟨rfl, rfl, by simp [rcons], by omega, by omega⟩, rfl⟩
    -- EC: skip=> &m1 &m2 [# <- <- -> <- ->].
    --     split; first smt(gt0_r).
    --     move=> cs j i ds not_lt_jr not_lt_ir [# _ eq_ji -> le_jr sz_cs_eq_j].
    --     have sz_ds_eq_r : size ds = r by smt().
    --     progress; [by rewrite ofblockK | by rewrite mkblockK].
    · equiv_skip
      intro j₁ cs₁ l₁ n₂ i₂ l₂ cs₂ ⟨hn, hj, hj0, hcs, hcs0⟩
      subst hn hj hcs hcs0 hj0
      refine ⟨⟨⟨rfl, rfl, rfl, gt0_r.le, by simp [size]⟩, rfl⟩, fun τ₁ τ₂ _ _ hI hg₁ _ => ?_⟩
      obtain ⟨-, -, hcs, hle, hsz⟩ := hI
      --     (GAP 10: the invariant's reads restated at the plain lenses for `omega`, `rw`)
      have hcs' : (localVarLens "cs" (List Bool)).get τ₁ = (localVarLens "l" (List Bool)).get τ₂ :=
        hcs
      have hsz' : size ((localVarLens "cs" (List Bool)).get τ₁) = r := by
        have : size ((localVarLens "cs" (List Bool)).get τ₁) = (localVarLens "j" ℤ).get τ₁ := hsz
        have : ¬ (localVarLens "j" ℤ).get τ₁ < r := of_decide_eq_false hg₁
        have : (localVarLens "j" ℤ).get τ₁ ≤ r := hle
        omega
      rw [← hcs']
      exact ⟨by rintro rfl; rw [ofblockK _ hsz'], by intro h; rw [h, mkblockK]⟩
  -- EC: rewrite (PrLoopSnoc_sample &1 (ofblock w)).
  --     rewrite dlist1E 1:ge0_r size_block /=.
  --     have -> :
  --       (fun (x : bool) => mu1 {0,1} x) =
  --       (fun (x : bool) => 1%r / 2%r).
  --     apply fun_ext=> x; by rewrite dbool1E.
  --     by rewrite Bigreal.BRM.big_const count_predT size_block
  --                iter_mul_one_half_pos 1:gt0_r.
  cases a1; cases a2
  refine (?_ : _ = (1 / 2 ^ r.toNat : ℝ)).trans h2.symm
  refine h1.trans ?_
  have hl := PrLoopSnoc_sample m1 (ofblock w0)
  have hlen : ((ofblock w0).length : ℤ) = r := by
    have := BitWord.size_word gt0_r.le w0
    simpa [size, ofblock] using this
  rw [dlist1E _ _ _ hlen] at hl
  simp only [dbool1E, List.map_const', List.prod_replicate] at hl
  have := congrArg ENNReal.toReal hl
  rw [ENNReal.coe_toReal] at this
  refine this.trans ?_
  rw [show (ofblock w0).length = r.toNat by omega]
  simp [ENNReal.toReal_pow, ENNReal.toReal_inv, one_div, inv_pow]

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
          · exact BlockGen_loop_direct
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
            §(localVarLens "r" block){2}) §HybridIROEager.mp{1})
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
      obtain ⟨hbs, -, -, -, -, hx, -⟩ := hfr
      obtain ⟨-, tm, -, t1, t2, tee, tran⟩ := hI
      simp only [decide_eq_false_iff_not, not_lt] at hg
      -- (GAP 10, as in the first case)
      have hi := (le_antisymm t2 hg).trans (sub_eq_iff_eq_add'.mp tm)
      refine ⟨hbs.trans hb, by rw [hr', hi], ?_⟩
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
        ec_progress
        ring
      -- EC: inline BlockSpongeTrans.next_block.
      --     wp; sp. call (_ : ={BlockSponge.BIRO.IRO.mp}). if=> //; wp; rnd; skip; smt().
      --     auto.
      · stmt_inline{1} (BlockSpongeTrans.next_block)
        stmt_wp; stmt_sp
        equiv_call (_ : ={BlockSponge.BIRO.IRO.mp})
        ec_auto

/-! ### `HybridIROEager.f` and `BlockSponge.BIRO.IRO.f` (EC l. 1614–1871) -/

omit [BlockSponge.Params] in
/-- The guard that EC's `splitwhile{1} 1 : i < (n1 %/ r) * r` leaves on the first loop. -/
private theorem splitwhile_guard_left (i n1 : ℤ) :
    (decide (i < n1) && decide (i < n1 / r * r)) = decide (i < n1 / r * r) := by
  have h := Int.ediv_mul_le n1 (ne_of_gt gt0_r)
  by_cases h' : i < n1 / r * r
  · have h1 : i < n1 := by omega
    simp [h', h1]
  · simp [h']

omit [BlockSponge.Params] in
/-- The guard that EC's `splitwhile{2} 1 : i < n1 %/ r` leaves on the first loop. -/
private theorem splitwhile_guard_right (i n1 : ℤ) :
    (decide (i < (n1 + r - 1) / r) && decide (i < n1 / r)) = decide (i < n1 / r) := by
  have hr := gt0_r
  have h : n1 / r ≤ (n1 + r - 1) / r := Int.ediv_le_ediv hr (by omega)
  by_cases h' : i < n1 / r
  · have h1 : i < (n1 + r - 1) / r := by omega
    simp [h', h1]
  · simp [h']

omit [SLCommon.Params] [BlockSponge.Params] in
/-- The guard that EC's `splitwhile{2} 1 : i < n1` leaves on the first loop, against `i < n`. -/
private theorem splitwhile_guard_le (i n m : ℤ) (h : n ≤ m) :
    decide (i < n) = (decide (i < m) && decide (i < n)) := by
  by_cases h' : i < n
  · have h1 : i < m := by omega
    simp [h', h1]
  · simp [h']

set_option maxHeartbeats 8000000 in
-- one declaration: EC's 258 lines (six `transitivity` steps, seven loops)
/-- EC's `lemma HybridIROEager_f_BlockIRO_f (n1 : int) (x2 : block list)` (EC l. 1614).

EC's script.  The right procedure takes its parameters as one pair `xn`, assigned to `x`, `n`
first, so EC's `seq 3 2` is `equiv_seq 3 3`.  EC's `conseq (_ : P ==> Q) _ (_ : size bs = n - 1
==> size bs = n)` is `equiv_conseq (: P ==> Q) _ (: … ==> …)` (`Logic/ECConseqHoare.lean`).
The leaves EC closes by `smt` are closed by hand; the guards the `splitwhile`s leave are the
lemmas `splitwhile_guard_left`, `_right`, `_le`. -/
theorem HybridIROEager_f_BlockIRO_f (n1 : ℤ) (x2 : List block) :
    equiv[ HybridIROEager.f (xs, n) ~ BlockSponge.BIRO.IRO.f (xn) :
      n1 = §n{1} ∧ x2 = (§xn{2}).1 ∧ §xs{1} = (§xn{2}).1 ∧ (§xn{2}).2 = (§n{1} + r - 1) / r ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ∧
        (valid_block x2 →
          (n1 ≤ 0 → §res{1} = [] ∧ §res{2} = []) ∧
          (0 < n1 → §res{1} = take n1 (blocks2bits §res{2}) ∧
            size §res{2} = (n1 + r - 1) / r)) ∧
        (¬ valid_block x2 → §res{1} = [] ∧ §res{2} = []) ] := by
  -- EC: proc=> /=.
  equiv_proc
  -- EC: seq 3 2 :
  --       (n1 = n{1} /\ xs{1} = x{2} /\ x2 = x{2} /\
  --        n{2} = (n{1} + r - 1) %/ r /\ n{2} * r = m{1} /\
  --        i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
  --       eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
  --     auto; progress.
  --     (the right procedure's one parameter `xn` is assigned to `x`, `n` first: `seq 3 3`)
  equiv_seq 3 3 : (n1 = §n{1} ∧ §xs{1} = §x{2} ∧ x2 = §x{2} ∧ §n{2} = (§n{1} + r - 1) / r ∧
    §n{2} * r = §m{1} ∧ §i{1} = 0 ∧ §i{2} = 0 ∧ §(localVarLens "bs" (List Bool)){1} = [] ∧
    §(localVarLens "bs" (List block)){2} = [] ∧
    eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
  · ec_auto
  -- EC: if=> //.
  stmt_if
  · ec_close
  rotate_left
  · ec_auto
  -- EC: case (n1 < 0).
  equiv_case (n1 < 0)
  -- EC: rcondf{1} 1; first auto; progress; smt().
  · stmt_rcondf{1} 1
    · intro σ₂; ec_auto
      rintro n xs m i bs mp ⟨⟨⟨rfl, -, -, -, -, rfl, -⟩, -⟩, hn⟩
      exact decide_eq_false (by omega)
    -- EC: rcondf{2} 1; first auto; progress;
    --       by rewrite -lezNgt needed_blocks_non_pos ltzW.
    stmt_rcondf{2} 1
    · intro σ₁; ec_auto
      rintro x n i bs mp ⟨⟨⟨h1, -, -, rfl, -, -, rfl, -⟩, -⟩, hn⟩
      exact decide_eq_false (not_lt.mpr (needed_blocks_non_pos _ (by omega)))
    -- EC: rcondf{1} 1; first auto; progress;
    --       by rewrite -lezNgt pmulr_lle0 1:gt0_r needed_blocks_non_pos ltzW.
    stmt_rcondf{1} 1
    · intro σ₂; ec_auto
      rintro n xs m i bs mp ⟨⟨⟨rfl, -, -, h4, rfl, rfl, -⟩, -⟩, hn⟩
      have h := needed_blocks_non_pos n1 (by omega)
      rw [← h4] at h
      exact decide_eq_false (not_lt.mpr (by nlinarith [ge0_r, h]))
    -- EC: by auto; progress; smt(needed_blocks0).
    ec_auto
    rintro n₁ xs₁ m₁ i₁ bs₁ mp₁ x₂ n₂ i₂ bs₂ mp₂
      ⟨⟨⟨-, -, -, -, -, -, -, rfl, rfl, ei⟩, -⟩, hn⟩
    exact ⟨ei, fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by omega)⟩,
      fun _ => ⟨rfl, rfl⟩⟩
  -- (* 0 <= n1 *)
  -- EC: conseq
  --       (_ :
  --        xs{1} = x{2} /\ n1 = n{1} /\ 0 <= n1 /\ n{2} = (n{1} + r - 1) %/ r /\
  --        n{2} * r = m{1} /\ n{1} <= m{1} /\
  --        i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  --        bs{1} = take n1 (blocks2bits bs{2}) /\
  --        size bs{2} = (n1 + r - 1) %/ r /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
  --     progress; [smt() | apply/needed_blocks_suff].
  --     move=> |> &1 &2 ? ? ? mp1 mp2 bs ? ? ?;
  --       smt(size_eq0 needed_blocks0 take0).
  equiv_conseq (: §xs{1} = §x{2} ∧ n1 = §n{1} ∧ 0 ≤ n1 ∧ §n{2} = (§n{1} + r - 1) / r ∧
      §n{2} * r = §m{1} ∧ §n{1} ≤ §m{1} ∧ §i{1} = 0 ∧ §i{2} = 0 ∧
      §(localVarLens "bs" (List Bool)){1} = [] ∧ §(localVarLens "bs" (List block)){2} = [] ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      §(localVarLens "bs" (List Bool)){1} =
        take n1 (blocks2bits §(localVarLens "bs" (List block)){2}) ∧
      size §(localVarLens "bs" (List block)){2} = (n1 + r - 1) / r ∧
      eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
  case pre =>
    ec_prep
    rename_i ei h0 hv
    exact ⟨h0, needed_blocks_suff _, ei⟩
  case post =>
    ec_prep
    rename_i ei' ei hsz h0 hv
    refine ⟨ei', fun _ => ⟨fun h => ?_, fun _ => hsz⟩, fun h => absurd hv h⟩
    obtain rfl : n₁ = 0 := by omega
    rw [needed_blocks0] at hsz
    obtain rfl : bs₂1 = [] := by simpa [size] using hsz
    exact ⟨take0 _, rfl⟩
  -- EC: splitwhile{1} 1 : i < (n1 %/ r) * r. splitwhile{2} 1 : i < n1 %/ r.
  stmt_splitwhile{1} 1 : §i < (n1 / r) * r
  stmt_splitwhile{2} 1 : §i < n1 / r
  -- EC: seq 1 1 :
  --       (xs{1} = x{2} /\ n1 = n{1} /\ 0 <= n1 /\ n{2} = (n1 + r - 1) %/ r /\
  --        n{2} * r = m{1} /\ n{1} <= m{1} /\ i{1} = n1 %/ r * r /\
  --        i{2} = n1 %/ r /\ size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
  equiv_seq 1 1 : (§xs{1} = §x{2} ∧ n1 = §n{1} ∧ 0 ≤ n1 ∧ §n{2} = (n1 + r - 1) / r ∧
    §n{2} * r = §m{1} ∧ §n{1} ≤ §m{1} ∧ §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧
    size §(localVarLens "bs" (List block)){2} = §i{2} ∧
    §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
    eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
  -- EC: conseq
  --       (_ :
  --        xs{1} = x{2} /\ n1 = n{1} /\ 0 <= n1 /\ n{2} = (n1 + r - 1) %/ r /\
  --        i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  --        i{1} = n1 %/ r * r /\ i{2} = n1 %/ r /\
  --        size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
  · equiv_conseq (: §xs{1} = §x{2} ∧ n1 = §n{1} ∧ 0 ≤ n1 ∧ §n{2} = (n1 + r - 1) / r ∧
        §i{1} = 0 ∧ §i{2} = 0 ∧ §(localVarLens "bs" (List Bool)){1} = [] ∧
          §(localVarLens "bs" (List block)){2} = [] ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
        §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧ size §(localVarLens "bs" (List block)){2} = §i{2} ∧
        §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    case pre => ec_close
    case post => ec_close
    -- EC: transitivity{1}
    --       { while (i < n1 %/ r * r) {
    --           b <@ HybridIROEager.fill_in(xs, i);
    --           bs <- rcons bs b;
    --           i <- i + 1;
    --         }
    --       }
    --       (={i, bs, xs, HybridIROEager.mp} /\ n1 = n{1} /\ 0 <= n1 ==>
    --        ={i, bs, xs, HybridIROEager.mp})
    --       (xs{1} = x{2} /\ n1 = n{1} /\ 0 <= n1 /\ n{2} = (n1 + r - 1) %/ r /\
    --        i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --        i{1} = n1 %/ r * r /\ i{2} = n1 %/ r /\
    --        size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
    --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
    equiv_trans{1} {
        while (decide ($i < n1 / r * r)) {
          b <- call (HybridIROEager.fill_in).procedure ($xs, $i);
          bs <- rcons $bs $b;
          i <- $i + 1;
        } }
      (={i, xs, HybridIROEager.mp} ∧
        §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧ n1 = §n{1} ∧
        0 ≤ n1 ==>
        ={i, xs, HybridIROEager.mp} ∧
          §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2})
      (§xs{1} = §x{2} ∧ n1 = §n{1} ∧ 0 ≤ n1 ∧ §n{2} = (n1 + r - 1) / r ∧
        §i{1} = 0 ∧ §i{2} = 0 ∧ §(localVarLens "bs" (List Bool)){1} = [] ∧
          §(localVarLens "bs" (List block)){2} = [] ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
        §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧ size §(localVarLens "bs" (List block)){2} = §i{2} ∧
        §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    -- EC: progress; exists HybridIROEager.mp{1} [] 0 n{1} x{2}=> //.
    · rintro σ₁ σ₂ ⟨hxs, hn, h0, hn2, hi1, hi2, hb1, hb2, ei⟩
      exact ⟨σ₁, ⟨⟨rfl, rfl, rfl⟩, rfl, hn, h0⟩, hxs, hn, h0, hn2, hi1, hi2, hb1, hb2, ei⟩
    · rintro τ₁ τ τ₂ ⟨⟨h1, -, h3⟩, h4⟩ ⟨k1, k2, k3, k4, k5⟩
      exact ⟨h1.trans k1, k2, k3, h4.trans k4, by rw [h3]; exact k5⟩
    -- EC: while (={i, bs, xs, HybridIROEager.mp} /\ n1 = n{1} /\ 0 <= n1).
    --     wp. call (_ : ={HybridIROEager.mp}). if=> //; auto.
    --     auto; progress; smt(leq_trunc_div ge0_r).
    --     auto; progress; smt(leq_trunc_div ge0_r).
    · equiv_while (={i, xs, HybridIROEager.mp} ∧
      §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧ n1 = §n{1} ∧
        0 ≤ n1)
      · stmt_wp
        equiv_call (_ : ={HybridIROEager.mp})
        ec_auto
        rintro i₁ xs₁ mp₁ bs₁ n₁ i₂ xs₂ mp₂ bs₂ ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl, h0⟩, -⟩
        refine ⟨⟨rfl, rfl⟩, ?_⟩
        rintro r₁ g₁ r₂ g₂ ⟨rfl, hmp⟩
        exact ⟨⟨⟨rfl, rfl, hmp⟩, rfl, rfl, h0⟩, splitwhile_guard_left _ _⟩
      ec_auto
      rintro i₁ xs₁ mp₁ bs₁ n₁ i₂ xs₂ mp₂ bs₂ ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, h0⟩
      exact ⟨⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl, h0⟩, splitwhile_guard_left _ _⟩,
        fun τ₁ τ₂ _ _ ⟨⟨hi, hx, hmp⟩, hbs, _, _⟩ _ _ => ⟨⟨hi, hx, hmp⟩, hbs⟩⟩
    -- EC: (transitivity{2}
    --        { while (i < n1 %/ r) {
    --            b <@ BlockSponge.BIRO.IRO.fill_in(x, i);
    --            bs <- rcons bs b;
    --            i <- i + 1;
    --          }
    --        }
    --        (xs{1} = x{2} /\ n1 = n{1} /\ 0 <= n1 /\ n{2} = (n1 + r - 1) %/ r /\
    --         i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
    --         eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --         i{1} = n1 %/ r * r /\ i{2} = n1 %/ r /\ size bs{2} = i{2} /\
    --         bs{1} = blocks2bits bs{2} /\
    --         eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
    --        (={i, x, bs, BlockSponge.BIRO.IRO.mp} /\ n{2} = (n1 + r - 1) %/ r ==>
    --         ={i, x, bs, BlockSponge.BIRO.IRO.mp})=> //;
    --        first progress;
    --          exists BlockSponge.BIRO.IRO.mp{2} [] 0 ((n{1} + r - 1) %/ r) x{2}=> //);
    --       first last.
    · equiv_trans{2} {
          while (decide ($i < n1 / r)) {
            b <- call (BlockSponge.BIRO.IRO.fill_in).procedure ($x, $i);
            bs <- rcons $bs $b;
            i <- $i + 1;
          } }
        (§xs{1} = §x{2} ∧ n1 = §n{1} ∧ 0 ≤ n1 ∧ §n{2} = (n1 + r - 1) / r ∧
          §i{1} = 0 ∧ §i{2} = 0 ∧ §(localVarLens "bs" (List Bool)){1} = [] ∧
            §(localVarLens "bs" (List block)){2} = [] ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧ size §(localVarLens "bs" (List block)){2} = §i{2} ∧
          §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
        (={i, x, BlockSponge.BIRO.IRO.mp} ∧
          §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
          §n{2} = (n1 + r - 1) / r ==>
          ={i, x, BlockSponge.BIRO.IRO.mp} ∧
            §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2})
      · rintro σ₁ σ₂ ⟨hxs, hn, h0, hn2, hi1, hi2, hb1, hb2, ei⟩
        exact ⟨σ₂, ⟨hxs, hn, h0, hn2, hi1, hi2, hb1, hb2, ei⟩, ⟨rfl, rfl, rfl⟩, rfl, hn2⟩
      · rintro τ₁ τ τ₂ ⟨k1, k2, k3, k4, k5⟩ ⟨⟨h1, -, h3⟩, h4⟩
        exact ⟨k1, by rw [← h1]; exact k2, by rw [← h4, ← h1]; exact k3,
          by rw [← h4]; exact k4, by rw [← h3]; exact k5⟩
      rotate_left
      -- EC: while
      --       (={i, x, bs, BlockSponge.BIRO.IRO.mp} /\ n{2} = (n1 + r - 1) %/ r).
      --     wp. call (_ : ={BlockSponge.BIRO.IRO.mp}). if=> //; auto.
      --     auto; progress;
      --       have /# : n1 %/ r <= (n1 + r - 1) %/ r
      --         by rewrite leq_div2r; smt(gt0_r).
      --     auto; progress;
      --       have /# : n1 %/ r <= (n1 + r - 1) %/ r
      --         by rewrite leq_div2r; smt(gt0_r).
      · equiv_while (={i, x, BlockSponge.BIRO.IRO.mp} ∧
        §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ∧
          §n{2} = (n1 + r - 1) / r)
        · stmt_wp
          equiv_call (_ : ={BlockSponge.BIRO.IRO.mp})
          ec_auto
          rintro i₁ x₁ mp₁ bs₁ i₂ x₂ mp₂ bs₂ n₂ ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, -⟩
          refine ⟨⟨rfl, rfl⟩, ?_⟩
          rintro r₁ g₁ r₂ g₂ ⟨rfl, hmp⟩
          exact ⟨⟨⟨rfl, rfl, hmp⟩, rfl, rfl⟩, (splitwhile_guard_right _ _).symm⟩
        ec_auto
        rintro i₁ x₁ mp₁ bs₁ i₂ x₂ mp₂ bs₂ n₂ ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩
        exact ⟨⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩, (splitwhile_guard_right _ _).symm⟩,
          fun τ₁ τ₂ _ _ ⟨⟨hi, hx, hmp⟩, hbs, _⟩ _ _ => ⟨⟨hi, hx, hmp⟩, hbs⟩⟩
      -- EC: conseq
      --       (_ :
      --        xs{1} = x{2} /\ 0 <= n1 /\
      --        i{1} = 0 /\ i{2} = 0 /\ bs{1} = [] /\ bs{2} = [] /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
      --        i{1} = n1 %/ r * r /\ i{2} = n1 %/ r /\
      --        size bs{2} = n1 %/ r /\ bs{1} = blocks2bits bs{2} /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
      equiv_conseq (: §xs{1} = §x{2} ∧ 0 ≤ n1 ∧ §i{1} = 0 ∧ §i{2} = 0 ∧
          §(localVarLens "bs" (List Bool)){1} = [] ∧ §(localVarLens "bs" (List block)){2} = [] ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧ size §(localVarLens "bs" (List block)){2} = n1 / r ∧
          §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
      case pre => ec_close
      case post => ec_close
      -- EC: transitivity{1}
      --       { (i, bs) <@ HybridIROEagerTrans.loop(n1 %/ r, xs); }
      --       (={xs, HybridIROEager.mp} /\ n{2} = n1 %/ r /\ i{1} = 0 /\ bs{1} = [] ==>
      --        ={i, xs, bs, HybridIROEager.mp})
      --       (xs{1} = x{2} /\ 0 <= n1 /\ i{2} = 0 /\ bs{2} = [] /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
      --        i{1} = n1 %/ r * r /\ i{2} = n1 %/ r /\
      --        size bs{2} = n1 %/ r /\ bs{1} = blocks2bits bs{2} /\
      --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
      equiv_trans{1} {
          i, bs <- call (HybridIROEagerTrans.loop).procedure (n1 / r, $xs); }
        (={xs, HybridIROEager.mp} ∧ §i{1} = 0 ∧ §(localVarLens "bs" (List Bool)){1} = [] ==>
          ={i, xs, HybridIROEager.mp} ∧
            §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2})
        (§xs{1} = §x{2} ∧ 0 ≤ n1 ∧ §i{2} = 0 ∧ §(localVarLens "bs" (List block)){2} = [] ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧ size §(localVarLens "bs" (List block)){2} = n1 / r ∧
          §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
      -- EC: progress; exists HybridIROEager.mp{1} (n1 %/ r) x{2}=> //.
      · rintro σ₁ σ₂ ⟨hxs, h0, hi1, hi2, hb1, hb2, ei⟩
        exact ⟨σ₁, ⟨⟨rfl, rfl⟩, hi1, hb1⟩, hxs, h0, hi2, hb2, ei⟩
      · rintro τ₁ τ τ₂ ⟨⟨h1, -, h3⟩, h4⟩ ⟨k1, k2, k3, k4, k5⟩
        exact ⟨h1.trans k1, k2, k3, h4.trans k4, by rw [h3]; exact k5⟩
      -- EC: inline HybridIROEagerTrans.loop; sp; wp.
      --     while
      --       (={HybridIROEager.mp} /\ i{1} = i0{2} /\ bs{1} = bs0{2} /\
      --        xs{1} = xs0{2} /\ n0{2} = n1 %/ r).
      --     wp. call (_ : ={HybridIROEager.mp}). if=> //; wp; rnd; auto.
      --     auto. auto.
      · stmt_inline{2} (HybridIROEagerTrans.loop); stmt_sp; stmt_wp
        --     (EC's `n0` is `n` here: the middle program does not read the caller's `n`)
        equiv_while (={HybridIROEager.mp} ∧ §i{1} = §i0{2} ∧
          §(localVarLens "bs" (List Bool)){1} = §bs0{2} ∧
          §xs{1} = §xs0{2} ∧ §n{2} = n1 / r)
        · stmt_wp
          equiv_call (_ : ={HybridIROEager.mp})
          ec_auto
        ec_auto
      -- EC: (transitivity{2}
      --        { (i, bs) <@ BlockSpongeTrans.loop(n1 %/ r, x); }
      --        (xs{1} = x{2} /\ 0 <= n1 /\
      --         eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
      --         i{1} = n1 %/ r * r /\ i{2} = n1 %/ r /\
      --         size bs{2} = n1 %/ r /\ bs{1} = blocks2bits bs{2} /\
      --         eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
      --        (={x, BlockSponge.BIRO.IRO.mp} /\ i{2} = 0 /\ bs{2} = [] ==>
      --         ={i, x, bs, BlockSponge.BIRO.IRO.mp})=> //;
      --        first progress; exists BlockSponge.BIRO.IRO.mp{2} x{2}=> //);
      --       last first.
      · equiv_trans{2} {
            i, bs <- call (BlockSpongeTrans.loop).procedure (n1 / r, $x); }
          (§xs{1} = §x{2} ∧ 0 ≤ n1 ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
            §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧
              size §(localVarLens "bs" (List block)){2} = n1 / r ∧
            §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
              eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
          (={x, BlockSponge.BIRO.IRO.mp} ∧ §i{2} = 0 ∧ §(localVarLens "bs" (List block)){2} = [] ==>
            ={i, x, BlockSponge.BIRO.IRO.mp} ∧
              §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2})
        · rintro σ₁ σ₂ ⟨hxs, h0, hi2, hb2, ei⟩
          exact ⟨σ₂, ⟨hxs, h0, ei⟩, ⟨rfl, rfl⟩, hi2, hb2⟩
        · rintro τ₁ τ τ₂ ⟨k1, k2, k3, k4, k5⟩ ⟨⟨h1, -, h3⟩, h4⟩
          exact ⟨k1, by rw [← h1]; exact k2, by rw [← h4]; exact k3,
            by rw [← h4]; exact k4, by rw [← h3]; exact k5⟩
        rotate_left
        -- EC: inline BlockSpongeTrans.loop; sp; wp.
        --     while
        --       (={BlockSponge.BIRO.IRO.mp} /\ i0{1} = i{2} /\ n0{1} = n1 %/ r /\
        --        xs{1} = x{2} /\ bs0{1} = bs{2}).
        --     wp. call (_ : ={BlockSponge.BIRO.IRO.mp}). if=> //; wp; rnd; auto.
        --     auto. auto.
        · stmt_inline{1} (BlockSpongeTrans.loop); stmt_sp; stmt_wp
          --     (EC's `n0` is `n` here, as above)
          equiv_while (={BlockSponge.BIRO.IRO.mp} ∧ §i0{1} = §i{2} ∧ §n{1} = n1 / r ∧
            §xs{1} = §x{2} ∧ §bs0{1} = §(localVarLens "bs" (List block)){2})
          · stmt_wp
            equiv_call (_ : ={BlockSponge.BIRO.IRO.mp})
            ec_auto
          ec_auto
        -- EC: call (HybridIROEagerTrans_BlockSpongeTrans_loop (n1 %/ r)).
        --     skip; progress; smt(divz_ge0 gt0_r).
        equiv_call (HybridIROEagerTrans_BlockSpongeTrans_loop (n1 / r))
        ec_auto
        ec_progress
        exact Int.ediv_nonneg (by assumption) ge0_r
  -- (* either nothing more to do on either side, or a single block to add
  --    on the right side, and less than r bits to add on the left side *)
  -- EC: conseq
  --       (_ :
  --        n1 = n{1} /\ 0 <= n1 /\ xs{1} = x{2} /\ n{2} = (n1 + r - 1) %/ r /\
  --        n{2} * r = m{1} /\ n{1} <= m{1} /\ i{1} = n1 %/ r * r /\
  --        i{2} = n1 %/ r /\ size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} /\
  --        (i{2} = n{2} \/ i{2} + 1 = n{2}) ==>
  --        bs{1} = take n1 (blocks2bits bs{2}) /\ size bs{2} = n{2} /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}) => //.
  --     progress; by apply/needed_blocks_rel_div_r.
  equiv_conseq (: n1 = §n{1} ∧ 0 ≤ n1 ∧ §xs{1} = §x{2} ∧ §n{2} = (n1 + r - 1) / r ∧
      §n{2} * r = §m{1} ∧ §n{1} ≤ §m{1} ∧ §i{1} = n1 / r * r ∧ §i{2} = n1 / r ∧
      size §(localVarLens "bs" (List block)){2} = §i{2} ∧
        §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ∧
      (§i{2} = §n{2} ∨ §i{2} + 1 = §n{2}) ==>
      §(localVarLens "bs" (List Bool)){1} =
        take n1 (blocks2bits §(localVarLens "bs" (List block)){2}) ∧
        size §(localVarLens "bs" (List block)){2} = §n{2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
  case pre =>
    ec_prep
    rename_i ei h0 hle hsz
    refine ⟨h0, hle, hsz, ei, ?_⟩
    rw [hsz]; exact needed_blocks_rel_div_r _
  case post => ec_close
  -- EC: case (i{2} = n{2}).  (* so i{1} = n{1} and i{1} = m{1} *)
  equiv_case (§i{2} = §n{2})
  -- EC: rcondf{2} 1; first auto; progress; smt().
  --     rcondf{1} 1; first auto; progress; smt().
  --     rcondf{1} 1; first auto; progress; smt().
  · stmt_rcondf{2} 1
    · intro σ₁; ec_auto
    stmt_rcondf{1} 1
    · intro σ₂; ec_auto
    stmt_rcondf{1} 1
    · intro σ₂; ec_auto
    -- EC: auto=> |> &1 &2 ? ? sz_eq ? ? need_blks_eq.
    --     split.
    --     have -> : n1 = size (blocks2bits bs{2})
    --       by rewrite size_blocks2bits sz_eq -mulzC divzK 1:needed_blocks_eq_div_r.
    --     by rewrite take_size.
    --     by rewrite sz_eq need_blks_eq.
    ec_auto
    rintro n₁ xs₁ m₁ i₁ bs₁ mp₁ x₂ n₂ i₂ bs₂ mp₂
      ⟨⟨-, h0, -, hn2, -, -, -, hi2, hsz, rfl, ei, -⟩, hin⟩
    have hdvd : r ∣ n1 := (needed_blocks_eq_div_r n1).mpr (by rw [← hi2, ← hn2]; exact hin)
    refine ⟨?_, hsz.trans hin, ei⟩
    have hsize : size (blocks2bits bs₂) = n1 := by
      rw [size_blocks2bits, hsz, hi2, mul_comm]; exact Int.ediv_mul_cancel hdvd
    rw [← hsize, take_size]
  -- (* i{2} <> n{2}, so i{2} + 1 = n{2}, m{1} - i{1} = r and i{1} <= m{1} *)
  -- EC: rcondt{2} 1; first auto; progress; smt().
  stmt_rcondt{2} 1
  · intro σ₁; ec_auto
    rintro x n i bs mp ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hor⟩, hne⟩
    exact decide_eq_true (by omega)
  -- EC: rcondf{2} 4.
  --     auto; call (_ : true); [if=> //; auto; progress; smt() | auto; smt()].
  stmt_rcondf{2} 4
  · intro σ₁
    stmt_wp
    hoare_call (: True ==> True)
    · hoare_proc; ec_auto
    · ec_auto
  -- EC: conseq
  --       (_ :
  --        n1 = n{1} /\ 0 <= n1 /\ xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\
  --        n{1} <= m{1} /\ m{1} - i{1} = r /\ i{1} <= n{1} /\
  --        bs{1} = blocks2bits bs{2} /\ size bs{1} = i{1} /\ size bs{2} = i{2} /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  --        bs{1} = take n1 (blocks2bits bs{2}) /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
  --       _
  --       (_ : size bs = n - 1 ==> size bs = n)=> //.
  --     progress; smt(divz_ge0 gt0_r lez_floor size_blocks2bits).
  --     wp. call (_ : true). auto. skip; smt(size_rcons).
  equiv_conseq (: n1 = §n{1} ∧ 0 ≤ n1 ∧ §xs{1} = §x{2} ∧ 0 ≤ §i{2} ∧ §i{1} = §i{2} * r ∧
      §n{1} ≤ §m{1} ∧ §m{1} - §i{1} = r ∧ §i{1} ≤ §n{1} ∧
      §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
        size §(localVarLens "bs" (List Bool)){1} = §i{1} ∧
      size §(localVarLens "bs" (List block)){2} = §i{2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      §(localVarLens "bs" (List Bool)){1} =
        take n1 (blocks2bits §(localVarLens "bs" (List block)){2}) ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    _ (: size §(localVarLens "bs" (List block)){2} = §n{2} - 1 ==>
      size §(localVarLens "bs" (List block)){2} = §n{2})
  case pre =>
    ec_prep
    · rename_i h; exact absurd trivial h
    · rename_i ei h0 hsz hne hn2 hle
      refine ⟨⟨h0, by rw [hsz]; exact Int.ediv_nonneg h0 ge0_r, by rw [hsz], hle,
        by rw [hsz]; ring, Int.ediv_mul_le _ (ne_of_gt gt0_r),
        by rw [size_blocks2bits, hsz, mul_comm], ei⟩, by ring⟩
  case post => ec_close
  case hoare =>
    stmt_wp
    hoare_call (: True ==> True)
    · hoare_proc; ec_auto
    · ec_auto
      intro bs n h r' g
      rw [size_rcons, h]; ring
  -- EC: transitivity{1}
  --       { while (i < m) {
  --           b <@ HybridIROEager.fill_in(xs, i);
  --           bs <- rcons bs b;
  --           i <- i + 1;
  --         }
  --       }
  --       (={bs, m, i, xs, HybridIROEager.mp} /\ n1 = n{1} /\ i{1} <= n1 /\
  --        n1 <= m{1} /\ size bs{1} = i{1} ==>
  --        ={HybridIROEager.mp} /\ bs{1} = take n1 bs{2})
  --       (xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\ m{1} - i{1} = r /\
  --        size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  --        bs{1} = blocks2bits bs{2} /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
  --     progress;
  --       exists HybridIROEager.mp{1} (blocks2bits bs{2})
  --              (size bs{2} * r) m{1} x{2}=> //.
  --     progress; smt(take_cat).
  equiv_trans{1} {
      while (decide ($i < $m)) {
        b <- call (HybridIROEager.fill_in).procedure ($xs, $i);
        bs <- rcons $bs $b;
        i <- $i + 1;
      } }
    (={m, i, xs, HybridIROEager.mp} ∧
      §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ∧ n1 = §n{1} ∧
      §i{1} ≤ n1 ∧
      n1 ≤ §m{1} ∧ size §(localVarLens "bs" (List Bool)){1} = §i{1} ==>
      ={HybridIROEager.mp} ∧
        §(localVarLens "bs" (List Bool)){1} = take n1 §(localVarLens "bs" (List Bool)){2})
    (§xs{1} = §x{2} ∧ 0 ≤ §i{2} ∧ §i{1} = §i{2} * r ∧ §m{1} - §i{1} = r ∧
        size §(localVarLens "bs" (List block)){2} = §i{2} ∧
          §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
  · rintro σ₁ σ₂ ⟨hn, h0, hxs, hi0, hi, hnm, hm, hin, hbs, hsz1, hsz2, ei⟩
    exact ⟨σ₁, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, hn, by rw [hn]; exact hin, by rw [hn]; exact hnm,
      hsz1⟩, hxs, hi0, hi, hm, hsz2, hbs, ei⟩
  · rintro τ₁ τ τ₂ ⟨hmp, hbs⟩ ⟨kbs, kei⟩
    exact ⟨by rw [hbs, kbs], by rw [hmp]; exact kei⟩
  -- EC: splitwhile{2} 1 : i < n1.
  --     seq 1 1 :
  --       (={HybridIROEager.mp, xs, bs, i, m} /\ i{1} = n1 /\ n1 <= m{1} /\
  --        size bs{1} = n1).
  · stmt_splitwhile{2} 1 : §i < n1
    equiv_seq 1 1 : (={HybridIROEager.mp, xs, bs, i, m} ∧ §i{1} = n1 ∧ n1 ≤ §m{1} ∧
      size §bs{1} = n1)
    -- EC: while
    --       (={HybridIROEager.mp, xs, bs, i, m} /\ n{1} = n1 /\ n1 <= m{1} /\
    --        i{1} <= n1 /\ size bs{1} = i{1}).
    --     wp; call (_ : ={HybridIROEager.mp}); first if => //; wp; rnd; auto.
    --     skip; smt(size_rcons).
    --     skip; smt().
    · equiv_while (={HybridIROEager.mp, xs, bs, i, m} ∧ §n{1} = n1 ∧ n1 ≤ §m{1} ∧
        §i{1} ≤ n1 ∧ size §bs{1} = §i{1})
      · stmt_wp
        equiv_call (_ : ={HybridIROEager.mp})
        ec_auto
        rintro mp₁ xs₁ bs₁ i₁ m₁ n₁ mp₂ xs₂ bs₂ i₂ m₂
          ⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, hnm, hin, hsz⟩, hg, -⟩
        have hg' := of_decide_eq_true hg
        refine ⟨⟨rfl, rfl⟩, ?_⟩
        rintro r₁ g₁ r₂ g₂ ⟨rfl, hmp⟩
        exact ⟨⟨⟨hmp, rfl, rfl, rfl, rfl⟩, rfl, hnm, by omega, by rw [size_rcons, hsz]⟩,
          splitwhile_guard_le _ _ _ hnm⟩
      ec_auto
      rintro m₁ i₁ xs₁ mp₁ bs₁ n₁ m₂ i₂ xs₂ mp₂ bs₂
        ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, hin, hnm, hsz⟩
      refine ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, hnm, hin, hsz⟩,
        splitwhile_guard_le _ _ _ hnm⟩, ?_⟩
      intro τ₁ τ₂ _ _ hI hg1 _
      obtain ⟨heq, tn, tnm, tin, tsz⟩ := hI
      have hg := of_decide_eq_false hg1
      have hi := le_antisymm tin (by rw [← tn]; exact not_lt.mp hg)
      exact ⟨heq, hi, tnm, by rw [tsz, hi]⟩
    -- EC: while
    --       (={HybridIROEager.mp, xs, i, m} /\ n1 <= m{1} /\
    --        n1 <= i{1} <= m{1} /\ n1 <= size bs{2} /\
    --        bs{1} = take n1 bs{2}).
    --     wp; call (_ : ={HybridIROEager.mp}); first if => //; wp; rnd; auto.
    --     skip; progress;
    --       [smt() | smt() | smt(size_rcons) |
    --        rewrite -cats1 take_cat;
    --        smt(size_rcons take_oversize cats1 cats0)].
    --     skip; smt(take_size).
    equiv_while (={HybridIROEager.mp, xs, i, m} ∧ n1 ≤ §m{1} ∧ n1 ≤ §i{1} ∧ §i{1} ≤ §m{1} ∧
      n1 ≤ size §bs{2} ∧ §bs{1} = take n1 §bs{2})
    · stmt_wp
      equiv_call (_ : ={HybridIROEager.mp})
      --     (GAP 3: the left call discards its result)
      simp only [Setter.throwaway_set]
      ec_auto
      rintro mp₁ xs₁ i₁ m₁ bs₁ mp₂ xs₂ i₂ m₂ bs₂
        ⟨⟨⟨rfl, rfl, rfl, rfl⟩, hnm, hni, him, hsz, rfl⟩, hg, -⟩
      have hg' := of_decide_eq_true hg
      refine ⟨⟨rfl, rfl⟩, ?_⟩
      rintro r₁ g₁ r₂ g₂ ⟨rfl, hmp⟩
      refine ⟨⟨⟨hmp, rfl, rfl, rfl⟩, hnm, by omega, by omega,
        by rw [size_rcons]; omega, ?_⟩, rfl⟩
      rw [rcons, take_cat]
      split_ifs with h
      · rfl
      · have h' : n1 = size bs₂ := by omega
        rw [h', sub_self, take0, cats0, take_size]
    --     (GAP 12: the strict `auto` and `equiv_skip` run out of recursion depth on this goal,
    --     whose conditions have `bs{1} = take n1 bs{2}` next to `={bs}`: the rule `prhlStmt_skip`
    --     and the implication by hand)
    refine prhlStmt_skip ?_
    rintro σ₁ σ₂ ⟨⟨hmp, hxs, hbs, hi, hm⟩, hin, hnm, hsz⟩
    exact ⟨⟨⟨⟨hmp, hxs, hi, hm⟩, hnm, hin.ge, hin.le.trans hnm,
        le_of_eq (hsz.symm.trans (congrArg size hbs)),
        (take_size _).symm.trans (congrArg₂ take hsz hbs)⟩,
        congrArg₂ (fun a b : ℤ => decide (a < b)) hi hm⟩,
      fun τ₁ τ₂ _ _ ⟨⟨tmp, _, _, _⟩, _, _, _, _, tbs⟩ _ _ => ⟨tmp, tbs⟩⟩
  -- (* now we can use HybridIROEagerTrans_BlockSpongeTrans_next_block *)
  -- EC: transitivity{1}
  --       { (bs, i) <@ HybridIROEagerTrans.next_block(xs, i, m, bs);
  --       }
  --       (={i, m, xs, bs, HybridIROEager.mp} ==>
  --        ={i, m, xs, bs, HybridIROEager.mp})
  --       (xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\ m{1} - i{1} = r /\
  --       size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
  --       eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  --       bs{1} = blocks2bits bs{2} /\
  --       eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})=> //.
  --     progress [-delta];
  --       exists HybridIROEager.mp{1} (blocks2bits bs{2}) (size bs{2} * r)
  --              m{1} x{2}=> //.
  · equiv_trans{1} {
        bs, i <- call (HybridIROEagerTrans.next_block).procedure ($xs, $i, $m, $bs); }
      (={i, m, xs, HybridIROEager.mp} ∧
        §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2} ==>
        ={i, m, xs, HybridIROEager.mp} ∧
          §(localVarLens "bs" (List Bool)){1} = §(localVarLens "bs" (List Bool)){2})
      (§xs{1} = §x{2} ∧ 0 ≤ §i{2} ∧ §i{1} = §i{2} * r ∧ §m{1} - §i{1} = r ∧
        size §(localVarLens "bs" (List block)){2} = §i{2} ∧
          §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
        §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
    · rintro σ₁ σ₂ h
      exact ⟨σ₁, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩, h⟩
    · rintro τ₁ τ τ₂ ⟨⟨-, -, -, hmp⟩, hbs⟩ ⟨kbs, kei⟩
      exact ⟨by rw [hbs, kbs], by rw [hmp]; exact kei⟩
    -- EC: inline HybridIROEagerTrans.next_block; sim.
    --     (`sim` does not pass the inlined call's copies of the parameters: EC's `while` rule,
    --     as in `HybridIROEagerTrans_BlockSpongeTrans_loop`)
    · stmt_inline{2} (HybridIROEagerTrans.next_block); stmt_sp; stmt_wp
      equiv_while (§xs{1} = §xs0{2} ∧ §i{1} = §i0{2} ∧ §m{1} = §m0{2} ∧ §bs{1} = §bs0{2} ∧
        ={HybridIROEager.mp})
      · stmt_wp
        equiv_call (_ : ={HybridIROEager.mp})
        ec_auto
      ec_auto
    -- EC: (transitivity{2}
    --        { (bs, i) <@ BlockSpongeTrans.next_block(x, i, bs);
    --        }
    --        (xs{1} = x{2} /\ 0 <= i{2} /\ i{1} = i{2} * r /\ m{1} - i{1} = r /\
    --         size bs{2} = i{2} /\ bs{1} = blocks2bits bs{2} /\
    --         eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
    --         bs{1} = blocks2bits bs{2} /\
    --         eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1})
    --        (={bs, i, x, BlockSponge.BIRO.IRO.mp} ==>
    --         ={bs, i, x, BlockSponge.BIRO.IRO.mp})=> //;
    --        first progress [-delta];
    --                exists BlockSponge.BIRO.IRO.mp{2} bs{2} (size bs{2}) x{2}=> //);
    --       last first.
    · equiv_trans{2} {
          bs, i <- call (BlockSpongeTrans.next_block).procedure ($x, $i, $bs); }
        (§xs{1} = §x{2} ∧ 0 ≤ §i{2} ∧ §i{1} = §i{2} * r ∧ §m{1} - §i{1} = r ∧
        size §(localVarLens "bs" (List block)){2} = §i{2} ∧
          §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
          eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
          §(localVarLens "bs" (List Bool)){1} = blocks2bits §(localVarLens "bs" (List block)){2} ∧
            eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1})
        (={i, x, BlockSponge.BIRO.IRO.mp} ∧
          §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2} ==>
          ={i, x, BlockSponge.BIRO.IRO.mp} ∧
            §(localVarLens "bs" (List block)){1} = §(localVarLens "bs" (List block)){2})
      · rintro σ₁ σ₂ h
        exact ⟨σ₂, h, ⟨rfl, rfl, rfl⟩, rfl⟩
      · rintro τ₁ τ τ₂ ⟨kbs, kei⟩ ⟨⟨-, -, hmp⟩, hbs⟩
        exact ⟨by rw [← hbs]; exact kbs, by rw [← hmp]; exact kei⟩
      rotate_left
      -- EC: inline BlockSpongeTrans.next_block; sim.
      · stmt_inline{1} (BlockSpongeTrans.next_block)
        sim
      -- EC: exists* i{2}; elim*=> i2.
      --     call (HybridIROEagerTrans_BlockSpongeTrans_next_block i2).
      --     auto.
      equiv_exists* §i{2}
      intro i2
      equiv_call (HybridIROEagerTrans_BlockSpongeTrans_next_block i2)
      ec_auto

/-! ### `LowerHybridIRO(HybridIROEager).f` and `BlockSponge.BIRO.IRO.f` (EC l. 1873–1909) -/

set_option maxHeartbeats 4000000 in
-- one declaration: two `conseq`s of long lemmas
/-- EC's `lemma HybridIROEager_BlockIRO_f` (EC l. 1873), the last of the theory `HybridIRO`.

EC: `transitivity HybridIROEager.f (…) (…)`, the rule `prhlProc_trans_ec` here (GAP 8), so the
two judgments come first (`h₁`: `conseq Lower_HybridIROEager_f`; `h₂`: `exists*`, then
`conseq (HybridIROEager_f_BlockIRO_f n1 xs')`), then EC's two side conditions.  The middle
memory (EC: `exists HybridIROEager.mp{1} BlockSponge.BIRO.IRO.mp{2} (xs{1}, n{1} * r)`) is the
left globals with `BlockSponge.BIRO.IRO.mp` set to the right one's.  Both procedures take one
pair: `xs{1} = x{2} /\ ={n}` is about its components. -/
theorem HybridIROEager_BlockIRO_f :
    equiv[ LowerHybridIRO(HybridIROEager).f (x) ~ BlockSponge.BIRO.IRO.f (xn) :
      (§x{1}).1 = (§xn{2}).1 ∧ (§x{1}).2 = (§xn{2}).2 ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      ={res} ∧ eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ] := by
  -- EC: by conseq Lower_HybridIROEager_f=> |> &1 &2 ? -> ?.
  have h₁ : equiv[ LowerHybridIRO(HybridIROEager).f (x) ~ HybridIROEager.f (xs, n) :
      (§x{1}).1 = §xs{2} ∧ ={HybridIROEager.mp} ∧ §n{2} = (§x{1}).2 * r ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      §res{1} = bits2blocks §res{2} ∧ ={HybridIROEager.mp} ] := by
    equiv_conseq Lower_HybridIROEager_f
    · exact fun _ _ _ _ ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3.symm⟩
    · exact fun _ _ _ _ h => h
  -- EC: exists* n{1}; elim*=> n1; exists* xs{1}; elim*=> xs'.
  --     conseq (HybridIROEager_f_BlockIRO_f n1 xs')=> //.
  have h₂ : equiv[ HybridIROEager.f (xs, n) ~ BlockSponge.BIRO.IRO.f (xn) :
      §xs{1} = (§xn{2}).1 ∧ §n{1} = (§xn{2}).2 * r ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ==>
      §res{1} = blocks2bits §res{2} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIROEager.mp{1} ] := by
    --     (`exists*` on a procedure judgment reads the declared parameter names: `xs` is `x`)
    equiv_exists* §n{1}, §x{1}
    intro (n1 : ℤ) (xs' : List block)
    --     (`post` needs the precondition, as EC states it: `equiv_conseq_pre`)
    equiv_conseq_pre (HybridIROEager_f_BlockIRO_f n1 xs')
    -- EC: move=> |> &1 &2 ? -> inv; by rewrite needed_blocks_prod_r.
    · rintro ⟨xs, n⟩ g₁ ⟨x, n'⟩ g₂ ⟨⟨⟨hx, hn, ei⟩, hn1⟩, hxs⟩
      replace hx : xs = x := hx
      replace hn : n = n' * r := hn
      replace hn1 : n = n1 := hn1
      replace hxs : xs = xs' := hxs
      exact ⟨hn1.symm, hxs.symm.trans hx, hx,
        by rw [hn]; exact (needed_blocks_prod_r n').symm, ei⟩
    -- EC: move=> |> &1 &2 ? n1_eq ? res1 res2 ? ? ? vb_imp not_vb_imp.
    --     case: (valid_block xs{1})=> [vb_xs1 | not_vb_xs1].
    --     have [le0_n1_imp gt0_n1_imp] := vb_imp vb_xs1.
    --     case: (n{1} <= 0)=> [le0_n1 /# | not_le0_n1].
    --     have gt0_n1 : 0 < n{1} by smt().
    --     have [-> sz_res2] := gt0_n1_imp gt0_n1.
    --     have -> : n{1} = size(blocks2bits res2)
    --        by rewrite size_blocks2bits sz_res2 n1_eq
    --                   needed_blocks_prod_r mulzC.
    --     by rewrite take_size.
    --     by have [-> ->] := not_vb_imp not_vb_xs1.
    · rintro ⟨xs, (n : ℤ)⟩ g₁ ⟨x, (n' : ℤ)⟩ g₂ ⟨⟨⟨hx, hn, -⟩, hn1⟩, hxs⟩
        (r₁ : List Bool) τ₁ (r₂ : List block) τ₂ ⟨ei, vb_imp, not_vb_imp⟩
      replace hn : n = n' * r := hn
      replace hn1 : n = n1 := hn1
      replace vb_imp : valid_block xs' → (n1 ≤ 0 → r₁ = [] ∧ r₂ = []) ∧
          (0 < n1 → r₁ = take n1 (blocks2bits r₂) ∧ size r₂ = (n1 + r - 1) / r) := vb_imp
      replace not_vb_imp : ¬ valid_block xs' → r₁ = [] ∧ r₂ = [] := not_vb_imp
      refine ⟨?_, ei⟩
      change r₁ = blocks2bits r₂
      by_cases vb : valid_block xs'
      · obtain ⟨le0_imp, gt0_imp⟩ := vb_imp vb
        by_cases le0 : n1 ≤ 0
        · obtain ⟨rfl, rfl⟩ := le0_imp le0; rfl
        · obtain ⟨h1, sz⟩ := gt0_imp (by omega)
          have hsize : size (blocks2bits r₂) = n1 := by
            rw [size_blocks2bits, sz, ← hn1, hn, needed_blocks_prod_r, mul_comm]
          rw [h1, ← hsize, take_size]
      · obtain ⟨rfl, rfl⟩ := not_vb_imp vb; rfl
  -- EC: transitivity
  --       HybridIROEager.f
  --       (={xs, HybridIROEager.mp} /\ n{2} = n{1} * r /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  --        res{1} = bits2blocks res{2} /\ ={HybridIROEager.mp})
  --       (xs{1} = x{2} /\ n{1} = n{2} * r /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1} ==>
  --        res{1} = (blocks2bits res{2}) /\
  --        eager_invar BlockSponge.BIRO.IRO.mp{2} HybridIROEager.mp{1}).
  refine prhlProc_trans_ec ?_ ?_ h₁ h₂
  -- EC: move=> |> &1 &2 ? n_eq inv.
  --     exists HybridIROEager.mp{1} BlockSponge.BIRO.IRO.mp{2} (xs{1}, n{1} * r).
  --     move=> |>; by rewrite n_eq.
  · rintro a₁ g₁ a₂ g₂ ⟨h1, h2, ei⟩
    replace h1 : a₁.1 = a₂.1 := h1
    replace h2 : a₁.2 = a₂.2 := h2
    replace ei : eager_invar (BlockSponge.BIRO.IRO.mp.get g₂) (HybridIROEager.mp.get g₁) := ei
    refine ⟨(a₁.1, a₁.2 * r),
      BlockSponge.BIRO.IRO.mp.set (BlockSponge.BIRO.IRO.mp.get g₂) g₁, ⟨rfl, ?_, rfl, ?_⟩, h1,
      congrArg (· * r) h2, ?_⟩
    · exact (Lens.get_of_disjoint_set HybridIROEager.mp BlockSponge.BIRO.IRO.mp _ g₁).symm
    · exact (congrArg (eager_invar · _) (BlockSponge.BIRO.IRO.mp.set_get g₁ _)).mpr ei
    · exact (congrArg (eager_invar _)
        (Lens.get_of_disjoint_set HybridIROEager.mp BlockSponge.BIRO.IRO.mp _ g₁)).mpr ei
  -- EC: progress; apply blocks2bitsK.
  · rintro r₁ g₁ r' g r₂ g₂ ⟨h1, hmp⟩ ⟨h2, ei⟩
    exact ⟨h1.trans ((congrArg bits2blocks h2).trans (blocks2bitsK r₂)),
      (congrArg (eager_invar _) hmp).mpr ei⟩

end HybridIRO

/-! ## `Sponge_Raise_BlockSponge_f` (EC l. 1922), the second tactic experiment -/

/-- `Perm` (EC's `RP`, a `PRP`) where a `DPRIMITIVE` is expected: its `f`, `fi`. -/
module_subtype (PRP.StrongPRP.PRP (block × capacity)) <: DPRIMITIVE

/-- `Perm` where a `BlockSponge.DPRIMITIVE` is expected. -/
module_subtype (PRP.StrongPRP.PRP (block × capacity)) <: BlockSponge.DPRIMITIVE

/-- `BlockSponge.Sponge(Perm)`, as `stmt_inline` names the callee. -/
noncomputable abbrev BlockSpongePerm : BlockSponge.FUNCTIONALITY :=
  Module.app BlockSponge.Sponge (Perm : BlockSponge.DPRIMITIVE)

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
        · equiv_proc; sim
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
          · equiv_proc; sim
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

/-! ### Footprints of the concrete modules of the final section

EC reads a concrete module's globals off its code; the frame rules ask `fp_le` for a bound on a
concrete callee, which it has for the modules it can read and otherwise takes from the lemmas
stated here (`@[fp_bound]`), each proved by `fp_module`.  They are what the frames of `call H`,
`conseq H` and `proc (I)` below are found from.  Not EC lemmas. -/

omit [SLCommon.Params] [BlockSponge.Params] in
/-- `IRO.f` touches `IRO.mp`. -/
@[fp_bound] theorem fvP_IRO_f : FVP.fvP IRO.f ≤ IRO.mp.footprint := by
  fp_module IRO.mp

omit [BlockSponge.Params] in
/-- `RaiseHybridIRO` has no variables. -/
@[fp_bound] theorem fvP_RaiseHybridIRO :
    FVP.fvP GaudisCrypt.SHA3.Sponge.HybridIRO.RaiseHybridIRO ≤ ⊥ := by
  fp_module

/-- `LowerHybridIRO` has no variables. -/
@[fp_bound] theorem fvP_LowerHybridIRO :
    FVP.fvP GaudisCrypt.SHA3.Sponge.HybridIRO.LowerHybridIRO ≤ ⊥ := by
  fp_module

-- EC's `call (_ : I)` and `proc (I)` on a procedure of the simulator: the first port's rules
attribute [local proc_inv] Indifferentiability.SIMULATOR.call_init
  Indifferentiability.SIMULATOR.call_f Indifferentiability.SIMULATOR.call_fi

/-! ## The main result (EC l. 1913–2146)

`local clone HybridIRO as HIRO`: the clone's variables are those of `HybridIRO` above; they are
fresh for the declared modules in EC, and named in their restrictions here.  `Dist` is restricted
against `BlockSim`: the region form (`with glob R`, E14). -/

section

declare module BlockSim <: BlockSponge.SIMULATOR {-IRO, -BlockSponge.BIRO.IRO,
  -HybridIRO.HybridIROLazy.mp, -HybridIRO.HybridIROEager.mp, -HybridIRO.ERO.RO.m,
  -HybridIRO.ERO.FRO.m} with glob R
declare module Dist <: DISTINGUISHER {-Perm, -R, -IRO, -BlockSponge.BIRO.IRO,
  -HybridIRO.HybridIROLazy.mp, -HybridIRO.HybridIROEager.mp, -HybridIRO.ERO.RO.m,
  -HybridIRO.ERO.FRO.m}

-- (`Dist`'s declaration mentions `R`: kept for the lemmas that do not mention `BlockSim`)
include R

/-- EC's `local lemma RealIndif_Sponge_BlockSponge &m :
Pr[RealIndif(Sponge, Perm, Dist).main() @ &m : res] =
Pr[BlockSponge.RealIndif(BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res]`. -/
theorem RealIndif_Sponge_BlockSponge (m : VariableAssignment) :
    Pr[ RealIndif(Sponge, Perm, Dist).main () @ &m : §res ] =
      Pr[ BlockSponge.RealIndif(BlockSponge.Sponge, Perm, LowerDist(Dist)).main () @ &m :
        §res ] := by
  -- EC: byequiv=> //; proc.
  byequiv; equiv_proc
  -- EC: seq 2 2 : (={glob Dist, glob Perm}); first sim.
  --     (`glob Perm` of the concrete `Perm` spelled out, here and in the call's invariant)
  equiv_seq 2 2 : (={glob Dist, Perm.m, Perm.mi})
  · sim
  --     (E5: `LowerDist(Dist)` wraps EC's alias `Dist(RaiseFun(F), P)` in a call, inlined first)
  stmt_inline{2} 0; stmt_wp
  -- EC: call (_ : ={glob Perm}); first 2 sim.
  --     (as an invariant: the oracles' goals are then EC's, `glob Dist` framed by the rule)
  equiv_call (_ : §Perm.m{1} = §Perm.m{2} ∧ §Perm.mi{1} = §Perm.mi{2})
  · equiv_proc; sim
  · equiv_proc; sim
  -- EC: conseq Sponge_Raise_BlockSponge_f=> //.
  · equiv_conseq Sponge_Raise_BlockSponge_f
    · rintro a₁ g₁ a₂ g₂ ⟨rfl, hm, hmi⟩
      refine ⟨rfl, ?_⟩
      change (Perm.m.footprint ⊔ Perm.mi.footprint).touched_getter.get g₁ =
        (Perm.m.footprint ⊔ Perm.mi.footprint).touched_getter.get g₂
      rw [TacticMisc.touched_getter_eq_iff_of_lens (X := Lens.pair Perm.m Perm.mi)
        (Footprint.lens_pair Perm.m Perm.mi)]
      exact Prod.ext hm hmi
    · rintro r₁ g₁ r₂ g₂ ⟨hr, hg⟩
      have hg' := Eq.mp (TacticMisc.touched_getter_eq_iff_of_lens
        (X := Lens.pair Perm.m Perm.mi) (Footprint.lens_pair Perm.m Perm.mi) g₁ g₂) hg
      exact ⟨hr, congrArg Prod.fst hg', congrArg Prod.snd hg'⟩
  -- EC: auto.
  ec_auto

-- EC's module type `BlockSponge.SIMULATOR` lists the oracles of each procedure (`proc init() :
-- unit { }`, `proc f(_ : block * capacity) : block * capacity { F.f }`, likewise `fi`).  `declare
-- module` has no such lists for a functor with several procedures; the section states them
-- (exception E2 of the first port): each procedure of `BlockSim(F)` is code with a hole for
-- `F.f`, `init` code without holes.
variable (BlockSim_rep : Indifferentiability.SIMULATOR.Representable (block × capacity)
  (List block × ℤ) (List block) BlockSim)

include BlockSim_rep in
/-- EC's `call (_ : true)` on `BlockSim(F).init ~ BlockSim(F').init`: `init` calls no oracle
(`BlockSim_rep`), so the two sides run the same code, which keeps `={glob BlockSim}` (and
`={glob Dist}`, which it does not touch).  Not an EC lemma. -/
theorem BlockSim_init_call (F F' : BlockSponge.DFUNCTIONALITY) :
    equiv[ BlockSim(F).init ~ BlockSim(F').init :
      ={glob Dist, glob BlockSim} ==> ={glob Dist, glob BlockSim} ] :=
  prhlProc_conseq (Indifferentiability.SIMULATOR.call_init _ _ _ IRO.mp BlockSim BlockSim_rep
      (FVP.fvP Dist ⊔ FVP.fvP BlockSim) le_sup_right (by fp_disjoint) (fun _ _ => True) F F')
    (fun _ _ _ _ h => ⟨rfl, h, trivial⟩) (fun _ _ _ _ h => h.2.1)

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO lazy_invar lazy_invar0) in
include BlockSim_rep in
/-- EC's `local lemma Ideal_IRO_Experiment_HybridLazy &m :
Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
Pr[Experiment(HIRO.RaiseHybridIRO(HIRO.HybridIROLazy),
BlockSim(HIRO.LowerHybridIRO(HIRO.HybridIROLazy)), Dist).main() @ &m : res]`. -/
theorem Ideal_IRO_Experiment_HybridLazy (m : VariableAssignment) :
    Pr[ IdealIndif(IRO.asF, RaiseSim(BlockSim), Dist).main () @ &m : §res ] =
      Pr[ Experiment(RaiseHybridIRO(HybridIRO.HybridIROLazy),
        BlockSim(LowerHybridIRO(HybridIRO.HybridIROLazy)), Dist).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc.
  byequiv; equiv_proc
  -- EC: seq 2 2 : (={glob Dist, glob BlockSim} /\ IRO.mp{1} = empty /\
  --       HIRO.HybridIROLazy.mp{2} = empty).
  equiv_seq 2 2 : (={glob Dist, glob BlockSim} ∧ §IRO.mp{1} = FMap.empty ∧
    §HybridIRO.HybridIROLazy.mp{2} = FMap.empty)
  · -- EC: inline*; wp; call (_ : true); auto.
    --     (`BlockSim_init_call`: EC's module type says that `init` calls no oracle)
    simp only [RaiseSim, Module.app_comp]
    stmt_inline*; stmt_wp
    equiv_call (BlockSim_init_call BlockSim Dist BlockSim_rep _ _)
    --     (GAP 3: the calls' discarded results; GAP 14 of `SmartCounter/Gconcl_list.lean`: `glob`
    --     past the initializations)
    simp only [Setter.throwaway_set]
    ec_auto
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
    ec_close
  -- EC: call (_ : ={glob Dist, glob BlockSim} /\ IRO.mp{1} = empty /\
  --       HIRO.HybridIROLazy.mp{2} = empty ==> ={res}).
  --     proc (={glob BlockSim} /\ HIRO.lazy_invar IRO.mp{1} HIRO.HybridIROLazy.mp{2})=> //.
  --     (the two lines are EC's `call (_ : I)`; `RaiseSim(BlockSim, F)` is `BlockSim(LowerFun(F))`)
  simp only [RaiseSim, Module.app_comp]
  equiv_call (_ : ={glob BlockSim} ∧ lazy_invar §IRO.mp{1} §HybridIRO.HybridIROLazy.mp{2})
  -- EC: proc (HIRO.lazy_invar IRO.mp{1} HIRO.HybridIROLazy.mp{2})=> //;
  --       apply HIRO.LowerFun_IRO_HybridIROLazy_f.
  · equiv_proc (lazy_invar §IRO.mp{1} §HybridIRO.HybridIROLazy.mp{2})
    exact HybridIRO.LowerFun_IRO_HybridIROLazy_f
  -- EC: proc (HIRO.lazy_invar IRO.mp{1} HIRO.HybridIROLazy.mp{2})=> //;
  --       apply HIRO.LowerFun_IRO_HybridIROLazy_f.
  · equiv_proc (lazy_invar §IRO.mp{1} §HybridIRO.HybridIROLazy.mp{2})
    exact HybridIRO.LowerFun_IRO_HybridIROLazy_f
  -- EC: by conseq HIRO.IRO_RaiseHybridIRO_HybridIROLazy_f.
  · equiv_conseq_frame HybridIRO.IRO_RaiseHybridIRO_HybridIROLazy_f
  -- EC: progress [-delta]; apply HIRO.lazy_invar0.  (EC's second goal of `proc (I)`: here the
  --     last, with the code before the call)
  --     auto.
  ec_auto
  ec_prep
  exact ⟨lazy_invar0, fun _ _ _ _ h => by rw [h.1]⟩

-- EC's `local module (HybridIRODist : HIRO.HYBRID_IRO_DIST) (HI : HIRO.HYBRID_IRO)` (EC l. 2008)
-- is the first port's `HybridIRODist`, with the section's `BlockSim`, `Dist` as arguments:
-- `HybridIRODist(BlockSim, Dist)`.

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO HybridIROExper) in
include BlockSim_rep in
/-- EC's `local lemma Experiment_HybridIROExper_Lazy &m :
Pr[Experiment(HIRO.RaiseHybridIRO(HIRO.HybridIROLazy),
BlockSim(HIRO.LowerHybridIRO(HIRO.HybridIROLazy)), Dist).main() @ &m : res] =
Pr[HIRO.HybridIROExper(HIRO.HybridIROLazy, HybridIRODist).main() @ &m : res]`. -/
theorem Experiment_HybridIROExper_Lazy (m : VariableAssignment) :
    Pr[ Experiment(RaiseHybridIRO(HybridIRO.HybridIROLazy),
        BlockSim(LowerHybridIRO(HybridIRO.HybridIROLazy)), Dist).main () @ &m : §res ] =
      Pr[ HybridIROExper(HybridIRO.HybridIROLazy, HybridIRODist(BlockSim, Dist)).main ()
        @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline*.
  byequiv; equiv_proc; stmt_inline*
  -- EC: seq 2 2 : (={glob Dist, glob BlockSim, HIRO.HybridIROLazy.mp}).
  equiv_seq 2 2 : (={glob Dist, glob BlockSim, HybridIRO.HybridIROLazy.mp})
  · -- EC: swap{2} 1 1; wp; call (_ : true); auto.
    --     (GAP 14: no `swap` past `init`, whose oracle list is known for its behaviour only;
    --     the call's invariant says what the swap would: `init` keeps the map just emptied)
    stmt_wp
    equiv_call (_ : ={glob Dist, glob BlockSim} ∧ §HybridIRO.HybridIROLazy.mp{2} = FMap.empty)
    simp only [Setter.throwaway_set]
    ec_auto
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
    ec_close
  -- EC: sim.
  --     (GAP 15: `sim` finds no equality set for the call, the precondition's being a `glob`
  --     region and a variable; the call with EC's set, its oracles by `sim`)
  stmt_wp
  equiv_call (_ : ={glob BlockSim} ∧
    §HybridIRO.HybridIROLazy.mp{1} = §HybridIRO.HybridIROLazy.mp{2})
  · equiv_proc (§HybridIRO.HybridIROLazy.mp{1} = §HybridIRO.HybridIROLazy.mp{2})
    equiv_proc; sim
  · equiv_proc (§HybridIRO.HybridIROLazy.mp{1} = §HybridIRO.HybridIROLazy.mp{2})
    equiv_proc; sim
  · have H : equiv[ RaiseHybridIRO(HybridIRO.HybridIROLazy).f (x) ~
        RaiseHybridIRO(HybridIRO.HybridIROLazy).f (x) :
        ={x, HybridIRO.HybridIROLazy.mp} ==> ={res, HybridIRO.HybridIROLazy.mp} ] := by
      equiv_proc; sim
    equiv_conseq_frame H
  ec_auto

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO HybridIROExper) in
include BlockSim_rep in
/-- EC's `local lemma HybridIROExper_Experiment_Eager &m :
Pr[HIRO.HybridIROExper(HIRO.HybridIROEager, HybridIRODist).main() @ &m : res] =
Pr[Experiment(HIRO.RaiseHybridIRO(HIRO.HybridIROEager),
BlockSim(HIRO.LowerHybridIRO(HIRO.HybridIROEager)), Dist).main() @ &m : res]`. -/
theorem HybridIROExper_Experiment_Eager (m : VariableAssignment) :
    Pr[ HybridIROExper(HybridIRO.HybridIROEager, HybridIRODist(BlockSim, Dist)).main ()
        @ &m : §res ] =
      Pr[ Experiment(RaiseHybridIRO(HybridIRO.HybridIROEager),
        BlockSim(LowerHybridIRO(HybridIRO.HybridIROEager)), Dist).main () @ &m : §res ] := by
  -- EC: byequiv=> //; proc; inline*.
  byequiv; equiv_proc; stmt_inline*
  -- EC: seq 2 2 : (={glob Dist, glob BlockSim, HIRO.HybridIROEager.mp}).
  equiv_seq 2 2 : (={glob Dist, glob BlockSim, HybridIRO.HybridIROEager.mp})
  · -- EC: swap{2} 1 1; wp; call (_ : true); auto.
    --     (GAP 14, as in `Experiment_HybridIROExper_Lazy`)
    stmt_wp
    equiv_call (_ : ={glob Dist, glob BlockSim} ∧ §HybridIRO.HybridIROEager.mp{1} = FMap.empty)
    simp only [Setter.throwaway_set]
    ec_auto
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
    ec_close
  -- EC: sim.
  --     (GAP 15, as in `Experiment_HybridIROExper_Lazy`)
  stmt_wp
  equiv_call (_ : ={glob BlockSim} ∧
    §HybridIRO.HybridIROEager.mp{1} = §HybridIRO.HybridIROEager.mp{2})
  · equiv_proc (§HybridIRO.HybridIROEager.mp{1} = §HybridIRO.HybridIROEager.mp{2})
    equiv_proc; sim
  · equiv_proc (§HybridIRO.HybridIROEager.mp{1} = §HybridIRO.HybridIROEager.mp{2})
    equiv_proc; sim
  · have H : equiv[ RaiseHybridIRO(HybridIRO.HybridIROEager).f (x) ~
        RaiseHybridIRO(HybridIRO.HybridIROEager).f (x) :
        ={x, HybridIRO.HybridIROEager.mp} ==> ={res, HybridIRO.HybridIROEager.mp} ] := by
      equiv_proc; sim
    equiv_conseq_frame H
  ec_auto

-- EC reads `HybridIRODist`'s globals off its code (for `HybridIROExper_Lazy_Eager`'s restriction)
attribute [local fp_bound] GaudisCrypt.SHA3.Sponge.fvP_HybridIRODist_le

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO HybridIROExper) in
include BlockSim_rep in
/-- EC's `local lemma Experiment_Hybrid_Lazy_Eager &m :
Pr[Experiment(HIRO.RaiseHybridIRO(HIRO.HybridIROLazy),
BlockSim(HIRO.LowerHybridIRO(HIRO.HybridIROLazy)), Dist).main() @ &m : res] =
Pr[Experiment(HIRO.RaiseHybridIRO(HIRO.HybridIROEager),
BlockSim(HIRO.LowerHybridIRO(HIRO.HybridIROEager)), Dist).main() @ &m : res]`.

`HIRO.HybridIROExper_Lazy_Eager` is applied to `HybridIRODist`, which satisfies its restriction:
EC checks that when the lemma is applied, here it is the instance stated first. -/
theorem Experiment_Hybrid_Lazy_Eager (m : VariableAssignment) :
    Pr[ Experiment(RaiseHybridIRO(HybridIRO.HybridIROLazy),
        BlockSim(LowerHybridIRO(HybridIRO.HybridIROLazy)), Dist).main () @ &m : §res ] =
      Pr[ Experiment(RaiseHybridIRO(HybridIRO.HybridIROEager),
        BlockSim(LowerHybridIRO(HybridIRO.HybridIROEager)), Dist).main () @ &m : §res ] := by
  -- EC: by rewrite (Experiment_HybridIROExper_Lazy &m)
  --       (HIRO.HybridIROExper_Lazy_Eager HybridIRODist &m)
  --       (HybridIROExper_Experiment_Eager &m).
  haveI : Module.Declared (HybridIRODist BlockSim Dist)
      (HybridIRO.HybridIROEager.mp.footprint ⊔ HybridIRO.HybridIROLazy.mp.footprint ⊔
        HybridIRO.ERO.RO.m.footprint ⊔ HybridIRO.ERO.FRO.m.footprint) :=
    ⟨by fp_finite, by fp_disjoint⟩
  rw [Experiment_HybridIROExper_Lazy BlockSim Dist BlockSim_rep m,
    HybridIRO.HybridIROExper_Lazy_Eager (HybridIRODist BlockSim Dist) m,
    HybridIROExper_Experiment_Eager BlockSim Dist BlockSim_rep m]

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO eager_invar) in
/-- EC's `local lemma RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f :
equiv[HIRO.RaiseHybridIRO(HIRO.HybridIROEager).f ~ RaiseFun(BlockSponge.BIRO.IRO).f :
={bs, n} /\ ={glob BlockSim} /\
HIRO.eager_invar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1} ==>
={res} /\ ={glob BlockSim} /\
HIRO.eager_invar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1}]`. -/
theorem RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f :
    equiv[ RaiseHybridIRO(HybridIRO.HybridIROEager).f (x) ~
        RaiseFun(BlockSponge.BIRO.IRO.asF).f (x) :
      ={x, glob BlockSim} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIRO.HybridIROEager.mp{1} ==>
      ={res, glob BlockSim} ∧
        eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIRO.HybridIROEager.mp{1} ] := by
  -- EC: proc=> /=.
  equiv_proc
  --     (the one parameter `x` assigned to `bs`, `n` first; the first port's view of
  --     `BlockSponge.BIRO.IRO` as a functionality opened, so that the callee is `IRO.f`)
  stmt_sp
  simp only [BlockSponge.BIRO.IRO.asF, Indifferentiability.FUNCTIONALITY.view,
    SHA3.Indifferentiability.DFUNCTIONALITY.f.mk_simp,
    SHA3.Indifferentiability.FUNCTIONALITY.f.mk_simp]
  -- EC: exists* n{1}; elim*=> n'.
  --     exists* (pad2blocks bs{2}); elim*=> xs2.
  equiv_exists* §n{1}, pad2blocks §bs{2}
  intro (n' : ℤ) (xs2 : List block)
  -- EC: call (HIRO.HybridIROEager_f_BlockIRO_f n' xs2).
  equiv_call (HybridIRO.HybridIROEager_f_BlockIRO_f n' xs2)
  -- EC: skip=> |> &1 &2 ? res1 res2 mp1 mp2 ? vb_imp not_vb_imp.
  ec_auto
  rintro x₁ tg₁ mp₁ bs₁ n₁ imp₁ x₂ tg₂ imp₂ bs₂ n₂ mp₂ ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, hinv⟩, rfl⟩, hx⟩, rfl⟩, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  refine ⟨⟨rfl, rfl, rfl, rfl, hinv⟩, ?_⟩
  rintro res1 g₁ res2 g₂ ⟨-, hg₁⟩ ⟨-, hg₂⟩ ⟨hinv', vb_imp, not_vb_imp⟩
  refine ⟨⟨?_, hg₁.trans hg₂.symm⟩, hinv'⟩
  -- EC: case: (valid_block (pad2blocks bs{2}))=> [vb | not_vb].
  by_cases vb : valid_block (pad2blocks bs₂)
  · -- EC: have [le0_n2_imp gt0_n2_imp] := vb_imp vb.
    obtain ⟨le0_n2_imp, gt0_n2_imp⟩ := vb_imp vb
    -- EC: case: (n' <= 0)=> [le0_n' /# | not_le0_n'].
    by_cases le0_n' : n₂ ≤ 0
    · obtain ⟨rfl, rfl⟩ := le0_n2_imp le0_n'
      exact (take_le0 _ _ le0_n').symm
    -- EC: have gt0_n' : 0 < n' by smt().
    --     by have [-> _] := gt0_n2_imp gt0_n'.
    · have gt0_n' : 0 < n₂ := by omega
      exact (gt0_n2_imp gt0_n').1
  -- EC: have [-> ->] := not_vb_imp not_vb; by rewrite blocks2bits_nil.
  · obtain ⟨rfl, rfl⟩ := not_vb_imp vb
    rw [blocks2bits_nil]; simp [take]

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO eager_invar eager_invar0) in
include BlockSim_rep in
/-- EC's `local lemma Experiment_HybridEager_Ideal_BlockIRO &m :
Pr[Experiment(HIRO.RaiseHybridIRO(HIRO.HybridIROEager),
BlockSim(HIRO.LowerHybridIRO(HIRO.HybridIROEager)), Dist).main() @ &m : res] =
Pr[BlockSponge.IdealIndif(BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res]`. -/
theorem Experiment_HybridEager_Ideal_BlockIRO (m : VariableAssignment) :
    Pr[ Experiment(RaiseHybridIRO(HybridIRO.HybridIROEager),
        BlockSim(LowerHybridIRO(HybridIRO.HybridIROEager)), Dist).main () @ &m : §res ] =
      Pr[ BlockSponge.IdealIndif(BlockSponge.BIRO.IRO.asF, BlockSim, LowerDist(Dist)).main ()
        @ &m : §res ] := by
  -- EC: byequiv=> //; proc.
  byequiv; equiv_proc
  -- EC: seq 2 2 :
  --       (={glob Dist, glob BlockSim} /\ HIRO.HybridIROEager.mp{1} = empty /\
  --        BlockSponge.BIRO.IRO.mp{2} = empty).
  equiv_seq 2 2 : (={glob Dist, glob BlockSim} ∧ §HybridIRO.HybridIROEager.mp{1} = FMap.empty ∧
    §BlockSponge.BIRO.IRO.mp{2} = FMap.empty)
  · -- EC: inline*; wp; call (_ : true); auto.
    stmt_inline*; stmt_wp
    equiv_call (BlockSim_init_call BlockSim Dist BlockSim_rep _ _)
    --     (GAP 3, and GAP 14 of `SmartCounter/Gconcl_list.lean`, as in
    --     `Ideal_IRO_Experiment_HybridLazy`)
    simp only [Setter.throwaway_set]
    ec_auto
    simp (disch := fp_disjoint) only [GaudisCrypt.touched_set_of_le_compl]
    ec_close
  -- EC: call (_ : ={glob Dist, glob BlockSim} /\ HIRO.HybridIROEager.mp{1} = empty /\
  --       BlockSponge.BIRO.IRO.mp{2} = empty ==> ={res}).
  --     proc (={glob BlockSim} /\
  --       HIRO.eager_invar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1})=> //.
  --     (the two lines are EC's `call (_ : I)`; E5: `LowerDist(Dist)` wraps EC's alias in a call,
  --     inlined first)
  stmt_inline{2} 0; stmt_wp
  equiv_call (_ : ={glob BlockSim} ∧
    eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIRO.HybridIROEager.mp{1})
  -- EC: proc (HIRO.eager_invar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1})=> //;
  --       conseq HIRO.HybridIROEager_BlockIRO_f=> //.
  · equiv_proc (eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIRO.HybridIROEager.mp{1})
    equiv_conseq_frame HybridIRO.HybridIROEager_BlockIRO_f
  -- EC: proc (HIRO.eager_invar BlockSponge.BIRO.IRO.mp{2} HIRO.HybridIROEager.mp{1})=> //;
  --       conseq HIRO.HybridIROEager_BlockIRO_f=> //.
  · equiv_proc (eager_invar §BlockSponge.BIRO.IRO.mp{2} §HybridIRO.HybridIROEager.mp{1})
    equiv_conseq_frame HybridIRO.HybridIROEager_BlockIRO_f
  -- EC: conseq RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f=> //.
  · equiv_conseq_frame (RaiseHybridIRO_HybridIROEager_RaiseFun_BlockIRO_f BlockSim)
  -- EC: progress [-delta]; apply HIRO.eager_invar0.  (EC's second goal of `proc (I)`: here the
  --     last, with the code before the call)
  --     auto.
  ec_auto
  ec_prep
  exact ⟨eager_invar0, fun _ _ _ _ h => by rw [h.1]⟩

open GaudisCrypt.SHA3.Sponge.HybridIRO (RaiseHybridIRO LowerHybridIRO) in
include BlockSim_rep in
/-- EC's `local lemma IdealIndif_IRO_BlockIRO &m :
Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res] =
Pr[BlockSponge.IdealIndif(BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main () @ &m : res]`. -/
theorem IdealIndif_IRO_BlockIRO (m : VariableAssignment) :
    Pr[ IdealIndif(IRO.asF, RaiseSim(BlockSim), Dist).main () @ &m : §res ] =
      Pr[ BlockSponge.IdealIndif(BlockSponge.BIRO.IRO.asF, BlockSim, LowerDist(Dist)).main ()
        @ &m : §res ] := by
  -- EC: by rewrite (Ideal_IRO_Experiment_HybridLazy &m) (Experiment_Hybrid_Lazy_Eager &m)
  --       (Experiment_HybridEager_Ideal_BlockIRO &m).
  rw [Ideal_IRO_Experiment_HybridLazy BlockSim Dist BlockSim_rep m,
    Experiment_Hybrid_Lazy_Eager BlockSim Dist BlockSim_rep m,
    Experiment_HybridEager_Ideal_BlockIRO BlockSim Dist BlockSim_rep m]

include BlockSim_rep in
/-- EC's `lemma conclu &m :
`|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m : res] -
Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
`|Pr[BlockSponge.RealIndif(BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
Pr[BlockSponge.IdealIndif(BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|`. -/
theorem conclu (m : VariableAssignment) :
    |Pr[ RealIndif(Sponge, Perm, Dist).main () @ &m : §res ] -
        Pr[ IdealIndif(IRO.asF, RaiseSim(BlockSim), Dist).main () @ &m : §res ]| =
      |Pr[ BlockSponge.RealIndif(BlockSponge.Sponge, Perm, LowerDist(Dist)).main () @ &m : §res ] -
        Pr[ BlockSponge.IdealIndif(BlockSponge.BIRO.IRO.asF, BlockSim, LowerDist(Dist)).main ()
          @ &m : §res ]| := by
  -- EC: by rewrite (RealIndif_Sponge_BlockSponge &m) (IdealIndif_IRO_BlockIRO &m).
  rw [RealIndif_Sponge_BlockSponge (R := R) Dist m,
    IdealIndif_IRO_BlockIRO BlockSim Dist BlockSim_rep m]

end

/-! ## Conclusion (EC l. 2148–2163) -/

section

declare module BlockSim <: BlockSponge.SIMULATOR {-IRO, -BlockSponge.BIRO.IRO,
  -HybridIRO.HybridIROLazy.mp, -HybridIRO.HybridIROEager.mp, -HybridIRO.ERO.RO.m,
  -HybridIRO.ERO.FRO.m} with glob R
declare module Dist <: DISTINGUISHER {-Perm, -R, -IRO, -BlockSponge.BIRO.IRO,
  -HybridIRO.HybridIROLazy.mp, -HybridIRO.HybridIROEager.mp, -HybridIRO.ERO.RO.m,
  -HybridIRO.ERO.FRO.m}

include R

/-- EC's `lemma conclusion (BlockSim <: BlockSponge.SIMULATOR{-IRO, -BlockSponge.BIRO.IRO})
(Dist <: DISTINGUISHER{-Perm, -BlockSim, -IRO, -BlockSponge.BIRO.IRO}) &m :
`|Pr[RealIndif(Sponge, Perm, Dist).main() @ &m : res] -
Pr[IdealIndif(IRO, RaiseSim(BlockSim), Dist).main() @ &m : res]| =
`|Pr[BlockSponge.RealIndif(BlockSponge.Sponge, Perm, LowerDist(Dist)).main() @ &m : res] -
Pr[BlockSponge.IdealIndif(BlockSponge.BIRO.IRO, BlockSim, LowerDist(Dist)).main() @ &m : res]|`.

The restrictions also name the variables of the theory `HybridIRO` and of its local clone `ERO`
(fresh in EC), `Dist`'s restriction against `BlockSim` is the region form (`with glob R`, E14),
and the oracle lists of EC's module type `SIMULATOR` are the hypothesis `BlockSim_rep` (E2). -/
theorem conclusion
    (BlockSim_rep : Indifferentiability.SIMULATOR.Representable (block × capacity)
      (List block × ℤ) (List block) BlockSim) (m : VariableAssignment) :
    |Pr[ RealIndif(Sponge, Perm, Dist).main () @ &m : §res ] -
        Pr[ IdealIndif(IRO.asF, RaiseSim(BlockSim), Dist).main () @ &m : §res ]| =
      |Pr[ BlockSponge.RealIndif(BlockSponge.Sponge, Perm, LowerDist(Dist)).main () @ &m : §res ] -
        Pr[ BlockSponge.IdealIndif(BlockSponge.BIRO.IRO.asF, BlockSim, LowerDist(Dist)).main ()
          @ &m : §res ]| := by
  -- EC: by apply (conclu BlockSim Dist &m).
  exact conclu BlockSim Dist BlockSim_rep m

end

end GaudisCrypt.SHA3.Pilot.Sponge
