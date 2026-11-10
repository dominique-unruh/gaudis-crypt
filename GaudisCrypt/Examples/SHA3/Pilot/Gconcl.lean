import GaudisCrypt.Examples.SHA3.Pilot.Gext
import GaudisCrypt.Examples.SHA3.SmartCounter.Gconcl

/-!
# Conclusion of the squeezeless sponge proof (EasyCrypt `proof/smart_counter/Gconcl.ec`) —
EC-fidelity port

The equivalences `G2_G3`, `G3_G4`, `G4_Ideal` in EC's scripts, over the old port's declarations of
`IF`, `S`, `G3`, `G4` (`SmartCounter/Gconcl.lean`), as `Pilot/Gext.lean`.

Translation:
* EC's local `G3(RO)`, `G4(RO)` take `D` as a Lean parameter (the section's `D`): `G3(D, F.LRO)`
  for EC's `G3(F.LRO)`;
* `declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S, -Redo}` with the section's
  `local clone import Gext as Gext0`: the clone's modules are fresh for `D` in EC, here `D`'s
  restriction names them (`G1`, `FRO.m`).
-/

/-! Gap list (batch-fix later, see TRANSFER_SKILL.md §1.6):
* GAP 1: EC's `sim` goes into calls of different concrete procedures (`G4.S(F.LRO).f` against
  `S(IF).f`); ours stops there: `stmt_inline*` first.
* GAP 2: the one-sided `equiv_while{i}` has no frame of the variables the loop keeps (the
  two-sided `while` has, `Logic/ECWhileRel.lean`): they go into the invariant.
-/

namespace GaudisCrypt.SHA3.Pilot.Gconcl

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet GaudisCrypt.EC.PROM GaudisCrypt.SHA3.Common
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix GaudisCrypt.SHA3.ConcreteF
open GaudisCrypt.SHA3.Handle
open GaudisCrypt.SHA3.Gext (G2 G2.M G2.S Eager Eager.main2 RRO)
open GaudisCrypt.SHA3.Gconcl (IF S G3 G3.M G3.S G4 G4.C G4.S)

variable [SLCommon.Params]

section

declare module D <: DISTINGUISHER {-C, -Perm, -F.RO, -F.FRO, -S.m, -S.mi, -S.paths, -Redo, -G1,
  -FRO.m}

set_option maxHeartbeats 4000000 in
/-- EC's `local equiv G4_Ideal : G4(F.LRO).distinguish ~ IdealIndif(IF,S,DRestr(D)).main :
={glob D} ==> ={res}`. -/
theorem G4_Ideal : equiv[ G4(D, F.LRO).distinguish ~ IdealIndif(IF, S, DRestr(D)).main :
    ={glob D} ==> ={res} ] := by
  -- EC: proc;inline *;wp.
  equiv_proc; stmt_inline*; stmt_wp
  -- EC: call (_: ={C.c,C.queries,F.RO.m} /\ G1.m{1}=S.m{2} /\ G1.mi{1}=S.mi{2} /\
  --          G1.paths{1}=S.paths{2}).
  equiv_call (_ : ={C.c, C.queries, F.RO.m} ∧ §G1.m{1} = §S.m{2} ∧ §G1.mi{1} = §S.mi{2} ∧
    §G1.paths{1} = §S.paths{2})
  -- EC: + by sim. + by sim.
  --     (GAP 1: our `sim` stops at calls of different procedures: inlined first; what it leaves
  --     before the code, by `auto_close`)
  · equiv_proc; stmt_inline*; sim; auto_close
  · equiv_proc; stmt_inline*; sim; auto_close
  -- EC: + proc;sp;if=>//;auto;if=>//;auto.
  · equiv_proc; stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    stmt_sp; stmt_if
    · auto_close
    on_goals -1 => equiv_auto
    -- EC: call (_: ={F.RO.m});2:by auto.
    stmt_wp; equiv_call (_ : ={F.RO.m})
    on_goals 2 => (equiv_auto; auto_close)
    -- EC: inline F.LRO.get F.FRO.sample;wp 7 2;sim.
    equiv_proc; stmt_inline*; stmt_wp 7 2; sim
    -- EC: by while{1} (true) (size p - i){1};auto;1:inline*;auto=>/#.
    --     (GAP 2: our one-sided `while` has no frame of what the loop keeps: `p{1} = x{2}` and
    --     `={F.RO.m}` in the invariant, EC's `true`)
    equiv_while{1} (§p{1} = §x{2} ∧ §F.RO.m{1} = §F.RO.m{2}) ((size §p{1} - §i{1}).toNat)
    · while_ll_phoare
      intro σ₂
      phoare_auto
    · intro σ₂ k
      hoare_auto
    · auto_progress
    · equiv_auto
  -- EC: by auto.
  · equiv_auto; auto_close

end

end GaudisCrypt.SHA3.Pilot.Gconcl
