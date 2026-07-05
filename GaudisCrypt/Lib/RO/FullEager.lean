import GaudisCrypt.Logic.EagerRhl
import GaudisCrypt.Lib.RO.GlobTransfer

/-!
# FullEager: the lazy = eager theorem, PROM-style

An independent, EasyCrypt-style derivation of the whole-game lazy = eager
coupling, after the `FullEager` subtheory of EasyCrypt's `PROM.ec`.  Where the
existing proof (`TransferInstantiate.lean` + `GlobTransfer.lean`) is organised
around the distributional transfer relation, this file derives the same headline
as a **chain of pRHL judgments** in the eager calculus
(`GaudisCrypt.Logic.EagerRhl`):

| PROM.ec (`FullEager`)                  | here                                   |
|----------------------------------------|----------------------------------------|
| `resample` (`Iter` over `Unknown`)      | `convert` (one uniform function draw)  |
| `eager_get`, per-op eager lemmas        | `eager_query`, `eager_init`            |
| `eager_D` (`eager proc` on abstract `D`)| `eager_call`                           |
| `D <: FRO_Distinguisher {-FRO}`         | `hdisj : FVP.fvP_proc A ≤ (RO.footprint)ᶜ` |
| `RO_LRO : ={glob D} ==> ={res, glob D}` | `RO_LRO_glob`                          |

**Kernel discipline.**  No step of the headline derivation inducts on `A`.  The
only adversary-crossing step is the calculus rule `eager_call`, whose soundness
(like EasyCrypt's `eager proc`, which is a trusted kernel rule justified by
induction in the metatheory) is a once-and-for-all induction over the adversary
syntax — here imported from `transfer_instantiate_of_fvP` through the
equality-coupling bridge.  A native `eagerR`-level re-run of that induction
would be a drop-in replacement.
-/

namespace GaudisCrypt.Lib.RO.Instantiate

open GaudisCrypt.Language.Lens
open GaudisCrypt.Language.Semantics
open GaudisCrypt.Language.Programs

/-! ## Per-operation eager lemmas (PROM's `eager_init`, `eager_get`) -/

/-- **Eager init**: `lazy_init; convert ~ convert; random_oracle_init` — the
    initialisations swap with the resampler.  (PROM's `eager_init`.) -/
theorem eager_init :
    ProgramDenotation.eagerR convert (fun σ₁ σ₂ : state => σ₁ = σ₂)
      lazy_init random_oracle_init (fun u v : Unit × state => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy convert _ _).mpr
    ProgramDenotation.transfer_lazy_init

/-- **Eager query**: `lazy_query x; convert ~ convert; random_oracle_query x` —
    a lazy query followed by the resampler is an eager query preceded by it.
    (PROM's `eager_get`.) -/
theorem eager_query (x : input) :
    ProgramDenotation.eagerR convert (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (lazy_query x) (random_oracle_query x)
      (fun u v : output × state => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy convert _ _).mpr
    (ProgramDenotation.transfer_lazy_query x)

/-! ## The abstract-adversary rule (PROM's `eager_D`) -/

/-- **`eager call` on the abstract adversary**: the two instantiations of `A`
    swap with the resampler, given only that `A`'s footprint avoids the oracle.
    This is the analogue of EasyCrypt's `eager proc` applied to the abstract
    distinguisher — a calculus rule whose soundness is the once-and-for-all
    induction over the adversary syntax (imported through the equality-coupling
    bridge), never re-run by clients. -/
theorem eager_call {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.eagerR convert (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (procedureDenotation (A.instantiate RO_lazy) args)
      (procedureDenotation (A.instantiate RO_eager) args)
      (fun u v : sig.ret × state => u = v) :=
  (ProgramDenotation.eagerR_eq_iff_transferBy convert _ _).mpr
    (ProgramDenotation.transfer_instantiate_of_fvP A args
      (fvP_proc_le_roLift_compl A hdisj))

/-! ## The headline (PROM's `RO_LRO`) -/

/-- **`RO_LRO` with `={glob A}`**: the whole lazy and eager games couple from
    `={glob A}` initial states with equal results and `={glob A}` final states —
    derived as a chain of pRHL judgments:

    1. `eagerR` for the whole game: `eagerR_bind eager_init eager_call`;
    2. the leading `convert` is swallowed by `random_oracle_init`
       (`convert_bind_random_oracle_init_bind`, chained through the bridge);
    3. absorb into a direct coupling recording `={glob A}` on the finals
       (`prhl2_of_lossless_tail_proj`, with `convert` lossless and glob-invariant);
    4. relax the precondition to `={glob A}` by `prhl2.trans` with the
       same-program self-coupling (`glob_self_coupling_lazy`), and `conseq`. -/
theorem RO_LRO_glob {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => u.1 = v.1 ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) := by
  -- 1. the whole-game eager judgment
  have h_eager : ProgramDenotation.eagerR convert (fun σ₁ σ₂ : state => σ₁ = σ₂)
      (lazy_init >>= fun _ => procedureDenotation (A.instantiate RO_lazy) args)
      (random_oracle_init >>= fun _ => procedureDenotation (A.instantiate RO_eager) args)
      (fun u v : sig.ret × state => u = v) :=
    ProgramDenotation.eagerR_bind eager_init (fun _ => eager_call A args hdisj)
  -- 2. the leading `convert` is swallowed by the eager initialisation
  have h_eq : ((lazy_init >>= fun _ => procedureDenotation (A.instantiate RO_lazy) args)
        >>= fun a => convert >>= fun _ => pure a)
      = (random_oracle_init >>= fun _ =>
          procedureDenotation (A.instantiate RO_eager) args) :=
    ((ProgramDenotation.eagerR_eq_iff_transferBy convert _ _).mp h_eager).trans
      (convert_bind_random_oracle_init_bind _)
  -- 3. absorb into a direct coupling, recording `={glob A}` on the finals
  have h_produce := ProgramDenotation.prhl2_of_lossless_tail_proj (FVP.glob A).get
    convert_lossless
    (convert_satisfies_of_ro_invariant (FVP.glob A).get (glob_ro_set_invariant A hdisj))
    h_eq
  -- 4. relax the precondition to `={glob A}` and land the post
  have h12 := ProgramDenotation.prhl2.trans
    (glob_self_coupling_lazy A args hdisj) h_produce
  refine h12.conseq (fun σ₁ σ₃ h => ⟨σ₃, h, rfl⟩) ?_
  rintro u v ⟨w, hw1, hw2⟩
  exact ⟨hw1.1.trans hw2.1, hw1.2.trans hw2.2⟩

/-- `Win`-form of `RO_LRO_glob`: any event decided by `A`'s output transfers
    between the lazy and eager games, with `={glob A}` throughout. -/
theorem RO_LRO_win {sig : ProcedureSignature}
    (A : ProcedureWithHoles roHoles sig) (args : sig.ParamType) (Win : sig.ret → Prop)
    (hdisj : FVP.fvP_proc A ≤ (random_oracle_state.footprint)ᶜ) :
    ProgramDenotation.prhl2
      (fun σ₁ σ₂ : state => (FVP.glob A).get σ₁ = (FVP.glob A).get σ₂)
      (do lazy_init; procedureDenotation (A.instantiate RO_lazy) args)
      (do random_oracle_init; procedureDenotation (A.instantiate RO_eager) args)
      (fun u v => (Win u.1 ↔ Win v.1) ∧ (FVP.glob A).get u.2 = (FVP.glob A).get v.2) :=
  (RO_LRO_glob A args hdisj).conseq
    (fun _ _ h => h) (fun _ _ h => ⟨by rw [h.1], h.2⟩)

end GaudisCrypt.Lib.RO.Instantiate
