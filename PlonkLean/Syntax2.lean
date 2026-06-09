import Mathlib.Data.List.AList
import Mathlib.Logic.Equiv.Defs
import Metatheory.STLCext.Normalization
import Metatheory.STLCext.Confluence
import PlonkLean.Language.Programs
import PlonkLean.Language.Modules


namespace Language.Modules

open Language.Programs
open Language.Modules
open scoped Language.Modules

variable [ProgramSpec]



/-- The STLC translation of a procedure-with-holes determines the procedure (and its
    hole/return signatures). -/
theorem ProcedureWithHoles.toSTLC_inj {holes holes' : HoleSigs} {sig sig' : ProcedureSignature}
    {p : ProcedureWithHoles holes sig} {p' : ProcedureWithHoles holes' sig'} :
    ProcedureWithHoles.toSTLC p = ProcedureWithHoles.toSTLC p' → holes = holes' ∧ sig = sig' ∧ p ≍ p' := by
  intro h
  simp only [ProcedureWithHoles.toSTLC] at h
  rw [Metatheory.STLCext.Term.func.injEq] at h
  obtain ⟨-, -, hdata, -⟩ := h
  -- hdata : (⟨holes, sig, p⟩ : FuncData) = ⟨holes', sig', p'⟩
  injection hdata with h1 h2
  subst h1
  injection (eq_of_heq h2) with h3 h4
  subst h3
  exact ⟨rfl, rfl, h4⟩


lemma HoleSigs.toList_ne_nil {holes : HoleSigs} (h : holes.NonEmpty) : holes.toList ≠ [] := by
  cases holes with
  | empty => exact absurd h (by simp [HoleSigs.NonEmpty])
  | append Γ s => simp [HoleSigs.toList]

/-- Build the proc-tuple argument (a right-nested `.pair` of `.proc`s) from a tuple of
    procedures — the inverse of `IsProcTuple.toArgs`. -/
def procTupleOfArgs {Δ : ModuleContext} : (sigs : List ProcedureSignature) → sigs ≠ [] →
    typeListToProdGeneric Prod PUnit (sigs.map Procedure) →
    ModuleExpression Δ
      (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc))
  | [],           h, _         => absurd rfl h
  | [_],          _, p         => .proc p
  | _ :: s :: ss, _, (p, rest) => .pair (.proc p) (procTupleOfArgs (s :: ss) (by simp) rest)

/-- The erasure of a proc-tuple built by `procTupleOfArgs` is a `BasicTerm` (so it can drive
    the STLC `funcApp` reduction). -/
lemma isBasicType_procTupleOfArgs {Δ : ModuleContext} : (sigs : List ProcedureSignature) →
    (hne : sigs ≠ []) → (args : typeListToProdGeneric Prod PUnit (sigs.map Procedure)) →
    Metatheory.STLCext.Term.isBasicType
      (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc)).toSTLC
      (ModuleExpression.toSTLC (procTupleOfArgs (Δ := Δ) sigs hne args))
  | [], hne, _ => absurd rfl hne
  | [_], _, p => by
      simp [procTupleOfArgs, ModuleExpression.toSTLC, ModuleType.toSTLC, typeListToProdGeneric,
        List.map, Metatheory.STLCext.Term.isBasicType]
  | _ :: s :: ss, _, (p, rest) => by
      simp only [procTupleOfArgs, ModuleExpression.toSTLC, ModuleType.toSTLC, List.map,
        typeListToProdGeneric, Metatheory.STLCext.Term.isBasicType]
      exact ⟨trivial, isBasicType_procTupleOfArgs (Δ := Δ) (s :: ss) (by simp) rest⟩

/-- Erasure to STLC ignores a type-cast of the module expression. -/
lemma ModuleExpression.toSTLC_cast {Δ : ModuleContext} {T T' : ModuleType} (h : T = T')
    (m : ModuleExpression Δ T) :
    ModuleExpression.toSTLC (h ▸ m) = ModuleExpression.toSTLC m := by cases h; rfl








-- TODO move to Modules.lean
theorem cbvReductionStep_is_reductionStep (m : ModuleExpression Γ T) (nn : ¬ Normal m) :
    ReductionStep m (cbvReductionStep m nn) :=
sorry

omit [ProgramSpec] in
private lemma ModuleContextIdx.toNat_inj' {Γ : ModuleContext} :
  ∀ {T1 T2 : ModuleType} (r1 : ModuleContextIdx Γ T1) (r2 : ModuleContextIdx Γ T2),
    r1.toNat = r2.toNat → T1 = T2 ∧ HEq r1 r2
  | _, _, .zero,    .zero,    _ => ⟨rfl, HEq.rfl⟩
  | _, _, .zero,    .succ _,  h => by simp [ModuleContextIdx.toNat] at h
  | _, _, .succ _,  .zero,    h => by simp [ModuleContextIdx.toNat] at h
  | _, _, .succ r1', .succ r2', h => by
      simp only [ModuleContextIdx.toNat, Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at h
      obtain ⟨hT, hr⟩ := ModuleContextIdx.toNat_inj' r1' r2' h
      subst hT
      exact ⟨rfl, heq_of_eq (congrArg ModuleContextIdx.succ (eq_of_heq hr))⟩

omit [ProgramSpec] in
private lemma ModuleContextIdx.toNat_inj {Γ : ModuleContext} {T : ModuleType} :
  ∀ (r r' : ModuleContextIdx Γ T), r.toNat = r'.toNat → r = r'
  | .zero,   .zero,    _ => rfl
  | .zero,   .succ _,  h => by simp [ModuleContextIdx.toNat] at h
  | .succ _, .zero,    h => by simp [ModuleContextIdx.toNat] at h
  | .succ r, .succ r', h =>
       congrArg ModuleContextIdx.succ (ModuleContextIdx.toNat_inj r r' (Nat.succ.inj h))

def ModuleExpression.erasedEqual
  (m : ModuleExpression Γ T) (m' : ModuleExpression Γ' T') : Prop := match m, m' with
  | @ModuleExpression.proc _ _ sig p, @ModuleExpression.proc _ _ sig' p' => sig = sig' ∧ p ≍ p'
  | @ModuleExpression.procHoles _ _ holes sig _ p,
    @ModuleExpression.procHoles _ _ holes' sig' _ p' => holes = holes' ∧ sig = sig' ∧ p ≍ p'
  | .var r, .var r' => r.toNat = r'.toNat
  | .app f a, .app f' a' => ModuleExpression.erasedEqual f f' ∧ ModuleExpression.erasedEqual a a'
  | .fst e, .fst e' => ModuleExpression.erasedEqual e e'
  | .snd e, .snd e' => ModuleExpression.erasedEqual e e'
  | .pair a b, .pair a' b' => ModuleExpression.erasedEqual a a' ∧ ModuleExpression.erasedEqual b b'
  | .abs body, .abs body' => ModuleExpression.erasedEqual body body'
  | .unit, .unit => True
  | _, _ => False

private theorem ModuleType.toSTLC_injective {a b : ModuleType}
    (h : a.toSTLC = b.toSTLC) : a = b := by
  induction a generalizing b with
  | proc s => cases b <;> simp_all [ModuleType.toSTLC]
  | unit => cases b <;> simp_all [ModuleType.toSTLC]
  | arr A B ihA ihB =>
      cases b with
      | arr A' B' =>
          simp only [ModuleType.toSTLC, Metatheory.STLCext.Ty.arr.injEq] at h; rw [ihA h.1, ihB h.2]
      | _ => simp [ModuleType.toSTLC] at h
  | prod A B ihA ihB =>
      cases b with
      | prod A' B' =>
          simp only [ModuleType.toSTLC, Metatheory.STLCext.Ty.prod.injEq] at h; rw [ihA h.1, ihB h.2]
      | _ => simp [ModuleType.toSTLC] at h

omit [ProgramSpec] in
private theorem typeListToProd_proc_inj {l1 l2 : List ProcedureSignature}
      (h : typeListToProdGeneric ModuleType.prod ModuleType.unit (l1.map ModuleType.proc)
        = typeListToProdGeneric ModuleType.prod ModuleType.unit (l2.map ModuleType.proc)) :
     l1 = l2 := by
  revert l2 h
  induction l1 with
  | nil => intro l2 h; cases l2 with
    | nil => rfl
    | cons b bs => cases bs <;> simp_all [typeListToProdGeneric, List.map]
  | cons a as iha => intro l2 h; cases l2 with
    | nil => cases as <;> simp_all [typeListToProdGeneric, List.map]
    | cons b bs =>
        cases as with
        | nil => cases bs <;> simp_all [typeListToProdGeneric, List.map]
        | cons a' as' => cases bs with
          | nil => simp_all [typeListToProdGeneric, List.map]
          | cons b' bs' =>
              simp only [List.map, typeListToProdGeneric, ModuleType.prod.injEq,
                ModuleType.proc.injEq] at h
              obtain ⟨rfl, hrest⟩ := h
              rw [iha (l2 := b' :: bs') hrest]

-- TODO move to Syntax.lean
omit [ProgramSpec] in
private theorem HoleSigs.toList_injective :
    ∀ {h1 h2 : HoleSigs}, h1.toList = h2.toList → h1 = h2 := by
  intro h1
  induction h1 with
  | empty => intro h2 h; cases h2 with
    | empty => rfl
    | append hs s => simp [HoleSigs.toList] at h
  | append hs s ih => intro h2 h; cases h2 with
    | empty => simp [HoleSigs.toList] at h
    | append hs' s' =>
        simp only [HoleSigs.toList] at h
        obtain ⟨hl, hr⟩ := List.append_inj' h rfl
        obtain rfl := ih hl
        simp_all

theorem ModuleExpression.toSTLC_injective {Γ Γ' : ModuleContext} {T T' : ModuleType}
    (m : ModuleExpression Γ T) (m' : ModuleExpression Γ' T') :
    ModuleExpression.toSTLC m = ModuleExpression.toSTLC m' → ModuleExpression.erasedEqual m m' := by
  revert Γ' T' m'
  induction m with
  | unit =>
    intro Γ' T' m' h
    cases m' <;> simp_all [ModuleExpression.toSTLC, ModuleExpression.erasedEqual, ProcedureWithHoles.toSTLC]
  | proc p =>
    intro Γ' T' m' h
    cases m' <;> simp_all [ModuleExpression.toSTLC, ModuleExpression.erasedEqual, ProcedureWithHoles.toSTLC]
  | procHoles ne p =>
    intro Γ' T' m' h
    cases m' with
    | unit => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
    | procHoles ne' p' =>
        simp only [ModuleExpression.toSTLC] at h
        exact ProcedureWithHoles.toSTLC_inj h
    | proc _ | var _ | app _ _ | fst _ | snd _ | abs _ | pair _ _ =>
        simp_all [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC]
  | var r =>
    intro Γ' T' m' h
    cases m' <;> simp_all [ModuleExpression.toSTLC, ModuleExpression.erasedEqual, ProcedureWithHoles.toSTLC]
  | app f a ihf iha =>
    intro Γ' T' m' h
    cases m' with
    | app f' a' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.app.injEq] at h
      exact ⟨ihf f' h.1, iha a' h.2⟩
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | fst e ih =>
    intro Γ' T' m' h
    cases m' with
    | fst e' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.fst.injEq] at h
      exact ih e' h
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | snd e ih =>
    intro Γ' T' m' h
    cases m' with
    | snd e' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.snd.injEq] at h
      exact ih e' h
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | pair a b iha ihb =>
    intro Γ' T' m' h
    cases m' with
    | pair a' b' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.pair.injEq] at h
      exact ⟨iha a' h.1, ihb b' h.2⟩
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | abs body ih =>
    intro Γ' T' m' h
    cases m' with
    | abs body' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.lam.injEq] at h
      exact ih body' h
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h

theorem ModuleExpression.erasedEqual_refl (m : ModuleExpression Γ T) :
  ModuleExpression.erasedEqual m m := by
  induction m with
  | unit => trivial
  | proc => exact ⟨rfl, HEq.refl _⟩
  | procHoles => exact ⟨rfl, rfl, HEq.refl _⟩
  | var r => simp [ModuleExpression.erasedEqual]
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | fst e ih => exact ih
  | snd e ih => exact ih
  | pair a b iha ihb => exact ⟨iha, ihb⟩
  | abs body ih => exact ih

theorem ModuleExpression.erasedEqual_pair_right (a : ModuleExpression Γ T)
  {b : ModuleExpression Γ U} {b' : ModuleExpression Γ U'} (h : ModuleExpression.erasedEqual b b') :
  ModuleExpression.erasedEqual (.pair a b) (.pair a b') :=
  ⟨ModuleExpression.erasedEqual_refl a, h⟩

theorem ModuleExpression.erasedEqual_pair_left
    {a : ModuleExpression Γ T} {a' : ModuleExpression Γ T'}
    (b : ModuleExpression Γ U) (h : ModuleExpression.erasedEqual a a') :
    ModuleExpression.erasedEqual (.pair a b) (.pair a' b) :=
  ⟨h, ModuleExpression.erasedEqual_refl b⟩



/-- For an argument of a procedure-tuple type, being a `BasicTerm` after erasure means it is
    a proc-tuple.  (So a non-proc-tuple argument blocks the STLC `funcApp` reduction.) -/
private lemma isBasicType_imp_isProcTuple {Δ : ModuleContext} :
    (sigs : List ProcedureSignature) →
    (arg : ModuleExpression Δ
        (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc))) →
    Metatheory.STLCext.Term.isBasicType
        (ModuleType.toSTLC
          (typeListToProdGeneric ModuleType.prod ModuleType.unit (sigs.map ModuleType.proc)))
        (ModuleExpression.toSTLC arg) →
    IsProcTuple arg
  | [], arg, h => by
      sorry
      -- cases arg <;>
      --   simp_all [ModuleExpression.toSTLC, ModuleType.toSTLC, Metatheory.STLCext.Term.isBasicType]
  | [_], arg, h =>
      by sorry
      -- cases arg <;>
        -- simp_all [ModuleExpression.toSTLC, ModuleType.toSTLC, Metatheory.STLCext.Term.isBasicType,
          -- IsProcTuple]
  | _ :: s :: ss, arg, h => by
      cases arg with
      | pair a b =>
          cases a with
          | proc p =>
              simp only [ModuleExpression.toSTLC, ModuleType.toSTLC,
                Metatheory.STLCext.Term.isBasicType] at h
              exact isBasicType_imp_isProcTuple (s :: ss) b h.2
          | var _ | app _ _ | fst _ | snd _ =>
              simp only [ModuleExpression.toSTLC, ModuleType.toSTLC,
                Metatheory.STLCext.Term.isBasicType] at h
              exact h.1.elim
      | var _ | app _ _ | fst _ | snd _ =>
          simp_all [ModuleExpression.toSTLC, ModuleType.toSTLC, Metatheory.STLCext.Term.isBasicType]

-- TODO move to Modules.lean
theorem reductionStep_stlc_complete
  (m : ModuleExpression Γ T) (M' : Metatheory.STLCext.Term)
  (h : Metatheory.STLCext.Step (ModuleExpression.toSTLC m) M') :
    ∃ m', ReductionStep m m' ∧ ModuleExpression.toSTLC m' = M' := by
  induction m generalizing M' with
  | unit | proc _ | procHoles _ _ | var _ => simp only [ModuleExpression.toSTLC] at h; cases h
  | app f arg ihf iharg =>
      -- case-split on f first so ModuleExpression.toSTLC f is a literal constructor
      -- after simp, enabling cases h without dependent-elim failures
      cases f with
      | abs body =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | beta => exact ⟨substitute body arg, .beta, ModuleExpression.toSTLC_subst body arg⟩
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp [ModuleExpression.toSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.abs body) arg', .appR hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | procHoles ne proc =>
          simp only [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
          cases h with
          | appL step => nomatch step
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.procHoles ne proc) arg', .appR hnd,
                by simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC, heq]⟩
          | funcApp d g N hbasic =>
              sorry
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp [ModuleExpression.toSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app _ arg', .appR hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | abs body ih =>
      simp only [ModuleExpression.toSTLC] at h
      cases h with
      | lam step =>
          obtain ⟨body', hnd, heq⟩ := ih _ step
          exact ⟨.abs body', .lam hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | pair a b iha ihb =>
      simp only [ModuleExpression.toSTLC] at h
      cases h with
      | pairL step =>
          obtain ⟨a', hnd, heq⟩ := iha _ step
          exact ⟨.pair a' b, .pairL hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | pairR step =>
          obtain ⟨b', hnd, heq⟩ := ihb _ step
          exact ⟨.pair a b', .pairR hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | fst e ih =>
      -- case-split on e first for the same reason
      cases e with
      | pair e1 e2 =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | fstPair => exact ⟨e1, .fstPair, rfl⟩
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | snd e ih =>
      cases e with
      | pair e1 e2 =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | sndPair => exact ⟨e2, .sndPair, rfl⟩
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp [ModuleExpression.toSTLC, heq]⟩



-- TODO should be a simple corollary of reductionStep_stlc_compat
theorem cbvReductionStep_stlc_compat (m : ModuleExpression Γ T) (nn : ¬ Normal m) :
  Metatheory.STLCext.Step (ModuleExpression.toSTLC m)
                          (ModuleExpression.toSTLC (cbvReductionStep m nn)) := by
  induction m with
  | unit => exact absurd Normal.unit nn
  | proc => exact absurd .const nn
  | procHoles => exact absurd .constHoles nn
  | var => exact absurd (.neutral .var) nn
  | app hd arg ihhd iharg =>
    -- With induction m: hd is the function (arrow type), arg is the argument
    simp only [cbvReductionStep, ModuleExpression.toSTLC]
    split_ifs with h_abs h_cond h_nh
    · -- beta: hd (function) is .abs
      rw [ModuleExpression.toSTLC_subst]
      have h_meq : ModuleExpression.toSTLC hd =
          Metatheory.STLCext.Term.lam (ModuleExpression.toSTLC h_abs.body) := by
        cases hd with
        | abs body => simp [IsAbs.body, ModuleExpression.toSTLC]
        | procHoles _ _ => simp [IsAbs] at h_abs
        | var _ | app _ _ | fst _ | snd _ => simp [IsAbs] at h_abs
      rw [h_meq]
      exact Metatheory.STLCext.Step.beta _ _
    · -- δ: reduce to `reductionStep_stlc_compat` via a `ReductionStep.delta`.
      refine reductionStep_stlc_compat (hd.app arg) _ ?step
      obtain ⟨hph, harg⟩ := h_cond
      cases hd with
      | procHoles ne proc =>
          sorry
      | abs _ => exact absurd hph (by simp [IsProcHoles])
      | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    · -- hd is Normal: reduce the argument
      simp only [ModuleExpression.toSTLC]
      have h_nn_arg : ¬ Normal arg := fun ha => by
        by_cases hph : IsProcHoles hd
        · exact nn (.neutral (.appProcHoles hph ha (fun hpt => h_cond ⟨hph, hpt⟩)))
        · have hne : Neutral hd := by
            cases h_nh with
            | neutral ne => exact ne
            | abs _ => simp [IsAbs] at h_abs
            | constHoles => exact absurd trivial hph
          exact nn (.neutral (.app hne ha))
      exact Metatheory.STLCext.Step.appR (iharg h_nn_arg)
    · -- appL: hd (function) not normal, reduce it
      simp only [ModuleExpression.toSTLC]
      exact Metatheory.STLCext.Step.appL (ihhd h_nh)
  | fst m' ih =>
    simp only [cbvReductionStep, ModuleExpression.toSTLC]
    split_ifs with h_pair
    · cases m' with
      | pair m1 m2 =>
        simp only [IsPair.fst, IsPair.split, ModuleExpression.toSTLC]
        exact Metatheory.STLCext.Step.fstPair _ _
      | var _ | app _ _ | fst _ | snd _ => simp [IsPair] at h_pair
    · simp only [ModuleExpression.toSTLC]
      have nn' : ¬ Normal m' := fun hn => match hn with
        | .neutral ne => nn (.neutral (.fst ne))
        | .pair _ _ => h_pair (by simp [IsPair])
      exact Metatheory.STLCext.Step.fst (ih nn')
  | snd m' ih =>
    simp only [cbvReductionStep, ModuleExpression.toSTLC]
    split_ifs with h_pair
    · cases m' with
      | pair m1 m2 =>
        simp only [IsPair.snd, IsPair.split, ModuleExpression.toSTLC]
        exact Metatheory.STLCext.Step.sndPair _ _
      | var _ | app _ _ | fst _ | snd _ => simp [IsPair] at h_pair
    · simp only [ModuleExpression.toSTLC]
      have nn' : ¬ Normal m' := fun hn => match hn with
        | .neutral ne => nn (.neutral (.snd ne))
        | .pair _ _ => h_pair (by simp [IsPair])
      exact Metatheory.STLCext.Step.snd (ih nn')
  | abs body ih =>
    simp only [cbvReductionStep, ModuleExpression.toSTLC]
    exact Metatheory.STLCext.Step.lam (ih (fun hb => nn (.abs hb)))
  | pair m1 m2 ih1 ih2 =>
    simp only [cbvReductionStep, ModuleExpression.toSTLC]
    split_ifs with h1
    · -- split_ifs gives Normal m1 first (after not_not simplification)
      simp only [ModuleExpression.toSTLC]
      have h2 : ¬ Normal m2 := fun h2 => nn (.pair h1 h2)
      exact Metatheory.STLCext.Step.pairR (ih2 h2)
    · simp only [ModuleExpression.toSTLC]
      exact Metatheory.STLCext.Step.pairL (ih1 h1)

-- scoped instance (priority := 1001) instWellFoundedModuleExpression1 {Γ : ModuleContext} {T : ModuleType} :
--     WellFoundedRelation (ModuleExpression Γ T) :=
--   ⟨fun p q => Metatheory.STLCext.Step q.toSTLC p.toSTLC,
--    ⟨reduce_acc⟩⟩

instance (priority := 1001) {Γ : ModuleContext} {T : ModuleType} :
    WellFoundedRelation (ModuleExpression Γ T) := instWellFoundedRelationModuleExpressionReduction

-- TODO move to Modules.lean
def reduce (m : ModuleExpression Γ T) : ModuleExpression Γ T :=
    if h : Normal m then m
    else
      reduce (cbvReductionStep m h)
termination_by m
decreasing_by
  exact cbvReductionStep_is_reductionStep m h


-- TODO move to Modules.lean
theorem multiStepReduction_reduce {m : ModuleExpression Γ T} :
    MultiStepReduction m (reduce m) := by
  apply WellFoundedRelation.wf.induction (C := fun m => MultiStepReduction m (reduce m)) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact Rewriting.Star.refl _
  · apply Rewriting.Star.head (cbvReductionStep_is_reductionStep n h)
    sorry


theorem multiStepReduction_to_stlc_star {m m' : ModuleExpression Γ T}
    (h : MultiStepReduction m m') :
    Rewriting.Star Metatheory.STLCext.Step (ModuleExpression.toSTLC m) (ModuleExpression.toSTLC m')
    := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail hab hbc ih => exact Rewriting.Star.tail ih (reductionStep_stlc_compat _ _ hbc)

theorem ModuleExpression.toSTLC_Normal_iff {m : ModuleExpression Γ T} :
    Normal m ↔ Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC m) := by
  constructor
  · intro hm
    suffices key : ∀ {Γ' : ModuleContext} {T' : ModuleType} (m' : ModuleExpression Γ' T'),
        (Normal m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC m')) ∧
        (Neutral m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC m') ∧
                     (∀ body, ModuleExpression.toSTLC m' ≠ Metatheory.STLCext.Term.lam body) ∧
                     (∀ P Q, ModuleExpression.toSTLC m' ≠ Metatheory.STLCext.Term.pair P Q)) from
      (key m).1 hm
    intro Γ' T' m'
    induction m' with
    | unit => sorry
    | var n =>
      constructor
      · intro _ N h; simp only [ModuleExpression.toSTLC] at h; cases h
      · intro _; refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
        · simp only [ModuleExpression.toSTLC] at h; cases h
        · intro h; cases h
        · intro h; cases h
    | proc _ | procHoles _ _ =>
      constructor
      · intro _ N h; simp only [ModuleExpression.toSTLC] at h; cases h
      · intro h; cases h
    | abs body ih =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with
        | neutral hne => exact nomatch hne
        | abs hb => cases h with | lam step => exact (ih.1 hb) _ step
      · intro h; exact nomatch h
    | pair a b iha ihb =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with
        | neutral hne => exact nomatch hne
        | pair ha hb =>
          cases h with
          | pairL step => exact (iha.1 ha) _ step
          | pairR step => exact (ihb.1 hb) _ step
      · intro h; exact nomatch h
    | app f arg ihf iharg =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with
        | neutral hne =>
          cases hne with
          | app hf_n harg_n =>
            obtain ⟨ihf_step, ihf_lam, _⟩ := ihf.2 hf_n
            generalize hF : ModuleExpression.toSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [ModuleExpression.toSTLC] at hF
          | appProcHoles hph ha hpt =>
            cases f with
            | procHoles ne p =>
                simp only [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
                cases h with
                | appL step => nomatch step
                | appR step => exact (iharg.1 ha) _ step
                | funcApp d g N' hbasic => sorry
            | abs _ => exact absurd hph (by simp [IsProcHoles])
            | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
      · intro hne
        cases hne with
        | app hf_n harg_n =>
          obtain ⟨ihf_step, ihf_lam, ihf_pair⟩ := ihf.2 hf_n
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [ModuleExpression.toSTLC] at h
            generalize hF : ModuleExpression.toSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [ModuleExpression.toSTLC] at hF
          · intro h; cases h
          · intro h; cases h
        | appProcHoles hph ha hpt =>
          cases f with
          | procHoles ne p =>
              refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
              · simp only [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
                cases h with
                | appL step => nomatch step
                | appR step => exact (iharg.1 ha) _ step
                | funcApp d g N' hbasic =>
                    sorry
              · intro h; cases h
              · intro h; cases h
          | abs _ => exact absurd hph (by simp [IsProcHoles])
          | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    | fst e ihe =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with | neutral hne => cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : ModuleExpression.toSTLC e = E at h
          cases h with
          | fstPair => exact absurd hE (ihe_pair _ _)
          | fst step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [ModuleExpression.toSTLC] at h
            generalize hE : ModuleExpression.toSTLC e = E at h
            cases h with
            | fstPair => exact absurd hE (ihe_pair _ _)
            | fst step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h
    | snd e ihe =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with | neutral hne => cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : ModuleExpression.toSTLC e = E at h
          cases h with
          | sndPair => exact absurd hE (ihe_pair _ _)
          | snd step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [ModuleExpression.toSTLC] at h
            generalize hE : ModuleExpression.toSTLC e = E at h
            cases h with
            | sndPair => exact absurd hE (ihe_pair _ _)
            | snd step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h
  · intro h
    by_contra hnn
    exact h _ (reductionStep_stlc_compat m _ (cbvReductionStep_is_reductionStep m hnn))

theorem multiStepReduction_stlc_complete (m : ModuleExpression Γ T) {M' : Metatheory.STLCext.Term}
    (h : Rewriting.Star Metatheory.STLCext.Step (ModuleExpression.toSTLC m) M') :
    ∃ m' : ModuleExpression Γ T, MultiStepReduction m m' ∧ ModuleExpression.toSTLC m' = M' := by
  induction h with
  | refl => exact ⟨m, Rewriting.Star.refl _, rfl⟩
  | tail hab hbc ih =>
    obtain ⟨m_b, hred_b, heq_b⟩ := ih
    rw [← heq_b] at hbc
    obtain ⟨m', hnd, heq'⟩ := reductionStep_stlc_complete m_b _ hbc
    exact ⟨m', Rewriting.Star.tail hred_b hnd, heq'⟩

private theorem ModuleExpression.erasedEqual_normal_neutral_eq
    {Γ : ModuleContext} {T1 T2 : ModuleType}
    (m : ModuleExpression Γ T1) (m' : ModuleExpression Γ T2)
    (h : ModuleExpression.erasedEqual m m') :
    (Normal m → T1 = T2 → HEq m m') ∧ (Neutral m → T1 = T2 ∧ HEq m m') := by
  induction m generalizing T2 with
  | unit => sorry
  | proc p =>
    refine ⟨fun _ _ => ?_, fun hne => by cases hne⟩
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case proc p' =>
      obtain ⟨hsig, hp⟩ := h
      subst hsig
      exact heq_of_eq (congrArg ModuleExpression.proc (eq_of_heq hp))
  | procHoles ne p =>
    refine ⟨fun _ _ => ?_, fun hne => by cases hne⟩
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case procHoles ne' p' =>
      obtain ⟨hholes, hsig, hp⟩ := h
      subst hholes; subst hsig
      obtain rfl := eq_of_heq hp
      rfl
  | var r =>
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case var r' =>
      obtain ⟨hT, hr⟩ := ModuleContextIdx.toNat_inj' _ _ h
      subst hT
      have heq : HEq (ModuleExpression.var r) (ModuleExpression.var r') :=
        heq_of_eq (congrArg ModuleExpression.var (eq_of_heq hr))
      exact ⟨fun _ _ => heq, fun _ => ⟨rfl, heq⟩⟩
  | app f arg ihf iharg =>
    cases m' with
    | app f' arg' =>
      simp only [ModuleExpression.erasedEqual] at h
      obtain ⟨hf_eq, harg_eq⟩ := h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | app hf ha =>
            obtain ⟨hTf, hf_heq⟩ := (ihf f' hf_eq).2 hf
            obtain ⟨hA, hB⟩ := ModuleType.arr.inj hTf
            subst hA hB
            exact (eq_of_heq hf_heq) ▸ (eq_of_heq ((iharg arg' harg_eq).1 ha rfl)) ▸ HEq.rfl
          | appProcHoles hph ha hpt =>
            cases f with
            | procHoles ne p =>
                cases f' with
                | procHoles ne' p' =>
                    simp only [ModuleExpression.erasedEqual] at hf_eq
                    obtain ⟨hh, hs, hp⟩ := hf_eq
                    subst hh; subst hs; obtain rfl := eq_of_heq hp
                    obtain rfl := eq_of_heq ((iharg arg' harg_eq).1 ha rfl)
                    rfl
                | var _ | app _ _ | fst _ | snd _ | abs _ =>
                    simp [ModuleExpression.erasedEqual] at hf_eq
            | abs _ => exact absurd hph (by simp [IsProcHoles])
            | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
      · intro hne
        cases hne with
        | app hf ha =>
          obtain ⟨hTf, hf_heq⟩ := (ihf f' hf_eq).2 hf
          obtain ⟨hA, hB⟩ := ModuleType.arr.inj hTf
          subst hA hB
          exact ⟨rfl, (eq_of_heq hf_heq) ▸ (eq_of_heq ((iharg arg' harg_eq).1 ha rfl)) ▸ HEq.rfl⟩
        | appProcHoles hph ha hpt =>
          cases f with
          | procHoles ne p =>
              cases f' with
              | procHoles ne' p' =>
                  simp only [ModuleExpression.erasedEqual] at hf_eq
                  obtain ⟨hh, hs, hp⟩ := hf_eq
                  subst hh; subst hs; obtain rfl := eq_of_heq hp
                  obtain rfl := eq_of_heq ((iharg arg' harg_eq).1 ha rfl)
                  exact ⟨rfl, HEq.rfl⟩
              | var _ | app _ _ | fst _ | snd _ | abs _ =>
                  simp [ModuleExpression.erasedEqual] at hf_eq
          | abs _ => exact absurd hph (by simp [IsProcHoles])
          | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    | _ => simp [ModuleExpression.erasedEqual] at h
  | fst e ihe =>
    cases m' with
    | fst e' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | fst hne' =>
            obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
            obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
            subst hA hB
            exact heq_of_eq (congrArg ModuleExpression.fst (eq_of_heq he_heq))
      · intro hne
        cases hne with
        | fst hne' =>
          obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
          obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
          subst hA hB
          exact ⟨rfl, heq_of_eq (congrArg ModuleExpression.fst (eq_of_heq he_heq))⟩
    | _ => simp [ModuleExpression.erasedEqual] at h
  | snd e ihe =>
    cases m' with
    | snd e' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | snd hne' =>
            obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
            obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
            subst hA hB
            exact heq_of_eq (congrArg ModuleExpression.snd (eq_of_heq he_heq))
      · intro hne
        cases hne with
        | snd hne' =>
          obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
          obtain ⟨hA, hB⟩ := ModuleType.prod.inj hTe
          subst hA hB
          exact ⟨rfl, heq_of_eq (congrArg ModuleExpression.snd (eq_of_heq he_heq))⟩
    | _ => simp [ModuleExpression.erasedEqual] at h
  | abs body ihbody =>
    cases m' with
    | abs body' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn hT
        cases hn with
        | neutral hne => cases hne
        | abs hb =>
          obtain ⟨hA, hB⟩ := ModuleType.arr.inj hT
          subst hA hB
          have hbody' := eq_of_heq ((ihbody body' h).1 hb rfl)
          subst hbody'
          exact HEq.rfl
      · intro hne
        cases hne
    | _ => simp [ModuleExpression.erasedEqual] at h
  | pair a b iha ihb =>
    cases m' with
    | pair a' b' =>
      simp only [ModuleExpression.erasedEqual] at h
      obtain ⟨ha_eq, hb_eq⟩ := h
      constructor
      · intro hn hT
        cases hn with
        | neutral hne => cases hne
        | pair ha hb =>
          obtain ⟨hA, hB⟩ := ModuleType.prod.inj hT
          subst hA hB
          have ha' := eq_of_heq ((iha a' ha_eq).1 ha rfl)
          have hb' := eq_of_heq ((ihb b' hb_eq).1 hb rfl)
          subst ha' hb'
          exact HEq.rfl
      · intro hne
        cases hne
    | _ => simp [ModuleExpression.erasedEqual] at h

theorem ModuleExpression.erasedEqual_normal_eq {Γ : ModuleContext} {T : ModuleType}
    {n1 n2 : ModuleExpression Γ T} (hn1 : Normal n1)
    (h : ModuleExpression.erasedEqual n1 n2) : n1 = n2 :=
  eq_of_heq ((ModuleExpression.erasedEqual_normal_neutral_eq n1 n2 h).1 hn1 rfl)

theorem ModuleExpression.erasedEqual_neutral_eq {Γ : ModuleContext} {T1 T2 : ModuleType}
    {e1 : ModuleExpression Γ T1} {e2 : ModuleExpression Γ T2}
    (hne1 : Neutral e1)
    (h : ModuleExpression.erasedEqual e1 e2) : T1 = T2 ∧ HEq e1 e2 :=
  (ModuleExpression.erasedEqual_normal_neutral_eq e1 e2 h).2 hne1

theorem ModuleExpression.toSTLC_injective_normal {Γ : ModuleContext} {T : ModuleType}
    {n1 n2 : ModuleExpression Γ T} (hn1 : Normal n1)
    (h : ModuleExpression.toSTLC n1 = ModuleExpression.toSTLC n2) : n1 = n2 :=
  ModuleExpression.erasedEqual_normal_eq hn1 (ModuleExpression.toSTLC_injective n1 n2 h)

theorem reduce_normal (m : ModuleExpression Δ t) : Normal (reduce m) := by
  apply WellFoundedRelation.wf.induction (C := fun m => Normal (reduce m)) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact h
  · sorry

theorem confluence {m m1 m2 : ModuleExpression Γ T}
   (h1 : MultiStepReduction m m1) (h2 : MultiStepReduction m m2) :
   reduce m1 = reduce m2 := by
  have star1 : Rewriting.Star Metatheory.STLCext.Step (ModuleExpression.toSTLC m)
                                                      (ModuleExpression.toSTLC (reduce m1)) :=
    Rewriting.Star.trans (multiStepReduction_to_stlc_star h1)
                         (multiStepReduction_to_stlc_star multiStepReduction_reduce)
  have star2 : Rewriting.Star Metatheory.STLCext.Step (ModuleExpression.toSTLC m)
                                                      (ModuleExpression.toSTLC (reduce m2)) :=
    Rewriting.Star.trans
      (multiStepReduction_to_stlc_star h2)
      (multiStepReduction_to_stlc_star multiStepReduction_reduce)
  have nf1 : Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC (reduce m1)) :=
    ModuleExpression.toSTLC_Normal_iff.mp (reduce_normal m1)
  have nf2 : Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC (reduce m2)) :=
    ModuleExpression.toSTLC_Normal_iff.mp (reduce_normal m2)
  exact ModuleExpression.toSTLC_injective_normal (reduce_normal m1)
    (Rewriting.normalForm_unique Metatheory.STLCext.step_confluent star1 star2 nf1 nf2)

theorem reduce_normalClosed (m : ModuleExpression .empty t) : NormalClosed (reduce m) :=
  (reduce_normal m).normalClosed

structure Module (T : ModuleType) where
  expression : ModuleExpression .empty T
  normal : NormalClosed expression

def _root_.Language.Modules.ModuleExpression.toProcModule {T : ModuleType}
  (m : ModuleExpression .empty T) : Module T :=
  ⟨reduce m, reduce_normalClosed m⟩

instance : CoeFun (Module (.arr T U)) (fun _ ↦ Module T → Module U) where
  coe f x := ModuleExpression.toProcModule (ModuleExpression.app f.expression x.expression)

@[simp]
theorem reduce_fst (m : ModuleExpression Γ T) (m' : ModuleExpression Γ T') :
  reduce (ModuleExpression.fst (ModuleExpression.pair m m')) = reduce m := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | fst ne' => exact nomatch ne'
  · rfl

@[simp]
theorem reduce_snd (m : ModuleExpression Γ T) (m' : ModuleExpression Γ T') :
  reduce (ModuleExpression.snd (ModuleExpression.pair m m')) = reduce m' := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | snd ne' => exact nomatch ne'
  · rfl

@[simp]
theorem reduce_idempotent (m : ModuleExpression Γ T) :
  reduce (reduce m) = reduce m := by
  conv_lhs => unfold reduce
  simp [reduce_normal m]

theorem multiStepReduction_app
    {m1 m1' : ModuleExpression Γ (.arr T U)} {m2 m2' : ModuleExpression Γ T}
    (h1 : MultiStepReduction m1 m1') (h2 : MultiStepReduction m2 m2') :
    MultiStepReduction (ModuleExpression.app m1 m2) (ModuleExpression.app m1' m2') := by
  have left : MultiStepReduction (ModuleExpression.app m1 m2) (ModuleExpression.app m1' m2) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appL hbc)
  have right : MultiStepReduction (ModuleExpression.app m1' m2) (ModuleExpression.app m1' m2') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appR hbc)
  exact Rewriting.Star.trans left right

theorem reduce_app (m : ModuleExpression Γ (.arr T U)) (m' : ModuleExpression Γ T) :
  reduce (ModuleExpression.app m m') = reduce (ModuleExpression.app (reduce m) (reduce m')) :=
  (reduce_idempotent _).symm.trans
    (confluence multiStepReduction_reduce
      (multiStepReduction_app multiStepReduction_reduce multiStepReduction_reduce))

@[simp]
theorem reduce_beta
  (body : ModuleExpression (Γ.append T) U) (arg : ModuleExpression Γ T) :
  reduce (ModuleExpression.app (ModuleExpression.abs body) arg) = reduce (substitute body arg) := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with
      | app ne' _ => exact nomatch ne'
      | appProcHoles hph _ _ => exact absurd hph (by simp [IsProcHoles])
  · rfl

private theorem multiStepReduction_fst
    {e e' : ModuleExpression Γ (.prod A B)} (h : MultiStepReduction e e') :
    MultiStepReduction (ModuleExpression.fst e) (ModuleExpression.fst e') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (.fst hbc)

-- TODO: How to tell the simplifier to use these theorems?
-- Maybe need to mark them as congruence rule?
-- => Investigate @[gcongr]
-- @[congr]
theorem reduce_fst_cong (m m' : ModuleExpression Γ (.prod T U)) :
    reduce m = reduce m' → reduce (ModuleExpression.fst m) = reduce (ModuleExpression.fst m') := by
  intro h
  have eq1 : reduce (ModuleExpression.fst m) = reduce (ModuleExpression.fst (reduce m)) :=
    (reduce_idempotent _).symm.trans
      (confluence multiStepReduction_reduce (multiStepReduction_fst multiStepReduction_reduce))
  have eq2 : reduce (ModuleExpression.fst m') = reduce (ModuleExpression.fst (reduce m')) :=
    (reduce_idempotent _).symm.trans
      (confluence multiStepReduction_reduce (multiStepReduction_fst multiStepReduction_reduce))
  rw [eq1, eq2, h]

def Module.fst {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toProcModule

def Module.snd {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toProcModule

def Module.pair {T U} (m1 : Module T) (m2 : Module U) : Module (.prod T U) :=
  (m1.expression.pair m2.expression).toProcModule

@[ext]
theorem Module.ext {T} {m1 m2 : Module T} (h : m1.expression = m2.expression) :
  m1 = m2 := by
  obtain ⟨e1, n1⟩ := m1; obtain ⟨e2, n2⟩ := m2
  simp only at h; subst h; rfl

@[simp]
theorem Module.expression_fst {T U} (m : Module (.prod T U)) :
    m.fst.expression = reduce m.expression.fst := rfl

@[simp]
theorem Module.toProcModule_expression {T} (m : ModuleExpression .empty T) :
    (ModuleExpression.toProcModule m).expression = reduce m := rfl

@[simp]
theorem reduce_fst_pair {T U} (m1 : ModuleExpression Γ T) (m2 : ModuleExpression Γ U) :
    reduce (.fst (.pair m1 m2)) = reduce m1 := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | fst ne' => exact nomatch ne'
  · rfl

private theorem multiStepReduction_pair
    {a a' : ModuleExpression Γ A} {b b' : ModuleExpression Γ B}
    (h1 : MultiStepReduction a a') (h2 : MultiStepReduction b b') :
    MultiStepReduction (ModuleExpression.pair a b) (ModuleExpression.pair a' b') := by
  have left : MultiStepReduction (ModuleExpression.pair a b) (ModuleExpression.pair a' b) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairL hbc)
  have right : MultiStepReduction (ModuleExpression.pair a' b) (ModuleExpression.pair a' b') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairR hbc)
  exact Rewriting.Star.trans left right

@[simp]
theorem reduce_pair {T U} (m1 : ModuleExpression Γ T) (m2 : ModuleExpression Γ U) :
    reduce (ModuleExpression.pair m1 m2) = ModuleExpression.pair (reduce m1) (reduce m2) := by
  have h2 : MultiStepReduction (ModuleExpression.pair m1 m2)
            (ModuleExpression.pair (reduce m1) (reduce m2)) :=
    multiStepReduction_pair multiStepReduction_reduce multiStepReduction_reduce
  have key : reduce (ModuleExpression.pair m1 m2) =
             reduce (ModuleExpression.pair (reduce m1) (reduce m2)) :=
    (reduce_idempotent _).symm.trans (confluence multiStepReduction_reduce h2)
  rw [key]; conv_lhs => unfold reduce
  rw [dif_pos (Normal.pair (reduce_normal m1) (reduce_normal m2))]

@[simp]
theorem Module.reduce_expression {T} (m : Module T) : reduce m.expression = m.expression := by
  obtain ⟨expression, normal⟩ := m; simp only
  have hn : Normal expression := by
    induction normal with
    |unit => exact .unit
    | const => exact .const
    | constHoles => exact .constHoles
    | abs h => exact .abs h
    | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  conv_lhs => unfold reduce
  rw [dif_pos hn]

@[simp]
theorem Module.fst_pair {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair m2).fst = m1 := by
  ext
  simp [Module.fst, Module.pair]


opaque FV : Type
-- Placeholder
axiom fv_proc {sig holes} (proc : ProcedureWithHoles holes sig) : Set FV
axiom fv_proc_instantiate {sig holes} (proc : ProcedureWithHoles holes sig) (args) :
  fv_proc (proc.instantiate args) = fv_proc proc ∪ ⋃ i : HoleIndex holes sig, fv_proc (args i)

def fv' {mctx : ModuleContext} {mty : ModuleType} (mex : ModuleExpression mctx mty) : Set FV :=
  match mex with
    | .unit => sorry
    | .proc p => fv_proc p
    | .procHoles n p => fv_proc p
    | .var .zero => {}
    | .var (.succ n) => {}
    | .app a b => fv' a ∪ fv' b
    | .fst a => fv' a
    | .snd a => fv' a
    | .abs body => fv' body
    | .pair a b => fv' a ∪ fv' b

-- Trivially true but not what we want.
-- Unintuitive that modules don't reduce when applying
-- Do we need the operational semantics of the simply typled λ-calculus?
-- I think so, below's the attempt
theorem fv'_app (a : ModuleExpression Γ (ModuleType.arr A B)) (b : ModuleExpression Γ A) :
  fv' (ModuleExpression.app a b) = fv' a ∪ fv' b := rfl

def fv (m : ModuleExpression c t) : Set FV := fv' (reduce m)

private lemma fv'_var_eq {Γ T} (r : ModuleContextIdx Γ T) : fv' (.var r) = {} := by
  cases r <;> rfl

private lemma fv'_rename_eq {Δ U} (m : ModuleExpression Δ U) :
    ∀ {Γ : ModuleContext} (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T),
    fv' (m.rename ρ) = fv' m := by
  induction m with
  | unit => sorry
  | proc | procHoles | var _ => intros; simp [ModuleExpression.rename, fv', fv'_var_eq]
  | app f a ihf iha => intros Γ ρ; simp [ModuleExpression.rename, fv', ihf ρ, iha ρ]
  | fst e ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih ρ]
  | snd e ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih ρ]
  | abs body ih => intros Γ ρ; simp [ModuleExpression.rename, fv', ih (liftRenaming ρ)]
  | pair a b iha ihb => intros Γ ρ; simp [ModuleExpression.rename, fv', iha ρ, ihb ρ]

private lemma fv'_substAll_le {S : Set FV} {Δ U} (m : ModuleExpression Δ U) :
    ∀ {Γ : ModuleContext} (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T),
    (∀ {T} (r : ModuleContextIdx Δ T), fv' (σ r) ⊆ S) →
    fv' (substituteSimultaneously σ m) ⊆ fv' m ∪ S := by
  induction m with
  | unit => sorry
  | proc | procHoles => intros; simp [substituteSimultaneously, fv']
  | var r =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv'_var_eq, Set.empty_union]
      exact hσ r
  | app f a ihf iha =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      rintro x (h | h)
      · rcases ihf σ hσ h with h' | h'
        · exact .inl (.inl h')
        · exact .inr h'
      · rcases iha σ hσ h with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'
  | fst e ih => intros Γ σ hσ; simp only [substituteSimultaneously, fv']; exact ih σ hσ
  | snd e ih => intros Γ σ hσ; simp only [substituteSimultaneously, fv']; exact ih σ hσ
  | abs body ih =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      apply ih (liftSubstitution σ)
      intro T r
      cases r with
      | zero => simp [liftSubstitution, fv']
      | succ r' => simp only [liftSubstitution]; rw [fv'_rename_eq]; exact hσ r'
  | pair a b iha ihb =>
      intros Γ σ hσ
      simp only [substituteSimultaneously, fv']
      rintro x (h | h)
      · rcases iha σ hσ h with h' | h'
        · exact .inl (.inl h')
        · exact .inr h'
      · rcases ihb σ hσ h with h' | h'
        · exact .inl (.inr h')
        · exact .inr h'

private lemma fv'_subst_le
    (body : ModuleExpression (Δ.append u) t) (arg : ModuleExpression Δ u) :
    fv' (substitute body arg) ⊆ fv' body ∪ fv' arg := by
  simp only [substitute]
  apply fv'_substAll_le body (S := fv' arg)
  intro T r
  cases r with
  | zero => simp [variableSubstitution]
  | succ r' => simp only [variableSubstitution, fv'_var_eq]; exact Set.empty_subset _

/-- The union of `fv_proc` over the entries of a procedure tuple. -/
def fvArgs : (sigs : List ProcedureSignature) →
    typeListToProdGeneric Prod PUnit (sigs.map Procedure) → Set FV
  | [],           _          => {}
  | [_],          p          => fv_proc p
  | _ :: s :: ss, (p, rest)  => fv_proc p ∪ fvArgs (s :: ss) rest

lemma fv'_procTupleOfArgs_eq_fvArgs {Δ : ModuleContext} :
    (sigs : List ProcedureSignature) → (hne : sigs ≠ []) →
    (args : typeListToProdGeneric Prod PUnit (sigs.map Procedure)) →
    fv' (procTupleOfArgs (Δ := Δ) sigs hne args) = fvArgs sigs args
  | [], hne, _ => absurd rfl hne
  | [_], _, p => by simp [procTupleOfArgs, fv', fvArgs]
  | _ :: s :: ss, _, (p, rest) => by
      simp only [procTupleOfArgs, fv', fvArgs]
      rw [fv'_procTupleOfArgs_eq_fvArgs (s :: ss) (by simp) rest]



theorem fv_reduction_step (m : ModuleExpression c t) (h : ReductionStep m m') :
  fv' m' ⊆ fv' m := by
  cases h
  all_goals sorry


theorem fv_reduce (m : ModuleExpression c t) : fv m ⊆ fv' m := by
  unfold fv
  -- Having some packaged induction principle for reduce would be nice.
  apply WellFoundedRelation.wf.induction (C := fun m => fv' (reduce m) ⊆ fv' m) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact Set.Subset.refl _
  · have h1 : ReductionStep n (cbvReductionStep n h) := by apply cbvReductionStep_is_reductionStep
    have h2 := fv_reduction_step _ h1
    have h3 : WellFoundedRelation.rel (cbvReductionStep n h) n := sorry
    have h4 := ih _ h3
    grind

theorem fv_app (a : ModuleExpression Γ (ModuleType.arr A B)) (b : ModuleExpression Γ A) :
    fv (ModuleExpression.app a b) ⊆ fv a ∪ fv b := by
  simp only [fv, ← fv'_app]
  rw [reduce_app]
  exact fv_reduce _



section Demo

axiom sig : ProcedureSignature
def TestModuleType := Module (ModuleType.prod (ModuleType.proc sig) (ModuleType.proc sig))

noncomputable
def TestModuleType.main (m : TestModuleType) : Module (ModuleType.proc sig) := m.fst
noncomputable
def TestModuleType.aux (m : TestModuleType) : Module (ModuleType.proc sig) := m.snd

structure TestModuleTypeStruct where
  main : Module (ModuleType.proc sig)
  aux : Module (ModuleType.proc sig)

noncomputable
def TestModuleTypeStruct.destruct (str : TestModuleTypeStruct) : TestModuleType :=
  str.main.pair str.aux

noncomputable
def TestModuleType.mk (str : TestModuleTypeStruct) : TestModuleType := str.main.pair str.aux

axiom testMain : Module (ModuleType.proc sig)
axiom testAux : Module (ModuleType.proc sig)

noncomputable
def myMod := TestModuleType.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModuleType.main, myMod, TestModuleType.mk]

end Demo

end Language.Modules
