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






-- scoped instance (priority := 1001) instWellFoundedModuleExpression1 {Γ : ModuleContext} {T : ModuleType} :
--     WellFoundedRelation (ModuleExpression Γ T) :=
--   ⟨fun p q => Metatheory.STLCext.Step q.toSTLC p.toSTLC,
--    ⟨reduce_acc⟩⟩

instance (priority := 1001) {Γ : ModuleContext} {T : ModuleType} :
    WellFoundedRelation (ModuleExpression Γ T) := instWellFoundedRelationModuleExpressionReduction



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


theorem ModuleExpression.erasedEqual_neutral_eq {Γ : ModuleContext} {T1 T2 : ModuleType}
    {e1 : ModuleExpression Γ T1} {e2 : ModuleExpression Γ T2}
    (hne1 : Neutral e1)
    (h : ModuleExpression.erasedEqual e1 e2) : T1 = T2 ∧ HEq e1 e2 :=
  (ModuleExpression.erasedEqual_normal_neutral_eq e1 e2 h).2 hne1


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

-- TODO move to Modules
def Module.fst {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toModule

-- TODO move to Modules
def Module.snd {T U} (m : Module (.prod T U)) : Module U :=
  m.expression.snd.toModule

-- TODO move to Modules
def Module.pair {T U} (m1 : Module T) (m2 : Module U) : Module (.prod T U) :=
  (m1.expression.pair m2.expression).toModule

-- TODO move to Modules
@[ext]
theorem Module.ext {T} {m1 m2 : Module T} (h : m1.expression = m2.expression) :
  m1 = m2 := by
  obtain ⟨e1, n1⟩ := m1; obtain ⟨e2, n2⟩ := m2
  simp only at h; subst h; rfl

@[simp]
theorem Module.expression_fst {T U} (m : Module (.prod T U)) :
    m.fst.expression = reduce m.expression.fst := rfl

-- TODO move to Modules
@[simp]
theorem Module.toModule_expression {T} (m : ModuleExpression .empty T) :
    (ModuleExpression.toModule m).expression = reduce m := rfl

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
  simp [Module.fst, Module.pair, reduce_pair]




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
