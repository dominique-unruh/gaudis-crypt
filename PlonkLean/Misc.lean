/-

Various mathematical things that we use.
Maybe some should be in mathlib.

-/

import Mathlib.Order.OmegaCompletePartialOrder

def OmegaCompletePartialOrder.ContinuousHom.lfp [OmegaCompletePartialOrder a] [OrderBot a]
    (f : a →𝒄 a) :=
  have prf := Monotone.monotone_iterate_of_le_map f.monotone (OrderBot.bot_le _)
  OmegaCompletePartialOrder.ωSup ⟨fun n => f^[n] ⊥, prf⟩

def IsLfp [LE a] (f : a -> a) (x : a) := IsLeast (Function.fixedPoints f) x

theorem ContinuousHom.lfp_isLfp [OmegaCompletePartialOrder a] [OrderBot a] (f : a →𝒄 a) :
    IsLfp f (f.lfp) := by
  let chain : OmegaCompletePartialOrder.Chain a :=
    ⟨fun n => f^[n] ⊥,
      Monotone.monotone_iterate_of_le_map f.monotone (OrderBot.bot_le _)⟩
  have hlfp : f.lfp = OmegaCompletePartialOrder.ωSup chain := rfl
  refine ⟨?_, ?_⟩
  · -- f.lfp is a fixed point of f.
    change f f.lfp = f.lfp
    rw [hlfp]
    have hmap : f (OmegaCompletePartialOrder.ωSup chain) =
                OmegaCompletePartialOrder.ωSup (chain.map f.toOrderHom) :=
      f.map_ωSup' chain
    rw [hmap]
    -- ωSup (chain.map f.toOrderHom) = ωSup chain (cofinal shift by 1)
    apply le_antisymm
    · apply OmegaCompletePartialOrder.ωSup_le
      intro n
      have hshift : (chain.map f.toOrderHom) n = chain (n+1) := by
        change f (f^[n] (⊥ : a)) = f^[n+1] ⊥
        rw [Function.iterate_succ_apply']
      rw [hshift]
      exact OmegaCompletePartialOrder.le_ωSup chain (n+1)
    · apply OmegaCompletePartialOrder.ωSup_le
      intro n
      calc chain n
          ≤ chain (n+1) := chain.monotone (Nat.le_succ n)
        _ = (chain.map f.toOrderHom) n := by
            change f^[n+1] (⊥ : a) = f (f^[n] ⊥)
            rw [Function.iterate_succ_apply']
        _ ≤ OmegaCompletePartialOrder.ωSup (chain.map f.toOrderHom) :=
            OmegaCompletePartialOrder.le_ωSup _ n
  · -- f.lfp is below every fixed point.
    intro y hy
    rw [hlfp]
    apply OmegaCompletePartialOrder.ωSup_le
    intro n
    change f^[n] (⊥ : a) ≤ y
    induction n with
    | zero => exact bot_le
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc f (f^[k] ⊥) ≤ f y := f.monotone ih
        f y = y := hy


theorem ContinuousHom.map_lfp_comp [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
      [OrderBot α] [OrderBot β] (f : β →𝒄 α) (g : α →𝒄 β) :
  f (g.comp f).lfp = (f.comp g).lfp := by
  apply le_antisymm
  · have h : (g.comp f).lfp ≤ g (f.comp g).lfp :=
      (ContinuousHom.lfp_isLfp (g.comp f)).2
        (congr_arg g (ContinuousHom.lfp_isLfp (f.comp g)).1)
    calc f (g.comp f).lfp
        ≤ f (g (f.comp g).lfp) := f.monotone h
      _ = (f.comp g).lfp := (ContinuousHom.lfp_isLfp (f.comp g)).1
  · exact (ContinuousHom.lfp_isLfp (f.comp g)).2
        (congr_arg f (ContinuousHom.lfp_isLfp (g.comp f)).1)
