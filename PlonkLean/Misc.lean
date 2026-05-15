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
    IsLfp f (f.lfp) := by sorry
