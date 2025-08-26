import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

structure MyException where
def F : EStateM MyException Unit Unit := do
  for _ in [0:5] do
    pure ()

theorem F_spec :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => ⌜1 < 2⌝⦄ := by
  mvcgen [F]

  case inv1 => exact ⇓ _ => ⌜1 < 2⌝
  -- it would be nice if we had a tactic wrapper around `case inv => exact ...` that does `mleave`
  -- on all subgoals afterwards.

  · mleave
    omega
  · mleave
    omega
  -- Goal that could be discharged completely automatically:
  -- case post.except
  -- ⊢ (⇓x => ⌜1 < 2⌝).snd ⊢ₑ (⇓x => ⌜1 < 2⌝).snd
  · assumption
  · mleave

theorem F_spec_using_with :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => ⌜1 < 2⌝⦄ := by
  mvcgen [F]
  invariants · ⇓ _ => ⌜1 < 2⌝
  with omega
