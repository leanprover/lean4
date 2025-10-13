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
  case inv1 => exact fun _ _ => ⌜1 < 2⌝
  -- it would be nice if we had a tactic wrapper around `case inv => exact ...` that does `mleave`
  -- on all subgoals afterwards.
  case vc1 =>
    mleave
    omega
  case vc2 =>
    mleave
    omega
  case vc3 =>
    mleave
    omega

theorem F_spec_using_with :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => ⌜1 < 2⌝⦄ := by
  mvcgen [F]
  invariants
  | inv1 => fun _ _ => ⌜1 < 2⌝
  with omega
