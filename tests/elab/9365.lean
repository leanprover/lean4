import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

abbrev SM := StateM (Array Nat)

noncomputable def setZeroHead : StateM (Array Nat) Unit := do
  modify fun _ => #[0, 1, 2, 3, 4, 5]

theorem setZeroHead_spec :
   ⦃⌜True⌝⦄
   setZeroHead
   ⦃⇓ _ gns => ⌜∃ ns', gns.toList = 0 :: ns'⌝⦄ := by
  mvcgen [setZeroHead]
  -- We want to see and name the tuple `t` here in order for us not having to repeat its
  -- definition in t.2.toList.tail below
  rename_i t
  exists t.2.toList.tail
