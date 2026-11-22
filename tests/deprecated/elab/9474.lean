import Std.Tactic.Do

/-!
Regression test for #9474: `mvcgen` introduces through `let`/`have` bindings.
-/

set_option sym.debug true

open Std.Do

noncomputable def setZeroHead : StateM (List Nat) Unit := do
  modify fun _ => [1, 0, 1, 2, 3, 4, 5]
  pure ()
  modify fun s => s.tail
  pure ()

theorem setZeroHead_spec :
   ⦃⌜True⌝⦄
   setZeroHead
   ⦃⇓ _ gns => ⌜∃ ns', gns = 0 :: ns'⌝⦄ := by
  mvcgen [setZeroHead] -- should mintro through let/have bindings
  mleave
  rename_i t
  exists t.2.tail
