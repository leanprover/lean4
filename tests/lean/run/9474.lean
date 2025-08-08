import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

abbrev gns : SVal ((List Nat)::[]) (List Nat) := fun s => SVal.pure s

noncomputable def setZeroHead : StateM (List Nat) Unit := do
  modify fun _ => [1, 0, 1, 2, 3, 4, 5]
  pure ()
  modify fun s => s.tail
  pure ()

theorem setZeroHead_spec :
   ⦃⌜True⌝⦄
   setZeroHead
   ⦃⇓ _ => ⌜∃ ns', #gns = 0 :: ns'⌝⦄ := by
  mvcgen [setZeroHead] -- should mintro through let/have bindings
  mleave
  rename_i t
  exists t.2.tail
