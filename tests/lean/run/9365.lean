import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

abbrev SM := StateM (Array Nat)

abbrev gns : SVal ((Array Nat)::[]) (Array Nat) := fun s => SVal.pure s

noncomputable def setZeroHead : StateM (Array Nat) Unit := do
  modify fun _ => #[0, 1, 2, 3, 4, 5]

theorem setZeroHead_spec :
   ⦃⌜True⌝⦄
   setZeroHead
   ⦃⇓ _ => ⌜∃ ns', (#gns).toList = 0 :: ns'⌝⦄ := by
  mvcgen [setZeroHead]
  -- We want `mintro`duce the tuple `t` here in order for us not having to repeat its
  -- definition in t.2.toList.tail below
  mintro t
  simp
  exists t.2.toList.tail
