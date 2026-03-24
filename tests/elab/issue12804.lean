/-!
# Issue 12804: reducibility attributes should not apply to theorems
-/

theorem wfThm : ∀ n : Nat, n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (wfThm n)

/--
error: failed to set reducibility status, `wfThm` is not a definition

Note: Use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [irreducible] wfThm

/--
error: failed to set reducibility status, `wfThm` is not a definition

Note: Use `set_option allowUnsafeReducibility true` to override reducibility status validation
-/
#guard_msgs in
attribute [reducible] wfThm
