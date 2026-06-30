/-! Test that `@[cbv_opaque]` is rejected on `@[reducible]` declarations.

The SymM framework eagerly unfolds reducible definitions during preprocessing, so
marking a reducible definition as `@[cbv_opaque]` would have no effect — `cbv`
never sees the constant by the time it runs. The attribute rejects this combination
up front with a clear error rather than silently doing nothing. -/

/-! ## Direct `@[reducible, cbv_opaque]` combination is rejected. -/

/--
error: `@[cbv_opaque]` cannot be applied to a `@[reducible]` declaration: `reducibleSecret` is reducible, so it is unfolded before `cbv` runs
-/
#guard_msgs in
@[reducible, cbv_opaque] def reducibleSecret : Nat := 42

/-! ## Post-hoc `attribute [cbv_opaque]` on a reducible definition is rejected. -/

@[reducible] def alreadyReducible : Nat := 7

/--
error: `@[cbv_opaque]` cannot be applied to a `@[reducible]` declaration: `alreadyReducible` is reducible, so it is unfolded before `cbv` runs
-/
#guard_msgs in
attribute [cbv_opaque] alreadyReducible

/-! ## Non-reducible `@[cbv_opaque]` still works (sanity check). -/

@[cbv_opaque] def nonReducibleSecret : Nat := 99

/--
error: unsolved goals
⊢ nonReducibleSecret = 99
-/
#guard_msgs in
example : nonReducibleSecret = 99 := by conv => lhs; cbv
