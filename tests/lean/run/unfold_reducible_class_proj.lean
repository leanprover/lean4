import Lean

open Lean Meta

/-!
Tests whether the class fields marked as `[reducible]` are properly
reduced by `unfoldDefinition?`.
-/

set_option allowUnsafeReducibility true
attribute [reducible] MonadControlT.stM

/--
info: ExceptT ε m
---
info: stM m (ExceptT ε m) α
---
info: stM m m (MonadControl.stM m (ExceptT ε m) α)
-/
#guard_msgs in
run_meta do
  withLocalDeclD `ε (.sort 1) fun ε => do
  withLocalDeclD `α (.sort 1) fun α => do
  withLocalDeclD `m (.forallE `a (.sort 1) (.sort 1) .default) fun m => do
  withLocalDeclD `i (mkApp (mkConst ``Monad [0, 0]) m) fun _ => do
  let e := mkApp2 (mkConst ``ExceptT [0, 0]) ε m
  check e
  logInfo e
  let s ← mkAppM ``stM #[m, e, α]
  check s
  logInfo s
  withReducible do logInfo (← unfoldDefinition? s)

/--
info: a + a
---
info: none
---
info: Add.add a a
-/
#guard_msgs in
run_meta do
  withLocalDeclD `a Nat.mkType fun a => do
    let e := mkNatAdd a a
    logInfo e
    withReducible do logInfo (← unfoldDefinition? e)
    withReducibleAndInstances do logInfo (← unfoldDefinition? e)
