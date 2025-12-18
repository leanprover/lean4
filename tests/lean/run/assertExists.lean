/-!
# Tests for `#import_path`, `assert_not_exists`, `assert_not_imported`, and `#check_assertions`
-/

-- Test #import_path with an existing declaration
/--
info: Declaration LawfulMonadLift is imported via
Init.Control.Lawful.MonadLift.Basic,
  which is imported by Init.Control.Lawful.MonadLift.Lemmas,
  which is imported by Init.Control.Lawful.MonadLift.Instances,
  which is imported by Init.Control.Lawful.MonadLift,
  which is imported by Init.Control.Lawful,
  which is imported by Init.Control,
  which is imported by Init,
  which is imported by this file.
-/
#guard_msgs in
#import_path LawfulMonadLift

-- Test #import_path with a non-existent declaration
/--
info: Declaration 'NonExistentDecl' is not in scope.
-/
#guard_msgs in
#import_path NonExistentDecl

-- Test assert_not_exists with declarations that don't exist (should pass silently)
#guard_msgs in
assert_not_exists FooBarBaz

#guard_msgs in
assert_not_exists NonExistent1 NonExistent2

-- Test assert_not_imported with modules that don't exist (should pass silently)
#guard_msgs in
assert_not_imported Fake.Module

-- Test assert_not_exists with an existing declaration (should error)
/--
error: Declaration LawfulMonadLift is not allowed to be imported by this file.
It is defined in Init.Control.Lawful.MonadLift.Basic,
  which is imported by Init.Control.Lawful.MonadLift.Lemmas,
  which is imported by Init.Control.Lawful.MonadLift.Instances,
  which is imported by Init.Control.Lawful.MonadLift,
  which is imported by Init.Control.Lawful,
  which is imported by Init.Control,
  which is imported by Init,
  which is imported by this file.

These invariants are maintained by `assert_not_exists` statements, and exist in order to ensure that "complicated" parts of the library are not accidentally introduced as dependencies of "simple" parts of the library.
-/
#guard_msgs in
assert_not_exists LawfulMonadLift

-- Test assert_not_imported with an imported module (should warn)
/--
warning: the module 'Init.Control.Lawful.MonadLift.Basic' is (transitively) imported via
Init.Control.Lawful.MonadLift.Basic,
  which is imported by Init.Control.Lawful.MonadLift.Lemmas,
  which is imported by Init.Control.Lawful.MonadLift.Instances,
  which is imported by Init.Control.Lawful.MonadLift,
  which is imported by Init.Control.Lawful,
  which is imported by Init.Control,
  which is imported by Init,
  which is imported by this file.
-/
#guard_msgs in
assert_not_imported Init.Control.Lawful.MonadLift.Basic

-- Test #check_assertions - should show the pending assertions
-- Note: The module name below is `lean.run.assertExists` (from the file path).
-- In VSCode or when run interactively, it would show `_stdin` instead.
/--
warning:
❌️ 'FooBarBaz' (declaration) asserted in 'lean.run.assertExists'.
❌️ 'NonExistent1' (declaration) asserted in 'lean.run.assertExists'.
❌️ 'NonExistent2' (declaration) asserted in 'lean.run.assertExists'.
❌️ 'Fake.Module' (module) asserted in 'lean.run.assertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions

-- Test #check_assertions! - should only show unmet assertions
/--
warning:
❌️ 'FooBarBaz' (declaration) asserted in 'lean.run.assertExists'.
❌️ 'NonExistent1' (declaration) asserted in 'lean.run.assertExists'.
❌️ 'NonExistent2' (declaration) asserted in 'lean.run.assertExists'.
❌️ 'Fake.Module' (module) asserted in 'lean.run.assertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions!
