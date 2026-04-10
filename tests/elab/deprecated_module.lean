/-
Tests for the `deprecated_module` command.
-/

-- Missing since (message is optional)
/--
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
deprecated_module

-- Missing since with message (also warns about duplicate since module is already marked above)
/--
warning: module is already marked as deprecated
---
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
deprecated_module "use NewModule instead"

-- No message, with since (also warns about duplicate)
/-- warning: module is already marked as deprecated -/
#guard_msgs in
deprecated_module (since := "2026-03-19")

-- Both message and since: only duplicate warning
/--
warning: module is already marked as deprecated
-/
#guard_msgs in
deprecated_module "use NewModule instead" (since := "2026-03-19")

-- Duplicate deprecated_module: warns about already being marked (standalone confirmation)
/--
warning: module is already marked as deprecated
-/
#guard_msgs in
deprecated_module "use SomethingElse instead" (since := "2026-03-20")
