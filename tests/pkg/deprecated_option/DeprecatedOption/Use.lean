import DeprecatedOption.Def

-- Cross-file: deprecated option without custom text
/--
warning: `test.deprecated.plain` has been deprecated
-/
#guard_msgs in
set_option test.deprecated.plain true

-- Cross-file: deprecated option with custom text
/--
warning: `test.deprecated.withText` has been deprecated: use `test.newOption` instead
-/
#guard_msgs in
set_option test.deprecated.withText 7

-- Cross-file: non-deprecated option produces no warning
#guard_msgs in
set_option test.notDeprecated false

-- set_option ... in block
/--
warning: `test.deprecated.plain` has been deprecated
-/
#guard_msgs in
set_option test.deprecated.plain true in
example := 0

-- Custom text in set_option ... in block
/--
warning: `test.deprecated.withText` has been deprecated: use `test.newOption` instead
-/
#guard_msgs in
set_option test.deprecated.withText 100 in
example := 0

-- Nested deprecated options in set_option ... in blocks
/--
warning: `test.deprecated.plain` has been deprecated
---
warning: `test.deprecated.withText` has been deprecated: use `test.newOption` instead
-/
#guard_msgs in
set_option test.deprecated.plain true in
set_option test.deprecated.withText 0 in
example := 0

-- Tactic context
/--
warning: `test.deprecated.plain` has been deprecated
-/
#guard_msgs in
example : True := by
  set_option test.deprecated.plain true in
  trivial

-- Tactic context with custom text
/--
warning: `test.deprecated.withText` has been deprecated: use `test.newOption` instead
-/
#guard_msgs in
example : True := by
  set_option test.deprecated.withText 0 in
  trivial

-- Suppressing warnings via linter.deprecated.options
#guard_msgs in
set_option linter.deprecated.options false in
set_option test.deprecated.plain true

#guard_msgs in
set_option linter.deprecated.options false in
set_option test.deprecated.withText 7

-- Suppressing in set_option ... in blocks
#guard_msgs in
set_option linter.deprecated.options false in
set_option test.deprecated.plain true in
example := 0

-- Suppressing in tactic context
#guard_msgs in
set_option linter.deprecated.options false in
example : True := by
  set_option test.deprecated.plain true in
  trivial
