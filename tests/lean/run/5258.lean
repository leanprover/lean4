/-!
# Detect when `export` may lead to ambiguities
https://github.com/leanprover/lean4/issues/5258
-/

set_option linter.aliasConflict true

theorem Foo.bar : True := .intro

export Foo (bar)

/-!
Warning when adding a declaration on top of an alias.
-/
/--
warning: 'bar' exists as an alias for the following declaration(s) and may lead to ambiguities: 'Foo.bar'
note: this linter can be disabled with `set_option linter.aliasConflict false`
-/
#guard_msgs in
theorem bar : True := .intro

theorem baz : True := .intro

theorem Foo.baz : True := .intro

/-!
Warning when adding an alias on top of a declaration.
-/
/--
warning: 'baz' is an existing declaration and this alias may lead to ambiguities
note: this linter can be disabled with `set_option linter.aliasConflict false`
-/
#guard_msgs in
export Foo (baz)

theorem Foo'.baz : True := .intro

/-!
Warning when adding an alias on top of both an alias and a declaration.
-/
/--
warning: 'baz' is an existing declaration and this alias may lead to ambiguities
note: this linter can be disabled with `set_option linter.aliasConflict false`
---
warning: 'baz' already exists as an alias for the following declaration(s) and may lead to ambiguities: 'Foo.baz'
note: this linter can be disabled with `set_option linter.aliasConflict false`
-/
#guard_msgs in
export Foo' (baz)
