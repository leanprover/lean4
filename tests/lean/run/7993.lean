/-!
# Warn about visibility (and namespace/type) changes in deprecation lints

https://github.com/leanprover/lean4/issues/7993

Deprecation lints should indicate if an updated constant is in a different namespace, is protected,
or has a different type from the deprecated one.
-/

set_option linter.deprecated true

abbrev Foo := Nat

namespace Foo

protected def bar : Foo → Foo
  | 0 => 0
  | n + 1 => Foo.bar n + 1

theorem bar_rfl : Foo.bar = Foo.bar := rfl

@[deprecated Foo.bar (since := "2025-01-01")]
def foo : Foo → Foo := id

end Foo

/--
warning: `Foo.foo` has been deprecated: Use `Foo.bar` instead

Note: `Foo.bar` is protected. References to this constant must include its prefix `Foo` even when inside its namespace.
-/
#guard_msgs in
open Foo in
example := foo

abbrev Bar := Nat

@[deprecated Foo.foo (since := "2025-01-01")]
def Bar.bar : Bar → Bar := id

abbrev b : Bar := 31

/--
warning: `Bar.bar` has been deprecated: Use `Foo.foo` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.bar` to `Foo.foo x`).
-/
#guard_msgs in
example := b.bar

/--
warning: `Bar.bar` has been deprecated: Use `Foo.foo` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.bar` to `foo x`).
-/
#guard_msgs in
open Foo in
example := b.bar

set_option linter.deprecated false in
@[deprecated Foo.bar_rfl (since := "2025-01-01")]
theorem Bar.bar_rfl : Bar.bar = Bar.bar := rfl

/--
warning: `Bar.bar_rfl` has been deprecated: Use `Foo.bar_rfl` instead

Note: The updated constant has a different type:
  Foo.bar = Foo.bar
instead of
  Bar.bar = Bar.bar

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.bar_rfl` to `Foo.bar_rfl x`).
-/
#guard_msgs in
example := Bar.bar_rfl

namespace A.B
protected def C := ()

@[deprecated B.C (since := "2025-01-01")]
def D := ()
end A.B

/--
warning: `A.B.D` has been deprecated: Use `A.B.C` instead

Note: `A.B.C` is protected. References to this constant must include at least the last component `B` of its prefix `A.B` even when inside its namespace.
-/
#guard_msgs in
open A B in
example := D
