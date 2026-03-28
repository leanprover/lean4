axiom A : Prop

namespace ex0
@[local simp] axiom a : A ↔ True
example : A := by simp
end ex0

namespace ex1
set_option linter.unusedVariables false in
@[local simp] axiom a : A ↔ True
example : A := by simp
end ex1

namespace ex2
open Nat in
@[local simp] axiom a : A ↔ True
example : A := by simp
end ex2

namespace ex3
@[local simp] axiom Foo.a : A ↔ True
example : A := by simp
end ex3

namespace ex4
axiom test.a : A ↔ True
set_option pp.mvars true in
attribute [local simp] test.a
example : A := by simp
end ex4

namespace ex5
section
@[local simp] axiom Foo.a : A ↔ True
end
/--
  error: `simp` made no progress
-/
#guard_msgs in
example : A := by simp
end ex5

namespace ex6
namespace Foo
axiom a : A ↔ True
attribute [local simp] a
end Foo
/--
  error: `simp` made no progress
-/
#guard_msgs in
example : A := by simp
end ex6
