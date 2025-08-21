axiom A : Prop

@[simp] def Foo.T := True
@[simp] def Bar.T := True

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

namespace ex3
@[local simp] axiom Foo.a : A ↔ True
example : A := by simp
end ex3

axiom A : Prop
namespace ex
axiom test.a : A ↔ True
set_option pp.mvars true in
attribute [local simp] test.a
example : A := by simp
end ex
