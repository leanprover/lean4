axiom A : Prop

@[simp] def Foo.T := True
@[simp] def Bar.T := True
axiom ax : A ↔ True

namespace ex0
@[local simp] axiom a : A ↔ True
example : A := by simp
end ex0

namespace ex1
set_option linter.unusedVariables false in
@[local simp] def a : A ↔ True := ax
example : A := by simp
end ex1

namespace ex2
open Nat in
@[local simp] def a : A ↔ True := ax
example : A := by simp
end ex2

namespace ex3
@[local simp] axiom test.a : A ↔ True
example : A := by simp
end ex3
