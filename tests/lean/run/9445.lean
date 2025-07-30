axiom A : Prop

@[simp] def Foo.T := True
@[simp] def Bar.T := True

namespace ex0
@[local simp] axiom a : A ↔ True
example : A := by simp
end ex0

namespace ex1
@[local simp] axiom test.a : A ↔ True
example : A := by simp -- fails
end ex1
