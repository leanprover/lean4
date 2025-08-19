axiom A : Prop
namespace ex1
namespace foo
end_local_scope
@[local simp] axiom bar : A ↔ true
end foo

theorem baz : A ↔ true := by simp
end ex1

namespace ex2
namespace foo
@[local simp] axiom bar : A ↔ true
end foo
/--
  error: unsolved goals
⊢ A
-/
#guard_msgs in
theorem baz : A ↔ true := by simp
end ex2
