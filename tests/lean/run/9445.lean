axiom A : Prop
namespace ex1
/--
warning: Local attributes in implicit sections are discouraged. Consider using `attribute [local] ...` after the current command.
-/
#guard_msgs in
@[local simp] axiom test.a : A ↔ True

axiom test.b : A ↔ True
@[local simp] axiom c : A ↔ True
