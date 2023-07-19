--

axiom p {α β} : α → β → Prop
axiom foo {α β} (a : α) (b : β) : p a b

example : p 0 0 := by simp [foo]
example (a : Nat) : p a a := by simp [foo a]
example : p 0 0 := by simp [foo 0]
example : p 0 0 := by simp [foo 0 0]
example : p 0 0 := by
  fail_if_success
    simp [foo 1] -- will not simplify
  simp [foo 0]
example : p 0 0 ∧ p 1 1 := by
  simp [foo 1]
  trace_state
  simp [foo 0]

namespace Foo

axiom p {α} : α → Prop
axiom foo {α} [ToString α] (n : Nat) (a : α) : p a

example : p 0 := by simp [foo 0]
example : p 0 ∧ True := by simp [foo 0]

end Foo
