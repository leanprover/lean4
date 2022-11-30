--

axiom P {α β} : α → β → Prop
axiom foo {α β} (a : α) (b : β) : P a b

example : P 0 0 := by simp [foo]
example (a : Nat) : P a a := by simp [foo a]
example : P 0 0 := by simp [foo 0]
example : P 0 0 := by simp [foo 0 0]
example : P 0 0 := by
  simp [foo 1] -- will not simplify
  simp [foo 0]
example : P 0 0 ∧ P 1 1 := by
  simp [foo 1]
  trace_state
  simp [foo 0]

namespace Foo

axiom P {α} : α → Prop
axiom foo {α} [ToString α] (n : Nat) (a : α) : P a

example : P 0 := by simp [foo 0]
example : P 0 ∧ True := by simp [foo 0]

end Foo
