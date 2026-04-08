example (p q : Prop) : p ∧ q → p := by
  refine fun ⟨a, b⟩ => a

example (p q : Prop) : p ∧ q → p := by
  refine fun a => ?hp
  trace_state
  exact a.1

example (p q : Prop) : p ∧ q → p := by
  refine fun ⟨a, b⟩ => a

example (p q : Prop) : p ∧ q → p := by
  refine fun ⟨a, b⟩ => ?hp
  trace_state
  exact a

example (p q : Prop) : p ∧ q → p := by
  refine fun a => ?hp
  case hp => exact a.1

example (p q : Prop) : p ∧ q → p := by
  refine fun ⟨a, b⟩ => ?hp
  case hp => exact a

example (p q : Prop) : p ∧ q → p := by
  refine λ ⟨a, b⟩ => ?hp
  trace_state
  exact a
