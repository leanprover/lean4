inductive Con : Type
| nil : Con
| foo : Con

inductive Conw : Con → Prop
| nilw : Conw Con.nil

example (x : Conw Con.nil) : x = Conw.nilw := by
  cases x
  trace_state
  rfl
