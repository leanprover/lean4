import Lean

elab "foo " n:num : tactic => do
  dbg_trace n.getNat

example : True := by
  foo
