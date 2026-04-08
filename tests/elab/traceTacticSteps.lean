-- Check whether all intermediate steps during tactic execution
-- can be successfully pretty-printed to trace output

set_option trace.Elab.step true

example : True := by
  skip
  trivial
