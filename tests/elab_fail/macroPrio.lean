import Lean

macro "foo!" x:term:max : term => `($x + 1)

#check foo! 0

theorem ex1 : foo! 2 = 3 :=
  rfl

macro "foo!" x:term:max : term => `($x * 2)

#check foo! 1 -- ambiguous

-- macro with higher priority
macro (priority := high) "foo!" x:term:max : term => `($x - 2)

#check foo! 2

theorem ex2 : foo! 2 = 0 :=
  rfl

-- Define elaborator with even higher priority
elab (priority := high+1) "foo!" x:term:max : term <= expectedType =>
  Lean.Elab.Term.elabTerm x expectedType

theorem ex3 : foo! 3 = 3 :=
  rfl
