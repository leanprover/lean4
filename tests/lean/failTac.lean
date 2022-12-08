example (a b : Nat) : False := by
  fail -- Error

example (a b : Nat) : False := by
  fail "giving up" -- Error

example (a b : Nat) : True := by
  first
   | fail "giving up"
   | constructor

example (a b : Nat) : True ∧ False := by
  constructor
  fail "failing here"
