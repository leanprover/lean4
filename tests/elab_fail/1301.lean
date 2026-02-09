syntax "tac" : tactic
theorem a : True := by tac
#check a -- should be declared

theorem a' : True ∧ True := ⟨by tac, by tac⟩
#check a' -- should be declared

syntax "term" : term
def b (n : Nat) : Nat := term
#print b -- should be declared
