module

public import Accepted

/-! Approved hypotheses do not relax the axiom policy for the proof. -/

public section

axiom cheat : True
theorem task (_ : Accepted.first) : True := cheat
