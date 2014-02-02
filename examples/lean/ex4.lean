import Int
import tactic
set_option simplifier::unfold true -- allow the simplifier to unfold definitions
definition a : Nat := 10
theorem T1 : a > 0 := (by simp)
