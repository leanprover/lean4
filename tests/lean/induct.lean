import macros
import tactic
using Nat

theorem add_comm2 (a b : Nat) : a + b = b + a
:= induction_on b (by skip) _
