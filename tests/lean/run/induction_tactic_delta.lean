open tactic

-- This test makes sure that [foo'] is not unfolded in the major premise,
-- since [foo'] is the type of the major premise of the provided recursor.

inductive foo (n : nat)
| mk : foo

definition foo' := @foo 0
definition foo'.rec := @foo.rec

example : Pi (x : foo'), x = x :=
by do x ← intro `x,
      induction x `foo'.rec [],
      reflexivity
