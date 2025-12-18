import Lean

class P (n : Nat)

theorem foo (n : Nat) [P n] : True := trivial

-- This should fail, as by default `apply` does not allow synthesis failures.
example : True := by
  apply foo 37

open Lean Meta Elab Tactic Term

/--
In mathlib4 we add the syntax:

`apply (config := cfg) e` is like `apply e` but allows you to provide a configuration
`cfg : ApplyConfig` to pass to the underlying apply operation.

For this test we just hard code the `allowSynthFailures` option into `apply'`.
-/
elab "apply'" e:term : tactic => do
  evalApplyLikeTactic (·.apply · { allowSynthFailures := true }) e

def instP (n : Nat) : P n := {}

example : True := by
  apply' foo
  apply instP
  exact 37

