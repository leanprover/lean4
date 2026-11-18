import Lean

/-!
Benchmark: a `do` block of `n` nested levels
`match (← do let a ← g i; pure a) with | .some r => pure r | none => (do …)`.
The continuation of each bind refers to the rest of the block through assigned metavariables.
The time for `2n` levels should be about twice the time for `n` levels.
-/

open Lean Elab Command

set_option maxRecDepth 100000

def g (i : Nat) : StateM Nat (Option Nat) := pure (some i)

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 400 else 20
  let mut body ← `(doSeq| pure 0)
  for i in (List.range n).reverse do
    body ← `(doSeq| match (← do let a ← g $(quote i); pure a) with
                    | .some r => pure r
                    | none => (do $body))
  elabCommand (← `(noncomputable def $(mkIdent `f) : StateM Nat Nat := do $body))

#bench
