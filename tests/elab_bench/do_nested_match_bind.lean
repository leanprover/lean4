import Lean

/-!
Benchmark: a `do` block of `n` nested levels
`match (← do let a ← g i; pure a) with | .some r => pure r | none => (do …)`.
The continuation of each bind refers to the rest of the block through assigned metavariables.
The time for `2n` levels should be about twice the time for `n` levels.
-/

open Lean Elab Command

def g (i : Nat) : StateM Nat (Option Nat) := pure (some i)

def indent (k : Nat) : String := "".pushn ' ' (2 * k)

def mkInput (n : Nat) : String := Id.run do
  let mut s := "set_option maxRecDepth 100000 in\nnoncomputable def f : StateM Nat Nat := do\n"
  for i in [0:n] do
    s := s ++ s!"{indent (i+1)}match (← do let a ← g {i}; pure a) with\n"
    s := s ++ s!"{indent (i+1)}| .some r => pure r\n{indent (i+1)}| none => (do\n"
  return s ++ indent (n+1) ++ "pure 0" ++ "".pushn ')' n ++ "\n"

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 400 else 20
  match Parser.runParserCategory (← getEnv) `command (mkInput n) with
  | .ok stx => elabCommand stx
  | .error e => throwError e

#bench
