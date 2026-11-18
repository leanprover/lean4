import Lean

/-!
Benchmark: `n` nested `if b i then acc := acc + i; …` statements, each followed by
`acc := acc * (i + 2)`. Every level has a continuation, so the join points nest `n` deep, and the
control-flow information of every level covers all deeper levels.
-/

open Lean Elab Command

def indent (k : Nat) : String := "".pushn ' ' (2 * k)

def mkInput (n : Nat) : String := Id.run do
  let mut s := "set_option maxRecDepth 100000 in\n\
    noncomputable def f (b : Nat → Bool) : StateM Nat Nat := do\n  let mut acc : Nat := 0\n"
  for i in [0:n] do
    s := s ++ s!"{indent (i+1)}if b {i} then\n{indent (i+2)}acc := acc + {i}\n"
  s := s ++ s!"{indent (n+1)}acc := 0\n"
  for i in (List.range n).reverse do
    s := s ++ s!"{indent (i+1)}acc := acc * {i+2}\n"
  return s ++ "  pure acc\n"

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 160 else 5
  match Parser.runParserCategory (← getEnv) `command (mkInput n) with
  | .ok stx => elabCommand stx
  | .error e => throwError e

#bench
