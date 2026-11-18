import Lean

/-!
Benchmark: `n` nested `try … catch … finally` blocks in `ExceptT String (StateM Nat)`. Every
level reassigns a `let mut` variable, can `throw`, and has a continuation after the inner level.
-/

open Lean Elab Command

def indent (k : Nat) : String := "".pushn ' ' (2 * k)

def mkInput (n : Nat) : String := Id.run do
  let mut s := "set_option maxRecDepth 100000 in\n\
    noncomputable def f : ExceptT String (StateM Nat) Nat := do\n  let mut acc : Nat := 0\n"
  for i in [0:n] do
    s := s ++ s!"{indent (i+1)}try\n{indent (i+2)}acc := acc + {i}\n"
    s := s ++ s!"{indent (i+2)}if acc > {i} then throw \"e{i}\"\n"
  for i in (List.range n).reverse do
    s := s ++ s!"{indent (i+2)}acc := acc + 1\n"
    s := s ++ s!"{indent (i+1)}catch _ =>\n{indent (i+2)}acc := acc * 2\n"
    s := s ++ s!"{indent (i+1)}finally\n{indent (i+2)}modify (· + 1)\n"
  return s ++ "  pure acc\n"

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 24 else 3
  match Parser.runParserCategory (← getEnv) `command (mkInput n) with
  | .ok stx => elabCommand stx
  | .error e => throwError e

#bench
