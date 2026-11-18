import Lean

/-!
Benchmark: a `do` block of `n` reassignments `xᵢ ← g xᵢ` that cycle through 10 `let mut` variables.
Every reassignment is a bind whose continuation is the rest of the block.
-/

open Lean Elab Command

def g (x : Nat) : StateM Nat Nat := pure (x + 1)

def mkInput (n : Nat) : String := Id.run do
  let vars := (List.range 10).map (s!"x{·}")
  let mut s := "set_option maxRecDepth 100000 in\nnoncomputable def f : StateM Nat Nat := do\n"
  for v in vars do
    s := s ++ s!"  let mut {v} := 0\n"
  for i in [0:n] do
    s := s ++ s!"  x{i % 10} ← g x{i % 10}\n"
  return s ++ s!"  pure ({" + ".intercalate vars})\n"

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 800 else 20
  match Parser.runParserCategory (← getEnv) `command (mkInput n) with
  | .ok stx => elabCommand stx
  | .error e => throwError e

#bench
