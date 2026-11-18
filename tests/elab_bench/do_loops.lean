import Lean

/-!
Benchmark: two `for` loop families.
* `nested`: `d` nested `for` loops whose bodies `continue`, `break`, `return` early and reassign a
  `let mut` variable.
* `manyMut`: one `for` loop that reassigns `m` `let mut` variables, so the loop state is an
  `m`-tuple.
-/

open Lean Elab Command

def indent (k : Nat) : String := "".pushn ' ' (2 * k)

def mkNested (d : Nat) : String := Id.run do
  let mut s := "set_option maxRecDepth 100000 in\n\
    noncomputable def nested (xs : List Nat) : StateM Nat Nat := do\n  let mut acc : Nat := 0\n"
  for i in [0:d] do
    s := s ++ s!"{indent (i+1)}for y{i} in xs do\n"
    s := s ++ s!"{indent (i+2)}if y{i} = {i} then continue\n"
    s := s ++ s!"{indent (i+2)}if y{i} = {i+1} then break\n"
    s := s ++ s!"{indent (i+2)}if acc > {1000+i} then return acc\n"
    s := s ++ s!"{indent (i+2)}acc := acc + y{i}\n"
  return s ++ "  pure acc\n"

def mkManyMut (m : Nat) : String := Id.run do
  let vars := (List.range m).map (s!"x{·}")
  let mut s := "set_option maxRecDepth 100000 in\n\
    noncomputable def manyMut (xs : List Nat) : StateM Nat Nat := do\n"
  for v in vars do
    s := s ++ s!"  let mut {v} : Nat := 0\n"
  s := s ++ "  for y in xs do\n"
  for v in vars do
    s := s ++ s!"    {v} := {v} + y\n"
  return s ++ s!"  pure ({" + ".intercalate vars})\n"

elab "#bench" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  for input in [mkNested (if bench then 48 else 3), mkManyMut (if bench then 160 else 10)] do
    match Parser.runParserCategory (← getEnv) `command input with
    | .ok stx => elabCommand stx
    | .error e => throwError e

#bench
