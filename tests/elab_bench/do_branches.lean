import Lean

/-!
Benchmark: two wide branching families, each followed by a continuation that reads 4 `let mut`
variables.
* `arms`: one `match k with` of `n` arms, where every arm reassigns one variable.
* `elseIfs`: one chain of `n` `if k = i then … else if …` branches, where every branch reassigns
  one variable.
-/

open Lean Elab Command

def vars : List String := (List.range 4).map (s!"x{·}")

def header (name : String) : String := Id.run do
  let mut s := s!"set_option maxRecDepth 100000 in\n\
    noncomputable def {name} (k : Nat) : StateM Nat Nat := do\n"
  for v in vars do
    s := s ++ s!"  let mut {v} : Nat := 0\n"
  return s

def footer : String := s!"  pure ({" + ".intercalate vars})\n"

def mkArms (n : Nat) : String := Id.run do
  let mut s := header "arms" ++ "  match k with\n"
  for i in [0:n] do
    s := s ++ s!"  | {i} => x{i % 4} := {i}\n"
  return s ++ "  | _ => x0 := 1\n" ++ footer

def mkElseIfs (n : Nat) : String := Id.run do
  let mut s := header "elseIfs"
  for i in [0:n] do
    s := s ++ s!"  {if i == 0 then "if" else "else if"} k = {i} then\n    x{i % 4} := {i}\n"
  return s ++ "  else\n    x0 := 1\n" ++ footer

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 500 else 10
  for input in [mkArms n, mkElseIfs n] do
    match Parser.runParserCategory (← getEnv) `command input with
    | .ok stx => elabCommand stx
    | .error e => throwError e

#bench
