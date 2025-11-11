import Lean.Data.Fmt.Basic

open Lean.Fmt

def n := 1000 --0

def quadratic (n : Nat) : Doc :=
  if n = 0 then
    .text "line"
  else
    .maybeFlattened
      (Doc.joinUsing .nl #[quadratic (n - 1), .text "line"])

def doc := quadratic n

@[noinline]
def format : IO String := do
  return format? doc 80 100 |>.getD ""

def bench : IO Unit := do
  IO.println <| ← timeit "" format

#eval bench
