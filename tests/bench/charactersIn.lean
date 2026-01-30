module
import Lean
meta import Lean.Data.FuzzyMatching
open Lean Elab

def TURNS : Nat := 20

def bench (pattern : String) : TermElabM Unit := do
  let env ← getEnv
  -- IO.println s!"{env.constants.size} decls"
  let list := env.constants.toList |>.map fun (n, _) => n.toString
  IO.println s!"Matching {list.length * TURNS} decls"
  for _ in 0...TURNS do
    let mut n := 0
    for name in list do
      if pattern.charactersIn name then n := n + 1
    IO.println s!"{n} matches"

set_option profiler true
#eval! bench "L"
#eval! bench "Lean."
#eval! bench "Lean.Expr"
#eval! bench "Lean.Expr.const"
