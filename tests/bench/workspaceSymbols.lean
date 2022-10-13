import Lean
open Lean Elab

def bench (pattern : String) : TermElabM Unit := do
  let env ← getEnv
  let mut n := 0
  IO.println s!"{env.constants.size} decls"
  for (c, _) in env.constants.toList do
    if Lean.FuzzyMatching.fuzzyMatch pattern c.toString then n := n + 1
  IO.println s!"{n} matches"

set_option profiler true
#eval bench "L"
#eval bench "Lean."
#eval bench "Lean.Expr"
#eval bench "Lean.Expr.const"
