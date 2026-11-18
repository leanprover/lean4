import Lean

/-!
Benchmark: a `do` block of `n` reassignments `xᵢ ← g xᵢ` that cycle through 10 `let mut` variables.
Every reassignment is a bind whose continuation is the rest of the block.
-/

open Lean Elab Command

set_option maxRecDepth 100000

def g (x : Nat) : StateM Nat Nat := pure (x + 1)

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 800 else 20
  let xs := (Array.range 10).map fun j => mkIdent (.mkSimple s!"x{j}")
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x := 0)
  let steps ← (Array.range n).mapM fun i =>
    let x := xs[i % 10]!
    `(Parser.Term.doSeqItem| $x:ident ← g $x)
  let sum ← (xs.extract 1).foldlM (init := (xs[0]! : Term)) fun t x => `($t + $x)
  elabCommand (← `(noncomputable def $(mkIdent `f) : StateM Nat Nat := do
    $decls*
    $steps*
    pure $sum))

#bench
