import Lean

/-!
Benchmark: a `do` block of `n` statements `if b i then xⱼ := xⱼ + i` over 20 `let mut` variables
of type `Nat`. Every `if` has a continuation, so every `if` introduces a join point whose
parameters are the reassigned variables.
-/

open Lean Elab Command

set_option maxRecDepth 100000

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 400 else 10
  let xs := (Array.range 20).map fun j => mkIdent (.mkSimple s!"x{j}")
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x : Nat := 0)
  let ifs ← (Array.range n).mapM fun i =>
    let x := xs[i % 20]!
    `(Parser.Term.doSeqItem| if b $(quote i) then $x:ident := $x + $(quote i))
  let sum ← (xs.extract 1).foldlM (init := (xs[0]! : Term)) fun t x => `($t + $x)
  elabCommand (← `(noncomputable def $(mkIdent `f) (b : Nat → Bool) : StateM Nat Nat := do
    $decls*
    $ifs*
    pure $sum))

#bench
