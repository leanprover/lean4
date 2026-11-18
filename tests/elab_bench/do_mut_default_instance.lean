import Lean

/-!
Benchmark: a `do` block of `n` statements `if b i then xⱼ := xⱼ + i` over 20 variables declared
as `let mut xⱼ := 0`. The type of every `xⱼ` stays a metavariable until the default instance for
`OfNat` applies at the end of the block, so every join point has metavariables in its type and
every `+` waits for the default instance.
-/

open Lean Elab Command

set_option maxRecDepth 100000

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 60 else 5
  let xs := (Array.range 20).map fun j => mkIdent (.mkSimple s!"x{j}")
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x := 0)
  let ifs ← (Array.range n).mapM fun i =>
    let x := xs[i % 20]!
    `(Parser.Term.doSeqItem| if b $(quote i) then $x:ident := $x + $(quote i))
  let sum ← (xs.extract 1).foldlM (init := (xs[0]! : Term)) fun t x => `($t + $x)
  elabCommand (← `(noncomputable def $(mkIdent `f) (b : Nat → Bool) : StateM Nat Nat := do
    $decls*
    $ifs*
    pure $sum))

#bench
