import Lean

/-!
Benchmark: two wide branching families, each followed by a continuation that reads 4 `let mut`
variables.
* `arms`: one `match k with` of `n` arms, where every arm reassigns one variable.
* `elseIfs`: one chain of `n` `if k = i then … else if …` branches, where every branch reassigns
  one variable.
-/

open Lean Elab Command

set_option maxRecDepth 100000

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 500 else 10
  let xs := (Array.range 4).map fun j => mkIdent (.mkSimple s!"x{j}")
  let x0 := xs[0]!
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x : Nat := 0)
  let sum ← (xs.extract 1).foldlM (init := (x0 : Term)) fun t x => `($t + $x)
  let rhss ← (Array.range n).mapM fun i =>
    let x := xs[i % 4]!
    `(doSeq| $x:ident := $(quote i))
  let pats ← (Array.range n).mapM fun i => `($(quote i))
  elabCommand (← `(noncomputable def $(mkIdent `arms) (k : Nat) : StateM Nat Nat := do
    $decls*
    match k with
    $[| $pats:term => $rhss:doSeq]*
    | _ => $x0:ident := 1
    pure $sum))
  let conds ← (Array.range n).mapM fun i => `(Parser.Term.doIfCond| k = $(quote i))
  elabCommand (← `(noncomputable def $(mkIdent `elseIfs) (k : Nat) : StateM Nat Nat := do
    $decls*
    if k = $(quote n) then $x0:ident := 0
    $[else if $conds:doIfCond then $rhss]*
    else $x0:ident := 1
    pure $sum))

#bench
