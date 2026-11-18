import Lean

/-!
Benchmark: `n` nested `if b i then acc := acc + i; …` statements, each followed by
`acc := acc * (i + 2)`. Every level has a continuation, so the join points nest `n` deep, and the
control-flow information of every level covers all deeper levels.
-/

open Lean Elab Command

set_option maxRecDepth 100000

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 160 else 5
  let acc := mkIdent `acc
  let mut inner : Array (TSyntax ``Parser.Term.doSeqItem) :=
    #[← `(Parser.Term.doSeqItem| $acc:ident := 0)]
  for i in (List.range n).reverse do
    inner := #[← `(Parser.Term.doSeqItem| if b $(quote i) then
                    $acc:ident := $acc + $(quote i)
                    $inner*),
               ← `(Parser.Term.doSeqItem| $acc:ident := $acc * $(quote (i + 2)))]
  elabCommand (← `(noncomputable def $(mkIdent `f) (b : Nat → Bool) : StateM Nat Nat := do
    let mut $acc : Nat := 0
    $inner*
    pure $acc))

#bench
