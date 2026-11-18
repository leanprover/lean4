import Lean

/-!
Benchmark: `n` nested `try … catch … finally` blocks in `ExceptT String (StateM Nat)`. Every
level reassigns a `let mut` variable, can `throw`, and has a continuation after the inner level.
-/

open Lean Elab Command

set_option maxRecDepth 100000

elab "#bench" : command => do
  let n := if (← IO.getEnv "TEST_BENCH") == some "1" then 24 else 3
  let acc := mkIdent `acc
  let mut inner : Array (TSyntax ``Parser.Term.doSeqItem) := #[]
  for i in (List.range n).reverse do
    inner := #[← `(Parser.Term.doSeqItem| try
                    $acc:ident := $acc + $(quote i)
                    if $acc > $(quote i) then throw "e"
                    $inner*
                    $acc:ident := $acc + 1
                  catch _ =>
                    $acc:ident := $acc * 2
                  finally
                    modify (· + 1))]
  elabCommand (← `(noncomputable def $(mkIdent `f) : ExceptT String (StateM Nat) Nat := do
    let mut $acc : Nat := 0
    $inner*
    pure $acc))

#bench
