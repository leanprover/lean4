import Lean

/-!
Benchmark: two `for` loop families.
* `nested`: `d` nested `for` loops whose bodies `continue`, `break`, `return` early and reassign a
  `let mut` variable.
* `manyMut`: one `for` loop that reassigns `m` `let mut` variables, so the loop state is an
  `m`-tuple.
-/

open Lean Elab Command

set_option maxRecDepth 100000

def elabNested (d : Nat) : CommandElabM Unit := do
  let acc := mkIdent `acc
  let mut inner : Array (TSyntax ``Parser.Term.doSeqItem) := #[]
  for i in (List.range d).reverse do
    let y := mkIdent (.mkSimple s!"y{i}")
    inner := #[← `(Parser.Term.doSeqItem| for $y:ident in xs do
                    if $y = $(quote i) then continue
                    if $y = $(quote (i + 1)) then break
                    if $acc > $(quote (1000 + i)) then return $acc
                    $acc:ident := $acc + $y
                    $inner*)]
  elabCommand (← `(noncomputable def $(mkIdent `nested) (xs : List Nat) : StateM Nat Nat := do
    let mut $acc : Nat := 0
    $inner*
    pure $acc))

def elabManyMut (m : Nat) : CommandElabM Unit := do
  let xs := (Array.range m).map fun j => mkIdent (.mkSimple s!"x{j}")
  let decls ← xs.mapM fun x => `(Parser.Term.doSeqItem| let mut $x : Nat := 0)
  let body ← xs.mapM fun x => `(Parser.Term.doSeqItem| $x:ident := $x + y)
  let sum ← (xs.extract 1).foldlM (init := (xs[0]! : Term)) fun t x => `($t + $x)
  elabCommand (← `(noncomputable def $(mkIdent `manyMut) (ys : List Nat) : StateM Nat Nat := do
    $decls*
    for y in ys do
      $body*
    pure $sum))

elab "#bench" : command => do
  let bench := (← IO.getEnv "TEST_BENCH") == some "1"
  elabNested (if bench then 48 else 3)
  elabManyMut (if bench then 160 else 10)

#bench
