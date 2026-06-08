/-!
Regression test: error messages from the `do` elaborator that mention a variable wrap that name
with hover info (a `subexprPos`/`__rpcref`-tagged subexpression). The first `example` triggers
the shadowing error, where the printed `x` should jump to the `let mut x := 0` binding.
The second `example` triggers the "cannot be mutated" error, where the printed `y` should jump
to the `let y := 0` binding.
-/

example : Id Nat := do
  let mut x := 0
  let x := 1
  pure x

example : Id Nat := do
  let y := 0
  y := 1
  pure y
--^ collectDiagnostics
--^ interactiveDiagnostics
