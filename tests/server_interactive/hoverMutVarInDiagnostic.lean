/-!
Regression tests for hover info on variable names in `do`-elaborator diagnostics. Each
example asserts on the rendered JSON: whether the name carries a `subexprPos`/`__rpcref`
hover tag (multi-mut shadowing and a regular `let`-bound variable: yes; an undeclared
variable: no) and which name the message shows.
-/

example : Id Nat := do
  let mut x := 0
  let mut y := 0
  let x := 1
  pure (x + y)

example : Id Nat := do
  let y := 0
  y := 1
  pure y

example : Id Nat := do
  q := 1
  pure 0
--^ collectDiagnostics
--^ interactiveDiagnostics
