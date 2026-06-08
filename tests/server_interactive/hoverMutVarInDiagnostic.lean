/-!
Regression tests for hover/go-to-def info on variable names in `do`-elaborator diagnostics.

* A shadowing error involving multiple `mut` variables identifies the right one, both in the
  rendered message text (`mutable variable \`x\` cannot be shadowed`) and via the hover info
  attached to the printed name.
* A "cannot be mutated" error on a regular `let`-bound variable carries hover info pointing
  at the `let` binding.
* A "cannot be mutated" error on an *undeclared* variable falls back to plain text — the
  `none` branch of `MessageData.ofUserName`.
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
