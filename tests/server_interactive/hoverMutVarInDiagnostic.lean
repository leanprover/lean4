/-!
Regression test: in an error message that mentions a `mut` variable, the rendered name carries
hover info (a `subexprPos`/`__rpcref`-tagged subexpression) so that hovering over it in the
infoview reveals its type and "Go to Definition" jumps to the original `let mut` binding.
-/

example : Id Nat := do
  let mut x := 0
  let x := 1
  pure x
--^ collectDiagnostics
--^ interactiveDiagnostics
