/-!
Regression tests for IDE integration of `mut` variables in `do`-elaborator diagnostics.

The `interactiveDiagnostics` examples assert on the *structural shape* of the rendered
diagnostic JSON: the presence or absence of a `subexprPos`/`__rpcref` tag on each variable
name. They do not resolve the RPC ref back to its `FVarId`, so a bug that wired the hover
info to the wrong expression would still pass these checks. What they do catch: forgetting
to attach hover info at all (the rpcref would disappear), looking up the wrong `MutVar` for
a shadowing message (the rendered name would change), and breaking the plain-text fallback
for undeclared names.

  - Multi-mut shadowing: the message text confirms `findMutVar?` picked the `x`, not the `y`.
  - Regular `let`-bound variable: each occurrence of the name gets an rpcref attached via
    the `some decl` branch of `MessageData.ofUserName`.
  - Undeclared variable: each occurrence renders as plain text via the `none` branch.

The trailing `documentHighlight` example closes the loop on the alias-chain side: with two
`mut` variables in scope and an explicit reassignment, highlighting at the `let mut x`
source position should pick up only the `x` occurrences, not the `y` ones. This exercises
the `FVarAliasInfo` records populated by `MutVar.mkAliasInfo`.
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

example : Id Nat := Id.run do
  let mut x := 0
        --^ textDocument/documentHighlight
  let mut y := 0
  x := 1
  pure (x + y)
