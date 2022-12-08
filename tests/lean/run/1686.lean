import Lean
open Lean Meta

def substIssue (hLocalDecl : LocalDecl) : MetaM Unit := do
  let error {α} _ : MetaM α := throwError "{hLocalDecl.type}"
  let some (_, lhs, rhs) ← matchEq? hLocalDecl.type | error ()
  error ()
