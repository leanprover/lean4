import Lean

open Lean Meta

-- In a new MCtx depth, metavariables should not be assignable by `isDefEq`.

run_meta do
  let m ← mkFreshExprMVar (Expr.sort levelOne) MetavarKind.syntheticOpaque
  withAssignableSyntheticOpaque do
  withNewMCtxDepth do
  let eq ← isDefEq m (.const ``Nat [])
  Lean.logInfo m! "{eq}"
