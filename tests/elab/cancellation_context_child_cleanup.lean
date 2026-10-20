import Std.Sync

/-!
Cancelling a child `CancellationContext` must remove it from its parent's children, so that a
long-lived root that forks and cancels many children does not grow without bound.
-/

open Std

#eval show IO Unit from do
  let root ← CancellationContext.new
  for _ in [0:1000] do
    let child ← root.fork
    child.cancel .cancel
  let children ← root.state.atomically do
    return ((← get).tokens.get? root.id).map (·.2.size)
  unless children == some 0 do
    throw <| IO.userError s!"root still lists {children} children"
