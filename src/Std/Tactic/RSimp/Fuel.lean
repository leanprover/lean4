import Lean

open Lean Meta

def lots_of_fuel : Nat := 9223372036854775807

def rsimp_iterate {α : Sort u} (x : α) (f : α → α) : α :=
  Nat.rec x (fun _ ih => f ih) lots_of_fuel

theorem reduce_with_fuel {α : Sort u} {x : α} {f : α → α} (h : x = f x) :
    x = rsimp_iterate x f := by
    unfold rsimp_iterate
    exact Nat.rec rfl (fun _ ih => h.trans (congrArg f ih)) lots_of_fuel

def recursionToFuel? (lhs rhs proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let f ← kabstract rhs lhs
  if f.hasLooseBVars then
    let t ← inferType lhs
    let u ← getLevel t
    let f := mkLambda `ih .default t f
    let rhs' := mkApp3 (.const ``rsimp_iterate [u]) t lhs f
    let proof' := mkApp4 (.const ``reduce_with_fuel [u]) t lhs f proof
    return some (rhs', proof')
  else
    return none

def recursionToFuel (lhs rhs proof : Expr) : MetaM (Expr × Expr) := do
  if let some (rhs', proof') ← recursionToFuel? lhs rhs proof then
    return (rhs', proof')
  else
    -- Not (obviously) recursive
    return (rhs, proof)
