import Lean

/-!
`diagnostics` must not change the outcome of the type checks for metavariable assignments: when a
check fails, it compares the types again at `.default` transparency to explain the failure, and that
comparison must not assign the metavariables in the types.
-/

open Lean Meta

class MyAdd (α : Type) where
  add : α → α → α

instance : MyAdd Nat := ⟨Nat.add⟩

/-- Unfolds at `.implicit` transparency, but not at `.instances` transparency. -/
@[implicit_reducible] def Copy (α : Type) := α

/-- Unfolds only at `.default` transparency. -/
def Syn (α : Type) : Type := α

/--
Whether a rejected assignment of `v` to a fresh `?m : mkType ?α` assigns `?α`. The assignment is
made at reducible transparency, as in `simp` or `rw`, since the type check never lowers it.
-/
def assignsTypeMVar (mkType : Expr → Expr) (v : Expr) : MetaM Bool := do
  let α ← mkFreshExprMVar (mkSort 1)
  let m ← mkFreshExprMVar (mkType α)
  if ← withReducible <| isExprDefEqAux m v then throwError "assignment accepted"
  return !(← instantiateMVars α).isMVar

/-- The check for class-typed metavariables (`backward.isDefEq.respectTransparency.instanceTypes`). -/
def assignsInstanceTypeMVar : MetaM Bool :=
  assignsTypeMVar (fun α => mkApp (mkConst ``MyAdd) (mkApp (mkConst ``Copy) α))
    (mkConst ``instMyAddNat)

/-- The check for other metavariables (`backward.isDefEq.respectTransparency.types`). -/
def assignsOrdinaryTypeMVar : MetaM Bool :=
  assignsTypeMVar (mkApp (mkConst ``Syn)) (mkConst ``Nat.zero)

/-- info: false -/
#guard_msgs in
#eval assignsInstanceTypeMVar

/-- info: false -/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 1000 in
#eval assignsInstanceTypeMVar

/-- info: false -/
#guard_msgs in
#eval assignsOrdinaryTypeMVar

/-- info: false -/
#guard_msgs in
set_option diagnostics true in
set_option diagnostics.threshold 1000 in
#eval assignsOrdinaryTypeMVar
