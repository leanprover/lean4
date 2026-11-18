module
import Lean.CoreM
import Lean.Meta.Transform

open Lean

/-!
Asserts that `Core.transform` preserves sharing when terms are not modified
-/

def mkTree : Expr :=
  let a := mkConst `a
  let b := mkConst `b
  let inner := mkApp2 (mkConst `f) a b
  mkApp3 (mkConst `g) inner (mkApp (mkConst `h) inner) b

unsafe def checkSharingPreserved : CoreM Unit := do
  let input := mkTree
  let output ← Core.transform input (pre := fun _ => return .continue) (post := fun e => return .done e)
  if ptrEq input output then
    logInfo "Sharing preserved"
  else
    throwError "Sharing not preserved"

/-- info: Sharing preserved -/
#guard_msgs in
#eval checkSharingPreserved
