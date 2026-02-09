module

/-! Tests that ctorIdx and constructor elims are exposed, i.e. reduce properly -/

example : Nat.ctorIdx 0 = 0 := rfl

example : Nat.succ.elim 1 rfl (fun n => n) = 0 := rfl
