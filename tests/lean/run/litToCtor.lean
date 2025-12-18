import Lean
open Lean Meta
def test [ToExpr α] (a : α) : MetaM Unit := do
   let a := toExpr a
   let c ← litToCtor a
   check c
   IO.println s!"{← ppExpr c}"
   assert! (← isDefEq c a)
/--
info: Nat.succ 9
-/
#guard_msgs in
#eval test 10
/--
info: Nat.succ 0
-/
#guard_msgs in
#eval test 1
/--
info: Nat.zero
-/
#guard_msgs in
#eval test 0
/--
info: Int.negSucc 1
-/
#guard_msgs in
#eval test (-2)
/--
info: Int.negSucc 0
-/
#guard_msgs in
#eval test (-1)
/--
info: Int.ofNat 0
-/
#guard_msgs in
#eval test (0 : Int)
/--
info: Int.ofNat 3
-/
#guard_msgs in
#eval test (3 : Int)
/--
info: ⟨3, ⋯⟩
-/
#guard_msgs in
#eval test (3 : Fin 5)
/--
info: ⟨0, ⋯⟩
-/
#guard_msgs in
#eval test (0 : Fin 5)
/--
info: ⟨1, ⋯⟩
-/
#guard_msgs in
#eval test (6 : Fin 5)
