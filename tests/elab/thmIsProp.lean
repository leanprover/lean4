import Lean

open Lean

/--
error: (kernel) type of theorem 'bad' is not a proposition
  Nat
-/
#guard_msgs (error) in
run_meta do
  addDecl <| .thmDecl {
    name        := `bad
    levelParams := []
    type        := mkConst ``Nat
    value       := toExpr 10
  }

theorem foo : 10 = 10 := rfl
where aux : Nat := 20

/--
info: def foo.aux : Nat :=
20
-/
#guard_msgs in
#print foo.aux


theorem foo2 : 10 = 10 :=
  let rec aux (x : Nat) : Nat := x + 1
  rfl

/--
info: def foo2.aux : Nat → Nat :=
fun x => x + 1
-/
#guard_msgs in
#print foo2.aux


/--
error: type of theorem `ugly` is not a proposition
  Nat
-/
#guard_msgs (error) in
theorem ugly : Nat := 10

/--
error: type of theorem `g` is not a proposition
  Nat → Nat
-/
#guard_msgs (error) in
mutual
theorem f (x : Nat) : x = x := rfl

theorem g (x : Nat) : Nat := x + 1
end
