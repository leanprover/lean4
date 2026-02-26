-- Auxiliary definitions nested in theorems must be defs

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
