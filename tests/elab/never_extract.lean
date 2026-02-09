def test1 (a : Nat) : Nat :=
  let f a :=
    dbg_trace s!"{a}"
    a
  let g a :=
    dbg_trace s!"{a + 0}"
    a
  (f a) + (g a)

/--
info: 1
1
---
info: 2
-/
#guard_msgs in
#eval test1 1

structure Twice (α : Type u) where
  first : α
  second : α
  first_eq_second : first = second

instance : Coe α (Twice α) where
  coe x := ⟨x, x, rfl⟩

/--
info: hello
hello
---
info: { first := 5, second := 5, first_eq_second := _ }
-/
#guard_msgs in
#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
