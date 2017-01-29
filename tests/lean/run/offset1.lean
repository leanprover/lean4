open nat

inductive {u} vec (α : Type u) : ℕ → Type u
| nil {} : vec 0
| cons   : α → Π {n : nat}, vec n → vec (n+1)

namespace vec
def head {α : Type*} : Π {n : ℕ}, vec α (n+1) → α
| n (cons x xs) := x
end vec

constants (dret : Π {n : ℕ}, vec nat n → (vec nat n → nat) → nat)
axiom dret_spec : Π {n : ℕ} (xs : vec nat n) (f : vec nat n → nat), dret xs f = f xs

example (v : vec nat (id 1)) : dret v vec.head = vec.head v :=
by rw dret_spec
