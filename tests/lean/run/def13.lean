inductive vec (A : Type) : nat → Type
| nil {} : vec 0
| cons   : Π {n}, A → vec n → vec (n+1)

open vec

variables {A : Type}
variables f : A → A → A

definition map_head_1 : ∀ {n}, vec A n → vec A n → vec A n
| .(0)     nil nil                       := nil
| .(n+1) (@cons .(A) n a va) (cons b vb) := cons (f a b) va

example : map_head_1 f nil nil = nil :=
rfl

example (a b : A) (n : nat) (va vb : vec A n) : map_head_1 f (cons a va) (cons b vb) = cons (f a b) va :=
rfl
