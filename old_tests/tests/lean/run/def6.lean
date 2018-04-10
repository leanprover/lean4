
inductive vec (A : Type) : nat → Type
| nil {} : vec 0
| cons   : Π {n}, A → vec n → vec (n+1)

open vec

definition h {A : Type} : ∀ {n}, vec A (n+1) → A
| n (cons a v) := a

definition t {A : Type} : ∀ {n}, vec A (n+1) → vec A n
| n (cons a v) := v

example {A n} (a : A) (v : vec A n) : h (cons a v) = a :=
rfl

example {A n} (a : A) (v : vec A n) : t (cons a v) = v :=
rfl
