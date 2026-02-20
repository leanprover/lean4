

inductive Vec.{u} (α : Type u) : Nat → Type u
| nil  : Vec α 0
| cons : α → {n : Nat} → Vec α n → Vec α (n+1)

open Vec
universe u

variable {α : Type u}
variable (f : α → α → α)

def mapHead1 : {n : Nat} → Vec α n → Vec α n → Vec α n
| _, nil, nil => nil
| _, cons a va, cons b bv => cons (f a b) va

theorem ex1 : mapHead1 f nil nil = nil :=
rfl

theorem ex2 (a b : α) (n : Nat) (va vb : Vec α n) : mapHead1 f (cons a va) (cons b vb) = cons (f a b) va :=
rfl
