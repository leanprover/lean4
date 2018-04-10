open nat
universe variables u

inductive rvec (α : Type u) : nat → Type u
| nil {} : rvec 0
| cons   : Π {n}, rvec n → α → rvec (succ n)

namespace rvec

local infix :: := cons
variables {α β δ : Type u}

def map (f : α → β) : Π {n : nat}, rvec α n → rvec β n
| 0        nil    := nil
| (succ n) (v::a) := map v :: f a

def map₂ (f : α → β → δ) : Π {n : nat}, rvec α n → rvec β n → rvec δ n
| 0        nil    nil    := nil
| (succ n) (v::a) (w::b) := map₂ v w :: f a b

lemma ex1 : map succ (nil::1::2) = nil::2::3 :=
rfl
end rvec
