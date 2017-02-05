universe variables u

inductive Vec (α : Type u) : nat → Type u
| nil {} : Vec 0
| cons   : Π {n}, α → Vec n → Vec (nat.succ n)


def head {α} : Π {n}, Vec α (n+1) → α
| n (Vec.cons h t) := h

check @head.equations._eqn_1
