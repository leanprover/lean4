inductive vec (A : Type) : nat → Type
| nil {} : vec nat.zero
| cons   : ∀ {n}, A → vec n → vec (nat.succ n)

open vec

definition boo (n : nat) (v : vec bool n) : vec bool n :=
match n, v : ∀ (n : _), vec bool n → _ with
| 0,   nil      := nil
| n+1, cons a v := cons (bnot a) v
end
