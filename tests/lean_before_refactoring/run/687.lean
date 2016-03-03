import data.fin

section rot
open nat fin eq.ops algebra
open eq.ops

definition rotr₀ {n : nat} : fin n → fin n :=
match n with
| 0        := take i, elim0 i
| (succ k) := madd (-maxi)
end

definition rotr₁ {n : nat} : fin n → fin n :=
match n with
| zero     := take i, elim0 i
| (succ k) := madd (-maxi)
end

definition rotr₂ : ∀ {n : nat}, fin n → fin n
| 0        i := elim0 i
| (succ n) i := madd (has_neg.neg maxi) i

definition rotr₃ : ∀ {n : nat}, fin n → fin n
| 0        := take i, elim0 i
| (succ n) := madd (-maxi)

definition rotr₄ : ∀ {n : nat}, fin n → fin n
| 0        i := elim0 i
| (succ n) i := madd (-maxi) i

end rot
