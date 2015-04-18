exit
import data.finset algebra.function algebra.binary
open nat list finset function binary

variable {A : Type}

-- TODO define for group
definition bigsum (s : finset A) (f : A → nat) : nat :=
acc (compose_right nat.add f) (right_commutative_compose_right nat.add f nat.add.right_comm) 0 s

definition bigprod (s : finset A) (f : A → nat) : nat :=
acc (compose_right nat.mul f) (right_commutative_compose_right nat.mul f nat.mul.right_comm) 1 s

definition bigand (s : finset A) (p : A → Prop) : Prop :=
acc (compose_right and p) (right_commutative_compose_right and p (λ a b c, propext (and.right_comm a b c))) true s

definition bigor (s : finset A) (p : A → Prop) : Prop :=
acc (compose_right or p) (right_commutative_compose_right or p (λ a b c, propext (or.right_comm a b c))) false s


example : to_finset [1, 3, 1] = to_finset [3, 3, 3, 1] :=
dec_trivial

example : to_finset [1, 2] ∪ to_finset [1, 3] = to_finset [3, 2, 1] :=
dec_trivial

example : 1 ∈ to_finset [3, 2, 1] :=
dec_trivial

example : bigsum (to_finset [3, 2, 2]) (λ x, x*x) = 13 :=
rfl

example : bigprod (to_finset [1, 2]) (λ x, x+1) = 6 :=
rfl
