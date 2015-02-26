import data.nat.basic
open nat

inductive fin : nat → Type :=
| fz : Π {n : nat},         fin (succ n)
| fs : Π {n : nat}, fin n → fin (succ n)

namespace fin

  inductive le : ∀ {n : nat}, fin n → fin n → Prop :=
  | lez : ∀ {n : nat} (j : fin (succ n)),     le fz j
  | les : ∀ {n : nat} {i j : fin n}, le i j → le (fs i) (fs j)

end fin
