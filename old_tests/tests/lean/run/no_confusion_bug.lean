open nat

inductive Fin : nat → Type
| fz : Π {n : nat},         Fin (succ n)
| fs : Π {n : nat}, Fin n → Fin (succ n)

namespace Fin

  inductive le : ∀ {n : nat}, Fin n → Fin n → Prop
  | lez : ∀ {n : nat} (j : Fin (succ n)),     le fz j
  | les : ∀ {n : nat} {i j : Fin n}, le i j → le (fs i) (fs j)

end Fin
