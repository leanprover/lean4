import data.nat
open nat

theorem add_assoc (m n k : nat) : m + n + k = m + (n + k) :=
nat.induction_on k
(show m + n + 0 = m + (n + 0), from rfl),
(take k,
   assume IH : m + n + k = m + (n + k),
   show m + n + mysucc k = m + (n + mysucc k), from
     calc
       m + n + mysucc k = mysucc (m + n + k) : rfl
       ... = mysucc (m + (n + k)) : IH
       ... = m + mysucc (n + k) : rfl
       ... = m + (n + mysucc k) : rfl)
