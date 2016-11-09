@[inline] def g (n : nat) : nat :=
nat.rec_on n 0 (λ m r, r + 2)

vm_eval g 10
