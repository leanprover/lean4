
definition plus (a b : nat) : nat :=
nat.rec_on a b (λ a' ih, nat.succ ih)

#eval plus 3 5
