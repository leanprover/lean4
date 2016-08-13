set_option new_elaborator true

definition plus (a b : nat) : nat :=
nat.rec_on a b (λ a' ih, nat.succ ih)

vm_eval plus 3 5
