#check λ _, nat
#check λ (_ _ : nat), nat
#check λ _ _ : nat, nat
#check (λ _, 0 : nat → nat)

def f (_ : nat) : nat :=
0
