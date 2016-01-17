set_option blast.strategy "cc"

example (C : nat → Type) (f : Π n, C n → C n) (n m : nat) (c : C n) (d : C m) :
        f n == f m → c == d → f n c == f m d :=
by blast
