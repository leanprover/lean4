open nat

eval [whnf] (fun x, x + 1) (2:nat)
eval (fun x, x + 1) (2:nat)

variable a : nat
eval [whnf] a + succ nat.zero
eval a + succ nat.zero
