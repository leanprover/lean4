open nat

eval [whnf] (fun x, x + 1) 2
eval (fun x, x + 1) 2

variable a : nat
eval [whnf] a + succ zero
eval a + succ zero
