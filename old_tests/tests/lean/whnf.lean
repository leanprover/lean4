open nat

#reduce [whnf] (fun x, x + 1) (2:nat)
#reduce (fun x, x + 1) (2:nat)

variable a : nat
#reduce [whnf] a + succ nat.zero
#reduce a + succ nat.zero
