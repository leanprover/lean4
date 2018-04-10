open nat

inductive bv : nat → Type
| nil  : bv 0
| cons : ∀ (n) (hd : bool) (tl : bv n), bv (succ n)

open bv bool

definition h : ∀ {n}, bv (succ (succ n)) → bool
| .(succ m) (cons (succ (succ m)) b v) := b
| .(0)      (cons (succ nat.zero) b v) := bnot b

example (m : nat) (b : bool) (v : bv (succ (succ m))) : @h (succ m) (cons (succ (succ m)) b v) = b :=
rfl

example (m : nat) (b : bool) (v : bv 1) : @h 0 (cons 1 b v) = bnot b :=
rfl
