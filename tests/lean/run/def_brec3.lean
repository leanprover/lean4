open nat

inductive bv : nat → Type
| nil  : bv 0
| cons : ∀ (n) (hd : bool) (tl : bv n), bv (succ n)

open bv

variable (f : bool → bool → bool)

definition map2 : ∀ {n}, bv n → bv n → bv n
| .(0)     nil            nil             := nil
| .(n+1) (cons n b1 v1) (cons .(n) b2 v2) := cons n (f b1 b2) (map2 v1 v2)

example : map2 f nil nil = nil :=
rfl

example (n : nat) (b1 b2 : bool) (v1 v2 : bv n) : map2 f (cons n b1 v1) (cons n b2 v2) = cons n (f b1 b2) (map2 f v1 v2) :=
rfl
#print map2
