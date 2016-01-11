import data.nat
open nat

constant tuple.{l} : Type.{l} → nat → Type.{l}
constant nil {A : Type} : tuple A 0

constant append {A : Type} {n m : nat} : tuple A n → tuple A m → tuple A (n + m)
infix ` ++ ` := append
axiom append_assoc {A : Type} {n₁ n₂ n₃ : nat} (v₁ : tuple A n₁) (v₂ : tuple A n₂) (v₃ : tuple A n₃) :
  (v₁ ++ v₂) ++ v₃ == v₁ ++ (v₂ ++ v₃)
attribute append_assoc [simp]

variables {A : Type}
variables {p m n q : nat}
variables {xs : tuple A m}
variables {ys : tuple A n}
variables {zs : tuple A p}
variables {ws : tuple A q}

example : p = m + n  → zs == xs ++ ys →  zs ++ ws == xs ++ (ys ++ ws) :=
by inst_simp

example : p = n + m  → zs == xs ++ ys →  zs ++ ws == xs ++ (ys ++ ws) :=
by inst_simp
