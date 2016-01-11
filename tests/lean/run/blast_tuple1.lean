import data.nat
open nat

constant tuple.{l} : Type.{l} → nat → Type.{l}
constant nil {A : Type} : tuple A 0
constant cons {A : Type} {n : nat} : A → tuple A n → tuple A (succ n)
constant append {A : Type} {n m : nat} : tuple A n → tuple A m → tuple A (n + m)
infix ` ++ ` := append
axiom append_nil {A : Type} {n : nat} (v : tuple A n) : v ++ nil = v
axiom nil_append {A : Type} {n : nat} (v : tuple A n) : nil ++ v == v
axiom append_assoc {A : Type} {n₁ n₂ n₃ : nat} (v₁ : tuple A n₁) (v₂ : tuple A n₂) (v₃ : tuple A n₃) : (v₁ ++ v₂) ++ v₃ == v₁ ++ (v₂ ++ v₃)
attribute append_nil nil_append append_assoc [simp]

example (A : Type) (n m : nat) (v₁ v₂ : tuple A n) (w₁ w₂ : tuple A m) :
        v₁ ++ nil ++ (v₂ ++ w₁) ++ (nil ++ w₂) == v₁ ++ v₂ ++ w₁ ++ w₂ :=
by inst_simp
