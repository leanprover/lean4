set_option new_elaborator true

definition f : nat → nat → nat
| a .a := a

definition f : ∀ (a b c : nat), a = c → c = a
| a b .b rfl := rfl

inductive vec (A : Type) : nat → Type
| nil {}  : vec 0
| cons : Π {n}, A → vec n → vec (n+1)

definition foo (A : Type) (f : A → A → A) : Π {n}, vec A n → vec A n → vec A n
| _  vec.nil          vec.nil          := vec.nil
| _ (vec.cons a₁ l₁) (vec.cons a₂ l₂) := vec.cons (f a₁ a₂) (foo l₁ l₂)
