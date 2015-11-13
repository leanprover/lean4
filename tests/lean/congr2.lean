import data.list

#congr @add
#congr @perm

section
variables p : nat → Prop
variables q : nat → nat → Prop
variables f : Π (x y : nat), p x → q x y → nat

#congr f
end

constant p : Π {A : Type}, A → Prop
constant q : Π {A : Type} (n m : A), p n → p m → Prop
constant r : Π {A : Type} (n m : A) (H₁ : p n) (H₂ : p m), q n m H₁ H₂ → Prop
constant h : Π (A : Type) (n m : A)
               (H₁ : p n) (H₂ : p m) (H₃ : q n n H₁ H₁) (H₄ : q n m H₁ H₂)
               (H₅ : r n m H₁ H₂ H₄) (H₆ : r n n H₁ H₁ H₃), A

#congr h

#congr @ite
