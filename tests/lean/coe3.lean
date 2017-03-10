constants A B₁ B₂ C D : Type

constant A_to_B₁ : has_coe A B₁
constant A_to_B₂ : has_coe A B₂
constant B₁_to_C : has_coe B₁ C
constant B₂_to_D : has_coe B₂ D

attribute [instance] A_to_B₁ A_to_B₂ B₁_to_C B₂_to_D

constant a : A
constant f : C → C
constant g : D → D

#check f a

#check g a
