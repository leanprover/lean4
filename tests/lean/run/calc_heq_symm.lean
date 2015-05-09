import logic

theorem tst {A B C D : Type} {a₁ a₂ : A} {b : B} {c : C} {d : D}
            (H₀ : a₁ = a₂) (H₁ : a₂ == b) (H₂ : b == c) (H₃ : c == d) : d == a₁ :=
calc d  == c  : H₃
    ... == b  : H₂
    ... == a₂ : H₁
    ... =  a₁ : H₀

reveal tst
print definition tst
