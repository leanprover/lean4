theorem tst {A B C D : Type} {a₁ a₂ : A} {b : B} {c : C} {d : D}
            (H₀ : a₁ = a₂) (H₁ : a₂ == b) (H₂ : b == c) (H₃ : c == d) : d == a₁ :=
calc d  == c  : heq.symm H₃
    ... == b  : heq.symm H₂
    ... == a₂ : heq.symm H₁
    ... =  a₁ : eq.symm H₀

print definition tst
