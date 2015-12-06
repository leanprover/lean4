import data.list
set_option blast.strategy "cc"
open perm list

definition tst₁
        (A : Type) (l₁ l₂ l₃ l₄ l₅ : list A) :
        (l₁ ~ l₂) → (l₃ ~ l₄) → (l₁ ++ l₃ ++ l₅ ++ l₄ ++ l₁) ~ (l₂ ++ l₄ ++ l₅ ++ l₃ ++ l₂) :=
by blast

print tst₁

definition tst₂
        (A : Type) (l₁ l₂ l₃ l₄ l₅ : list A) :
        (l₁ ~ l₂) → (l₃ = l₄) → (l₁ ++ l₃ ++ l₅ ++ l₄ ++ l₁) ~ (l₂ ++ l₄ ++ l₅ ++ l₃ ++ l₂) :=
by blast
