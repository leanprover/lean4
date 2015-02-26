import logic data.sigma
open sigma
inductive list (T : Type) : Type := nil {} : list T | cons   : T → list T → list T open list notation h :: t  := cons h t notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l
check ∃ (A : Type₁) (x y : A), x = y
check ∃ (x : num), x = 0
check Σ (x : num), x = 10
check Σ (A : Type₁), list A
