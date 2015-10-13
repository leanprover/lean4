import data.num
check (λ {A : Type.{1}} (a : A), a) (10:num)
check (λ {A} a, a) 10
check (λ a, a) (10:num)
