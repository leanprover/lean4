check (λ {A : Type.{1}} (a : A), a) (10:num)
set_option trace.app_builder true
check (λ {A} (a : A), a) 10
check (λ a, a) (10:num)
