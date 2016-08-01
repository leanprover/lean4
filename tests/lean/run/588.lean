import standard
open function

variables {a b r : Type}

definition f a := Πr, (a -> r) -> r

definition g (fn : a -> b) (sa : f a) : f b := sorry

-- Remark: to support the next one we must restrict the context of the meta-variable in the body of the lambda
-- check λx, g id x = x

check λ(x : f a), g id x = x

universe variables l₁ l₂ l₃

check λ (x : f.{_ l₂} a), g.{_ _ l₂ l₂} id x = x

example (x : f a) : g id x = x :=
sorry
