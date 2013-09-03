Set pp::colors false
Variable f : Pi A : Type, A -> A -> A
Variable N : Type
Variable g : N -> N -> Bool
Variable a : N
Check g true (f _ a a)
