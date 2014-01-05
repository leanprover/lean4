variable f : Pi A : Type, A -> A -> A
variable N : Type
variable g : N -> N -> Bool
variable a : N
check g true (f _ a a)
