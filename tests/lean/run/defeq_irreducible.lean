constants (A : Type) (a : A)
definition f (a : A) : A := a

definition f.def [defeq] (a : A) : f a = a := rfl
attribute f [irreducible]

#defeq_simplify f a

-- example : f a = a := by blast
