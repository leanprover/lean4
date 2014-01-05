import Int
check fun (A : Type) (a : A),
          let b := a
          in b

variable g : Pi A : Type, A -> A

definition f (A: Type) (a : A) : A :=
   let b := g A a,
       c := g A b
   in c

print f _ 10.
print f _ (- 10).
