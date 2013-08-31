Check fun (A : Type) (a : A),
          let b := a
          in b

Variable g : Pi A : Type, A -> A

Definition f (A: Type) (a : A) : A :=
   let b := g A a,
       c := g A b
   in c
