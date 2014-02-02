import Int.
definition revapp {A : (Type U)} {B : A -> (Type U)} (a : A) (f : forall (x : A), B x) : (B a) := f a.
infixl 100 |> : revapp

check 10 |> (fun x, x + 1)
         |> (fun x, x + 2)
         |> (fun x, 2 * x)
         |> (fun x, 3 - x)
         |> (fun x, x + 2)

definition revcomp {A B C: (Type U)} (f : A -> B) (g : B -> C) : A -> C :=
        fun x, g (f x)
infixl 100 #> : revcomp

check (fun x, x + 1)     #>
      (fun x, 2 * x * x) #>
      (fun x, 10 + x)

definition simple := (fun x, x + 1)     #>
                     (fun x, 2 * x * x) #>
                     (fun x, 10 + x)

check simple

definition simple2 := (fun x : Int, x + 1) #>
                      (fun x, 2 * x * x)   #>
                      (fun x, 10 + x)
check simple2
