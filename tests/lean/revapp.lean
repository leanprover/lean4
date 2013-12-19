Definition revapp {A : (Type U)} {B : A -> (Type U)} (a : A) (f : Pi (x : A), B x) : (B a) := f a.
Infixl 100 |> : revapp

Eval 10 |> (fun x, x + 1)
        |> (fun x, x + 2)
        |> (fun x, 2 * x)
        |> (fun x, 3 - x)
        |> (fun x, x + 2)

Definition revcomp {A B C: (Type U)} (f : A -> B) (g : B -> C) : A -> C :=
        fun x, g (f x)
Infixl 100 #> : revcomp

Eval (fun x, x + 1)     #>
     (fun x, 2 * x * x) #>
     (fun x, 10 + x)

Definition simple := (fun x, x + 1)     #>
                     (fun x, 2 * x * x) #>
                     (fun x, 10 + x)

Check simple
Eval simple 10

Definition simple2 := (fun x : Int, x + 1) #>
                      (fun x, 2 * x * x)   #>
                      (fun x, 10 + x)
Check simple2
Eval simple2 (-10)
