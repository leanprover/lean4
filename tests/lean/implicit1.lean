Import int.
Import real.
Variable f : Int -> Int -> Int
Show forall a, f a a > 0
Show forall a b, f a b > 0
Variable g : Int -> Real -> Int
Show forall a b, g a b > 0
Show forall a b, g a (f a b) > 0
SetOption pp::coercion true
Show forall a b, g a (f a b) > 0
Show fun a, a + 1
Show fun a b, a + b
Show fun (a b) (c : Int), a + c + b
(*
   The next example shows a limitation of the current elaborator.
   The current elaborator resolves overloads before solving the implicit argument constraints.
   So, it does not have enough information for deciding which overload to use.
*)
Show (fun a b, a + b) 10 20.
Variable x : Int
(* The following one works because the type of x is used to decide which + should be used *)
Show fun a b, a + x + b