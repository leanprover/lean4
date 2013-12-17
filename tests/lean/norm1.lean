Variable N : Type
Variable P : N -> N -> N -> Bool
Variable a : N
Variable g : N -> N
Variable H : (N -> N -> N) -> N

Eval fun f : N -> N, (fun x y : N, g x) (f a)
Eval fun (a : N) (f : N -> N) (g : (N -> N) -> N -> N) (h : N -> N -> N),
     (fun (x : N) (y : N) (z : N), h x y) (g (fun x : N, f (f x)) (f a)) (f a)
Eval fun (a b : N) (g : Bool -> N), (fun x y : Bool, g x) (a == b)
Eval fun (a : Type) (b : a -> Type) (g : Type U -> Bool), (fun x y : Type U, g x) (Pi x : a, b x)
Eval fun f : N -> N, (fun x y z : N, g x) (f a)
Eval fun f g : N -> N, (fun x y z : N, g x) (f a)
Eval fun f : N -> N, (fun x : N, fun y : N, fun z : N, P x y z) (f a)
Eval fun (f : N -> N) (a : N), (fun x : N, fun y : N, fun z : N, P x y z) (f a)
Eval fun f g : N -> N, (fun x y1 z1 : N, H ((fun x y2 z2 : N, g x) x)) (f a)
Check fun f g : N -> N, (fun x y1 z1 : N, H ((fun x y2 z2 : N, g x) x)) (f a)
