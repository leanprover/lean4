variable N : Type
variable P : N -> N -> N -> Bool
variable a : N
variable g : N -> N
variable H : (N -> N -> N) -> N

eval fun f : N -> N, (fun x y : N, g x) (f a)
eval fun (a : N) (f : N -> N) (g : (N -> N) -> N -> N) (h : N -> N -> N),
     (fun (x : N) (y : N) (z : N), h x y) (g (fun x : N, f (f x)) (f a)) (f a)
eval fun (a b : N) (g : Bool -> N), (fun x y : Bool, g x) (a == b)
eval fun (a : Type) (b : a -> Type) (g : (Type U) -> Bool), (fun x y : (Type U), g x) (Pi x : a, b x)
eval fun f : N -> N, (fun x y z : N, g x) (f a)
eval fun f g : N -> N, (fun x y z : N, g x) (f a)
eval fun f : N -> N, (fun x : N, fun y : N, fun z : N, P x y z) (f a)
eval fun (f : N -> N) (a : N), (fun x : N, fun y : N, fun z : N, P x y z) (f a)
eval fun f g : N -> N, (fun x y1 z1 : N, H ((fun x y2 z2 : N, g x) x)) (f a)
check fun f g : N -> N, (fun x y1 z1 : N, H ((fun x y2 z2 : N, g x) x)) (f a)
