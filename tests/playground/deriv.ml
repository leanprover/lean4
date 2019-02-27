type expr =
| Val of int
| Var of string
| Add of expr * expr
| Mul of expr * expr
| Pow of expr * expr
| Ln of expr;;

let rec pown a n =
if n == 0 then 1
else if n == 1 then a
else let b = pown a (n / 2) in
b * b * (if n mod 2 == 0 then 1 else a);;

let rec add n m =
match (n, m) with
| (Val n, Val m) -> Val (n+m)
| (Val 0, f)     -> f
| (f, Val 0)     -> f
| (f, Val n)     -> add (Val n) f
| (Val n, Add(Val m, f)) -> add (Val (n+m)) f
| (f, Add(Val n, g))     -> add (Val n) (add f g)
| (Add(f, g), h)         -> add f (add g h)
| (f, g)                 -> Add (f, g);;

let rec mul n m =
match (n, m) with
| (Val n, Val m) -> Val (n*m)
| (Val 0, _)     -> Val 0
| (_, Val 0)     -> Val 0
| (Val 1, f)     -> f
| (f, Val 1)     -> f
| (f, Val n)     -> mul (Val n) f
| (Val n, Mul (Val m, f)) -> mul (Val (n*m)) f
| (f, Mul (Val n, g))     -> mul (Val n) (mul f g)
| (Mul (f, g), h)         -> mul f (mul g h)
| (f, g)                  -> Mul (f, g);;

let rec pow m n =
match (m, n) with
| (Val m, Val n) -> Val (pown m n)
| (_,  Val 0)    -> Val 1
| (f, Val 1)     -> f
| (Val 0, _)     -> Val 0
| (f, g)         -> Pow (f, g);;

let rec ln n =
match n with
| (Val 1) -> Val 0
| f       -> Ln f;;

let rec d x f =
match f with
| Val _      -> Val 0
| Var y      -> if x = y then Val 1 else Val 0
| Add (f, g) -> add (d x f) (d x g)
| Mul (f, g) -> add (mul f (d x g)) (mul g (d x f))
| Pow (f, g) -> mul (pow f g) (add (mul (mul g (d x f)) (pow f (Val (-1)))) (mul (ln f) (d x g)))
| Ln f       -> mul (d x f) (pow f (Val (-1)));;

let rec count f =
match f with
| Val _ -> 1
| Var _ -> 1
| Add (f, g) -> count f + count g
| Mul (f, g) -> count f + count g
| Pow (f, g) -> count f + count g
| Ln f       -> count f;;

let rec nest_aux s f n x =
if n == 0 then x
else let x = f (s - n) x in
     nest_aux s f (n - 1) x;;

let nest f n e =
nest_aux n f n e;;

let deriv i f =
  let d = d "x" f in
  Printf.printf "%8d count: %8d\n" (i+1) (count d);
  d;;

let x = Var "x" in
let f = pow x x in
nest deriv 10 f;;
