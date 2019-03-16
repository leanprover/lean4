/- Benchmark for new code generator -/
inductive Expr
| Val : int → Expr
| Var : string → Expr
| Add : Expr → Expr → Expr
| Mul : Expr → Expr → Expr
| Pow : Expr → Expr → Expr
| Ln  : Expr → Expr

open Expr

def pown : int → int → int
| a 0 := 1
| a 1 := a
| a n :=
  let b := pown a (n / 2) in
  b * b * (if n % 2 = 0 then 1 else a)

def add : Expr → Expr → Expr
| (Val n)   (Val m)         := Val (n + m)
| (Val 0)   f               := f
| f         (Val 0)         := f
| f         (Val n)         := add (Val n) f
| (Val n)   (Add (Val m) f) := add (Val (n+m)) f
| f         (Add (Val n) g) := add (Val n) (add f g)
| (Add f g) h               := add f (add g h)
| f         g               := Add f g

def mul : Expr → Expr → Expr
| (Val n)   (Val m)         := Val (n*m)
| (Val 0)   _               := Val 0
| _         (Val 0)         := Val 0
| (Val 1)   f               := f
| f         (Val 1)         := f
| f         (Val n)         := mul (Val n) f
| (Val n)   (Mul (Val m) f) := mul (Val (n*m)) f
| f         (Mul (Val n) g) := mul (Val n) (mul f g)
| (Mul f g) h               := mul f (mul g h)
| f         g               := Mul f g

def pow : Expr → Expr → Expr
| (Val m) (Val n) := Val (pown m n)
| _       (Val 0) := Val 1
| f       (Val 1) := f
| (Val 0) _       := Val 0
| f       g       := Pow f g

def ln : Expr → Expr
| (Val 1) := Val 0
| f       := Ln f

def d (x : string) : Expr → Expr
| (Val _)   := Val 0
| (Var y)   := if x = y then Val 1 else Val 0
| (Add f g) := add (d f) (d g)
| (Mul f g) := add (mul f (d g)) (mul g (d f))
| (Pow f g) := mul (pow f g) (add (mul (mul g (d f)) (pow f (Val (-1)))) (mul (ln f) (d g)))
| (Ln f)    := mul (d f) (pow f (Val (-1)))

def count : Expr → nat
| (Val _) := 1
| (Var _) := 1
| (Add f g) := count f + count g
| (Mul f g) := count f + count g
| (Pow f g) := count f + count g
| (Ln f)    := count f

def Expr.to_string : Expr → string
| (Val n) := to_string n
| (Var x) := x
| (Add f g) := "(" ++ Expr.to_string f ++ " + " ++ Expr.to_string g ++ ")"
| (Mul f g) := "(" ++ Expr.to_string f ++ " * " ++ Expr.to_string g ++ ")"
| (Pow f g) := "(" ++ Expr.to_string f ++ " ^ " ++ Expr.to_string g ++ ")"
| (Ln f)    := "ln(" ++ Expr.to_string f ++ ")"

instance : has_to_string Expr :=
⟨Expr.to_string⟩

def nest_aux (s : nat) (f : nat → Expr → io Expr) : nat → Expr → io Expr
| 0       x := pure x
| m@(n+1) x := f (s - m) x >>= nest_aux n

def nest (f : nat → Expr → io Expr) (n : nat) (e : Expr) : io Expr :=
nest_aux n f n e

def deriv (i : nat) (f : Expr) : io Expr :=
do
  let d := d "x" f,
  io.println (to_string (i+1) ++ " count: " ++ (to_string $ count d)),
  pure d

def main (xs : list string) : io uint32 :=
do let x := Var "x",
   let f := pow x x,
   nest deriv 9 f,
   pure 0

-- set_option profiler true
-- #eval main []
