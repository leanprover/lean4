/- Benchmark for new code generator -/
import Init.System.IO


inductive Expr
| Val : Int → Expr
| Var : String → Expr
| Add : Expr → Expr → Expr
| Mul : Expr → Expr → Expr
| Pow : Expr → Expr → Expr
| Ln  : Expr → Expr

namespace Expr

unsafe def pown : Int → Int → Int
| a, 0 => 1
| a, 1 => a
| a, n =>
  let b := pown a (n / 2);
  b * b * (if n % 2 = 0 then 1 else a)

unsafe def add : Expr → Expr → Expr
| Val n,     Val m           => Val (n + m)
| Val 0,     f               => f
| f,         Val 0           => f
| f,         Val n           => add (Val n) f
| Val n,     Add (Val m) f   => add (Val (n+m)) f
| f,         Add (Val n) g   => add (Val n) (add f g)
| Add f g,   h               => add f (add g h)
| f,         g               => Add f g

unsafe def mul : Expr → Expr → Expr
| Val n,     Val m           => Val (n*m)
| Val 0,     _               => Val 0
| _,         Val 0           => Val 0
| Val 1,     f               => f
| f,         Val 1           => f
| f,         Val n           => mul (Val n) f
| Val n,     Mul (Val m) f   => mul (Val (n*m)) f
| f,         Mul (Val n) g   => mul (Val n) (mul f g)
| Mul f g,   h               => mul f (mul g h)
| f,         g               => Mul f g

unsafe def pow : Expr → Expr → Expr
| Val m,   Val n   => Val (pown m n)
| _,       Val 0   => Val 1
| f,       Val 1   => f
| Val 0,   _       => Val 0
| f,       g       => Pow f g

def ln : Expr → Expr
| Val 1   => Val 0
| f       => Ln f

unsafe def d (x : String) : Expr → Expr
| Val _     => Val 0
| Var y     => if x = y then Val 1 else Val 0
| Add f g   => add (d x f) (d x g)
| Mul f g   => add (mul f (d x g)) (mul g (d x f))
| Pow f g   => mul (pow f g) (add (mul (mul g (d x f)) (pow f (Val (0 - 1)))) (mul (ln f) (d x g)))
| Ln f      => mul (d x f) (pow f (Val (0 - 1)))

partial def count : Expr → Nat
| Val _   => 1
| Var _   => 1
| Add f g   => count f + count g
| Mul f g   => count f + count g
| Pow f g   => count f + count g
| Ln f      => count f

partial def Expr.toString : Expr → String
| Val n   => ToString.toString n
| Var x   => x
| Add f g   => "(" ++ toString f ++ " + " ++ toString g ++ ")"
| Mul f g   => "(" ++ toString f ++ " * " ++ toString g ++ ")"
| Pow f g   => "(" ++ toString f ++ " ^ " ++ toString g ++ ")"
| Ln f      => "ln(" ++ toString f ++ ")"

instance : ToString Expr :=
⟨Expr.toString⟩

unsafe def nest (f : Expr → IO Expr) : Nat → Expr → IO Expr
| 0,     x => pure x
| n+1,   x => f x >>= nest f n

unsafe def deriv (f : Expr) : IO Expr :=
do
  let d := d "x" f;
  IO.print "count: ";
  IO.println (count f);
  pure d

end Expr

unsafe def main : IO Unit :=
do let x := Expr.Var "x";
   let f := Expr.pow x x;
   discard $ Expr.nest Expr.deriv 9 f;
   pure ()
