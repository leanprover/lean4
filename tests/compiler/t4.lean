/- Benchmark for new code generator -/
inductive Expr
| Val : Int → Expr
| Var : String → Expr
| Add : Expr → Expr → Expr
| Mul : Expr → Expr → Expr
| Pow : Expr → Expr → Expr
| Ln  : Expr → Expr

namespace Expr

protected def Expr.toString : Expr → String
| Val n   => toString n
| Var x   => x
| Add f g   => "(" ++ Expr.toString f ++ " + " ++ Expr.toString g ++ ")"
| Mul f g   => "(" ++ Expr.toString f ++ " * " ++ Expr.toString g ++ ")"
| Pow f g   => "(" ++ Expr.toString f ++ " ^ " ++ Expr.toString g ++ ")"
| Ln f      => "ln(" ++ Expr.toString f ++ ")"

instance : ToString Expr :=
⟨Expr.toString⟩

partial def pown : Int → Int → Int
| a, 0 => 1
| a, 1 => a
| a, n =>
  let b := pown a (n / 2);
  b * b * (if n % 2 = 0 then 1 else a)

partial def addAux : Expr → Expr → Expr
| Val n,     Val m           => Val (n + m)
| Val 0,     f               => f
| f,         Val 0           => f
| f,         Val n           => addAux (Val n) f
| Val n,     Add (Val m) f   => addAux (Val (n+m)) f
| f,         Add (Val n) g   => addAux (Val n) (addAux f g)
| Add f g,   h               => addAux f (addAux g h)
| f,         g               => Add f g

def add (a b : Expr) : Expr :=
-- dbgTrace (">> add (" ++ toString a ++ ", " ++ toString b ++ ")") $ fun _ =>
addAux a b

-- set_option trace.compiler.borrowed_inference true

partial def mulAux : Expr → Expr → Expr
| Val n,     Val m           => Val (n*m)
| Val 0,     _               => Val 0
| _,         Val 0           => Val 0
| Val 1,     f               => f
| f,         Val 1           => f
| f,         Val n           => mulAux (Val n) f
| Val n,     Mul (Val m) f   => mulAux (Val (n*m)) f
| f,         Mul (Val n) g   => mulAux (Val n) (mulAux f g)
| Mul f g,   h               => mulAux f (mulAux g h)
| f,         g               => Mul f g

def mul (a b : Expr) : Expr :=
-- dbgTrace (">> mul (" ++ toString a ++ ", " ++ toString b ++ ")") $ fun _ =>
mulAux a b

def pow : Expr → Expr → Expr
| Val m,   Val n   => Val (pown m n)
| _,       Val 0   => Val 1
| f,       Val 1   => f
| Val 0,   _       => Val 0
| f,       g       => Pow f g

def ln : Expr → Expr
| Val 1   => Val 0
| f       => Ln f

def d (x : String) : Expr → Expr
| Val _     => Val 0
| Var y     => if x = y then Val 1 else Val 0
| Add f g   => add (d x f) (d x g)
| Mul f g   =>
  -- dbgTrace (">> d (" ++ toString f ++ ", " ++ toString g ++ ")") $ fun _ =>
  add (mul f (d x g)) (mul g (d x f))
| Pow f g   => mul (pow f g) (add (mul (mul g (d x f)) (pow f (Val (-1)))) (mul (ln f) (d x g)))
| Ln f      => mul (d x f) (pow f (Val (-1)))

def count : Expr → Nat
| Val _   => 1
| Var _   => 1
| Add f g   => count f + count g
| Mul f g   => count f + count g
| Pow f g   => count f + count g
| Ln f      => count f


def nestAux (s : Nat) (f : Nat → Expr → IO Expr) : Nat → Expr → IO Expr
| 0,       x => pure x
| m@(n+1), x => f (s - m) x >>= nestAux s f n

def nest (f : Nat → Expr → IO Expr) (n : Nat) (e : Expr) : IO Expr :=
nestAux n f n e

def deriv (i : Nat) (f : Expr) : IO Expr :=
do
  let d := d "x" f;
  IO.println (toString (i+1) ++ " count: " ++ (toString $ count d));
  IO.println (toString d);
  pure d

end Expr

def main (xs : List String) : IO UInt32 :=
do let x := Expr.Var "x";
   let f := Expr.add x (Expr.mul x (Expr.mul x (Expr.add x x)));
   IO.println f;
   discard <| Expr.nest Expr.deriv 3 f;
   pure 0

-- setOption profiler True
-- #eval main []
