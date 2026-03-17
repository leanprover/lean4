inductive Expr
| Val : Int → Expr
| Var : String → Expr
| Add : Expr → Expr → Expr
| Mul : Expr → Expr → Expr

namespace Expr

protected def Expr.toString : Expr → String
| Val n   => toString n
| Var x   => x
| Add f g   => "(" ++ Expr.toString f ++ " + " ++ Expr.toString g ++ ")"
| Mul f g   => "(" ++ Expr.toString f ++ " * " ++ Expr.toString g ++ ")"

instance : ToString Expr :=
⟨Expr.toString⟩

partial def addAux : Expr → Expr → Expr
| f,         Add (Val n) g   => addAux (Val n) (addAux f g)
| f,         g               => Add f g

def add (a b : Expr) : Expr :=
addAux a b

end Expr

open Expr

def main (xs : List String) : IO UInt32 :=
do let x := Var "x";
   IO.println (add (Val 1) (Add (Mul (Val 2) x) x));
   pure 0
