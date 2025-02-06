inductive Expr where
  | app (f : String) (args : Array Expr)

def Expr.size (e : Expr) : Nat := Id.run do
  match e with
  | app f args =>
    let mut sz := 1
    for h : i in [: args.size] do
      sz := sz + size args[i]
    return sz

namespace Ex2
inductive Expr where
  | app (f : String) (args : List Expr)

def Expr.size (e : Expr) : Nat := Id.run do
  match e with
  | app f args =>
    let mut sz := 1
    for h : arg in args do
      sz := sz + size arg
    return sz

end Ex2
