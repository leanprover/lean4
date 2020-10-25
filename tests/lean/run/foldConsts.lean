import Lean

open Lean

partial def mkTerm : Nat → Expr
| 0   => mkApp (mkConst `a) (mkConst `b)
| n+1 => mkApp (mkTerm n) (mkTerm n)

def collectConsts (e : Expr) : List Name :=
e.foldConsts [] List.cons

def tst1 : IO Unit :=
IO.println $ collectConsts (mkTerm 1000)

#eval tst1
