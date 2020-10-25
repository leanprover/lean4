import Lean

open Lean

partial def mkBig : Nat → Expr
| 0     => mkConst `a
| (n+1) => mkApp2 (mkConst `f []) (mkBig n) (mkBig n)

def replaceTest (e : Expr) : Expr :=
e.replace $ fun e => match e with
 | Expr.const c _ _ => if c == `f then mkConst `g else none
 | _ => none

#eval replaceTest $ mkBig 4

#eval (replaceTest $ mkBig 128).getAppFn

def findTest (e : Expr) : Option Expr :=
e.find? $ fun e => match e with
  | Expr.const c _ _ => c == `g
  | _ => false

#eval findTest $ mkBig 4
#eval findTest $ replaceTest $ mkBig 4
#eval findTest $ mkBig 128
#eval findTest $ (replaceTest $ mkBig 128)
