import Lean

open Lean

partial def mkBig : Nat → Expr
| 0     => mkConst `a
| (n+1) => mkApp2 (mkConst `f []) (mkBig n) (mkBig n)

def replaceTest (e : Expr) : Expr :=
e.replace $ fun e => match e with
 | Expr.const c _ => if c == `f then mkConst `g else none
 | _ => none

#eval replaceTest $ mkBig 4

/-- info: Lean.Expr.const `g [] -/
#guard_msgs in
#eval (replaceTest $ mkBig 128).getAppFn

def findTest (e : Expr) : Option Expr :=
e.find? $ fun e => match e with
  | Expr.const c _ => c == `g
  | _ => false

/-- info: none -/
#guard_msgs in
#eval findTest $ mkBig 4

/-- info: some (Lean.Expr.const `g []) -/
#guard_msgs in
#eval findTest $ replaceTest $ mkBig 4

/-- info: none -/
#guard_msgs in
#eval findTest $ mkBig 128

/-- info: some (Lean.Expr.const `g []) -/
#guard_msgs in
#eval findTest $ (replaceTest $ mkBig 128)
