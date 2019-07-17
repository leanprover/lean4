import init.lean.expr
open Lean

def main : IO UInt32 :=
let e := Expr.app (Expr.const `f []) (Expr.const `a []);
IO.println e.dbgToString *>
IO.println ("hash: " ++ toString e.hash) *>
pure 0
