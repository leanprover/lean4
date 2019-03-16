import init.lean.expr
open lean

def main : io uint32 :=
let e := expr.app (expr.const `f []) (expr.const `a []) in
io.println e.dbg_to_string *>
io.println ("hash: " ++ to_string e.hash) *>
pure 0
