import init.lean.compiler.ir
open Lean.IR

def tst1 : IO Unit :=
let fbody : FnBody :=
   FnBody.vdecl `x IRType.uint32 (Expr.lit (LitVal.num 0)) $
   FnBody.ret `x;
IO.println $ format fbody

def main : IO Unit :=
tst1
