import Lean.Compiler.IR

open Lean
open Lean.IR

def test : CoreM Unit := do
   let ctorLayout ← Compiler.LCNF.getCtorLayout ``Lean.IR.Expr.reuse;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   IO.println "---";
   let ctorLayout ← Compiler.LCNF.getCtorLayout ``Subtype.mk;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   pure ()

#eval test
