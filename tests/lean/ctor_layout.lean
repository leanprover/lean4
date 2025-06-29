import Lean.Compiler.IR

open Lean
open Lean.IR

def test : CoreM Unit := do
   let ctorLayout ← getCtorLayout ``Lean.IR.Expr.reuse;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   IO.println "---";
   let ctorLayout ← getCtorLayout ``Lean.EnvironmentHeader.mk;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   IO.println "---";
   let ctorLayout ← getCtorLayout ``Subtype.mk;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   pure ()

#eval test
