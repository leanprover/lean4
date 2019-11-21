import Init.Lean.Compiler.IR
open Lean
open Lean.IR

def tst : IO Unit :=
do initSearchPath "Init=../../library/Init";
   env ← importModules [{module := `Init.Lean.Compiler.IR.Basic}];
   ctorLayout ← IO.ofExcept $ getCtorLayout env `Lean.IR.Expr.reuse;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   IO.println "---";
   ctorLayout ← IO.ofExcept $ getCtorLayout env `Lean.EnvironmentHeader.mk;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   IO.println "---";
   ctorLayout ← IO.ofExcept $ getCtorLayout env `Subtype.mk;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   pure ()

#eval tst
