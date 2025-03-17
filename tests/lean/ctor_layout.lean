import Lean.Compiler.IR

open Lean
open Lean.IR

unsafe def main : IO Unit :=
withImportModules #[{module := `Lean.Compiler.IR.Basic}] {} 0 fun env => do
   let ctorLayout ← IO.ofExcept $ getCtorLayout env `Lean.IR.Expr.reuse;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   IO.println "---";
   let ctorLayout ← IO.ofExcept $ getCtorLayout env `Lean.EnvironmentHeader.mk;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   IO.println "---";
   let ctorLayout ← IO.ofExcept $ getCtorLayout env `Subtype.mk;
   ctorLayout.fieldInfo.forM $ fun finfo => IO.println (format finfo);
   pure ()

#eval main
