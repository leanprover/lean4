import Lean
new_frontend
open Lean
open Lean.Meta

unsafe def tst1 : IO Unit :=
withImportModules [{module := `Lean}] {} 0 fun env => do
   let insts := env.getGlobalInstances;
   IO.println (format insts)

#eval tst1
