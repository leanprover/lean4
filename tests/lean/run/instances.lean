import Lean

open Lean
open Lean.Meta

instance : ToFormat InstanceEntry where
  format e := format e.val

unsafe def tst1 : IO Unit :=
withImportModules [{module := `Lean}] {} 0 fun env => do
   let aux : MetaM Unit := do
     let insts ← getGlobalInstancesIndex
     IO.println (format insts)
   discard <| aux.run |>.toIO {} { env := env }

#eval tst1
