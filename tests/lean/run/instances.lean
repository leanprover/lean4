import Lean

open Lean
open Lean.Meta

instance : ToFormat InstanceEntry where
  format e := format e.val

unsafe def tst1 : IO Unit := do
  let env ← importModules (loadExts := true) #[{module := `Lean}] {}
  let aux : MetaM Unit := do
    let insts ← getGlobalInstancesIndex
    assert! insts.size > 0
    IO.println (format insts)
  discard <| aux.run |>.toIO { fileName := "", fileMap := default } { env := env }

#eval tst1
