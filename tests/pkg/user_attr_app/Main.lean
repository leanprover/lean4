import UserAttr.Tst

open Lean

def tst : MetaM Unit := do
  let env ← getEnv
  assert! (blaAttr.hasTag env `f)
  assert! (blaAttr.hasTag env `g)
  assert! !(blaAttr.hasTag env `id)
  pure ()

#eval tst

unsafe def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) [".lake/build/lib"]
  withImportModules #[{ module := `UserAttr.Tst : Import }] {} 0 fun env => pure ()
