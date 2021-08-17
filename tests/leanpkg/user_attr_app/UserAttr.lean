import UserAttr.Tst

open Lean

def tst : MetaM Unit := do
  let env ← getEnv
  assert! (blaAttr.hasTag env `f)
  assert! (blaAttr.hasTag env `g)
  assert! !(blaAttr.hasTag env `id)
  pure ()

#eval tst

def declareLeanPath : MetaM Unit := do
  addAndCompile <| Declaration.defnDecl {
    name  := `leanPath
    type  := mkConst ``String
    value := toExpr <| System.SearchPath.separator.toString.intercalate ((← Lean.getBuiltinSearchPath).map toString)
    levelParams := []
    hints := ReducibilityHints.abbrev
    safety := DefinitionSafety.safe
  }

#eval declareLeanPath

#eval leanPath

unsafe def main : IO Unit := do
  initSearchPath s!"{leanPath}{System.SearchPath.separator}build"
  withImportModules [{ module := `UserAttr.Tst : Import }] {} 0 fun env => ()
