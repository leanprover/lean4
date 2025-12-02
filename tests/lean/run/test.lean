module

prelude
public import Init.System.IO

noncomputable def findWithExt : IO Unit := do
  let _ ← ([] : List System.FilePath).findM? fun p => p.isDir
  return
