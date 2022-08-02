/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Module
import Lean.Data.Json

namespace Lean.Elab

def headerToImports (header : Syntax) : List Import :=
  let imports := if header[0].isNone then [{ module := `Init : Import }] else []
  imports ++ header[1].getArgs.toList.map fun stx =>
    -- `stx` is of the form `(Module.import "import" "runtime"? id)
    let runtime := !stx[1].isNone
    let id      := stx[2].getId
    { module := id, runtimeOnly := runtime }

def processHeader (header : Syntax) (opts : Options) (messages : MessageLog) (inputCtx : Parser.InputContext) (trustLevel : UInt32 := 0)
    : IO (Environment × MessageLog) := do
  try
    let env ← importModules (headerToImports header) opts trustLevel
    pure (env, messages)
  catch e =>
    let env ← mkEmptyEnvironment
    let spos := header.getPos?.getD 0
    let pos  := inputCtx.fileMap.toPosition spos
    pure (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos := pos })

def parseImports (input : String) (fileName : Option String := none) : IO (List Import × Position × MessageLog) := do
  let fileName := fileName.getD "<input>"
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  pure (headerToImports header, inputCtx.fileMap.toPosition parserState.pos, messages)

@[export lean_print_imports]
def printImports (input : String) (fileName : Option String) : IO Unit := do
  let (deps, _, _) ← parseImports input fileName
  for dep in deps do
    let fname ← findOLean dep.module
    IO.println fname

deriving instance ToJson for Import

structure PrintImportResult where
  imports? : Option (Array Import) := none
  errors   : Array String := #[]
  deriving ToJson

structure PrintImportsResult where
  imports : Array PrintImportResult
  deriving ToJson

@[export lean_print_imports_json]
def printImportsJson (fileNames : Array String) : IO Unit := do
  let rs ← fileNames.mapM fun fn => do
    try
      let (deps, _, msgs) ← parseImports (← IO.FS.readFile ⟨fn⟩) fn
      if msgs.hasErrors then
        return { errors := (← msgs.toList.toArray.mapM (·.toString)) }
      else
        return { imports? := some deps.toArray }
    catch e => return { errors := #[e.toString] }
  IO.println (toJson { imports := rs : PrintImportsResult })

end Lean.Elab
