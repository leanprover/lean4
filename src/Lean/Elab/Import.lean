/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Module
import Lean.Util.Paths
import Lean.CoreM

namespace Lean.Elab

def headerToImports : TSyntax ``Parser.Module.header → Array Import
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude%$preludeTk]? $importsStx*) =>
    let imports := if preludeTk.isNone then #[{ module := `Init : Import }] else #[]
    imports ++ importsStx.map fun
      | `(Parser.Module.import| import $[private%$privateTk]? $n) =>
        { module := n.getId, importPrivate := privateTk.isSome }
      | _ => unreachable!
  | _ => unreachable!

def processHeader (header : TSyntax ``Parser.Module.header) (opts : Options) (messages : MessageLog)
    (inputCtx : Parser.InputContext) (trustLevel : UInt32 := 0)
    (plugins : Array System.FilePath := #[]) (leakEnv := false)
    : IO (Environment × MessageLog) := do
  let isModule := !header.raw[0].isNone
  let level := if isModule then
    if Elab.inServer.get opts then
      .server
    else
      .exported
  else
    .private
  try
    let env ←
      importModules (leakEnv := leakEnv) (loadExts := true) (level := level) (headerToImports header) opts trustLevel plugins
    pure (env, messages)
  catch e =>
    let env ← mkEmptyEnvironment
    let spos := header.raw.getPos?.getD 0
    let pos  := inputCtx.fileMap.toPosition spos
    pure (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos := pos })

def parseImports (input : String) (fileName : Option String := none) : IO (Array Import × Position × MessageLog) := do
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

@[export lean_print_import_srcs]
def printImportSrcs (input : String) (fileName : Option String) : IO Unit := do
  let sp ← getSrcSearchPath
  let (deps, _, _) ← parseImports input fileName
  for dep in deps do
    let fname ← findLean sp dep.module
    IO.println fname

end Lean.Elab
