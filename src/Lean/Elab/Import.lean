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

abbrev HeaderSyntax := TSyntax ``Parser.Module.header

def HeaderSyntax.startPos (header : HeaderSyntax) : String.Pos :=
  header.raw.getPos?.getD 0

def HeaderSyntax.isModule (header : HeaderSyntax) : Bool :=
  !header.raw[0].isNone

def HeaderSyntax.imports (stx : HeaderSyntax) (includeInit : Bool := true) : Array Import :=
  match stx with
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude%$preludeTk]? $importsStx*) =>
    let imports := if preludeTk.isNone && includeInit then #[{ module := `Init : Import }] else #[]
    imports ++ importsStx.map fun
      | `(Parser.Module.import| $[private%$privateTk]? $[meta%$metaTk]? import $[all%$allTk]? $n) =>
        { module := n.getId, importAll := allTk.isSome, isExported := privateTk.isNone
          isMeta := metaTk.isSome }
      | _ => unreachable!
  | _ => unreachable!

abbrev headerToImports := @HeaderSyntax.imports

def processHeaderCore
    (startPos : String.Pos) (imports : Array Import) (isModule : Bool)
    (opts : Options) (messages : MessageLog) (inputCtx : Parser.InputContext)
    (trustLevel : UInt32 := 0) (plugins : Array System.FilePath := #[]) (leakEnv := false)
    (mainModule := Name.anonymous) (arts : NameMap ModuleArtifacts := {})
    : IO (Environment × MessageLog) := do
  let level := if isModule then
    if Elab.inServer.get opts then
      .server
    else
      .exported
  else
    .private
  let (env, messages) ← try
    for i in imports do
      if !isModule && i.importAll then
        throw <| .userError "cannot use `import all` without `module`"
      if i.importAll && mainModule.getRoot != i.module.getRoot then
        throw <| .userError "cannot use `import all` across module path roots"
      if !isModule && !i.isExported then
        throw <| .userError "cannot use `private import` without `module`"
    let env ←
      importModules (leakEnv := leakEnv) (loadExts := true) (level := level)
        imports opts trustLevel plugins arts
    pure (env, messages)
  catch e =>
    let env ← mkEmptyEnvironment
    let pos := inputCtx.fileMap.toPosition startPos
    pure (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos := pos })
  return (env.setMainModule mainModule, messages)

/--
Elaborates the given header syntax into an environment.

If `mainModule` is not given, `Environment.setMainModule` should be called manually. This is a
backwards compatibility measure not compatible with the module system.
-/
@[inline] def processHeader
    (header : HeaderSyntax)
    (opts : Options) (messages : MessageLog) (inputCtx : Parser.InputContext)
    (trustLevel : UInt32 := 0) (plugins : Array System.FilePath := #[]) (leakEnv := false)
    (mainModule := Name.anonymous)
    : IO (Environment × MessageLog) := do
  processHeaderCore header.startPos header.imports header.isModule
    opts messages inputCtx trustLevel plugins leakEnv mainModule

def parseImports (input : String) (fileName : Option String := none) : IO (Array Import × Position × MessageLog) := do
  let fileName := fileName.getD "<input>"
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  pure (headerToImports header, inputCtx.fileMap.toPosition parserState.pos, messages)

def printImports (input : String) (fileName : Option String) : IO Unit := do
  let (deps, _, _) ← parseImports input fileName
  for dep in deps do
    let fname ← findOLean dep.module
    IO.println fname

def printImportSrcs (input : String) (fileName : Option String) : IO Unit := do
  let sp ← getSrcSearchPath
  let (deps, _, _) ← parseImports input fileName
  for dep in deps do
    let fname ← findLean sp dep.module
    IO.println fname

end Lean.Elab
