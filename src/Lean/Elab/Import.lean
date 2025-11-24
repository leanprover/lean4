/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Parser.Module
meta import Lean.Parser.Module
import Lean.Compiler.ModPkgExt

public section

public section

namespace Lean.Elab

abbrev HeaderSyntax := TSyntax ``Parser.Module.header

def HeaderSyntax.startPos (header : HeaderSyntax) : String.Pos.Raw :=
  header.raw.getPos?.getD 0

def HeaderSyntax.isModule (header : HeaderSyntax) : Bool :=
  !header.raw[0].isNone

def HeaderSyntax.imports (stx : HeaderSyntax) (includeInit : Bool := true) : Array Import :=
  match stx with
  | `(Parser.Module.header| $[module%$moduleTk]? $[prelude%$preludeTk]? $importsStx*) =>
    let imports := if preludeTk.isNone && includeInit then #[{ module := `Init : Import }] else #[]
    imports ++ importsStx.map fun
      | `(Parser.Module.import| $[public%$publicTk]? $[meta%$metaTk]? import $[all%$allTk]? $n) =>
        { module := n.getId, importAll := allTk.isSome
          isExported := publicTk.isSome || moduleTk.isNone
          isMeta := metaTk.isSome }
      | _ => unreachable!
  | _ => unreachable!

def HeaderSyntax.toModuleHeader (stx : HeaderSyntax) : ModuleHeader where
  isModule := stx.isModule
  imports := stx.imports

abbrev headerToImports := @HeaderSyntax.imports

def processHeaderCore
    (startPos : String.Pos.Raw) (imports : Array Import) (isModule : Bool)
    (opts : Options) (messages : MessageLog) (inputCtx : Parser.InputContext)
    (trustLevel : UInt32 := 0) (plugins : Array System.FilePath := #[]) (leakEnv := false)
    (mainModule := Name.anonymous) (package? : Option PkgId := none)
    (arts : NameMap ImportArtifacts := {})
    : IO (Environment × MessageLog) := do
  let level := if isModule then
    if Elab.inServer.get opts then
      .server
    else
      .exported
  else
    .private
  let (env, messages) ← try
    let env ←
      importModules (leakEnv := leakEnv) (loadExts := true) (level := level)
        imports opts trustLevel plugins arts
    pure (env, messages)
  catch e =>
    let env ← mkEmptyEnvironment
    let pos := inputCtx.fileMap.toPosition startPos
    pure (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos := pos })
  let env := env.setMainModule mainModule |>.setModulePackage package?
  return (env, messages)

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
