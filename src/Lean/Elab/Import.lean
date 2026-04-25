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
public import Lean.DeprecatedModule
import Init.Data.String.Modify

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
    let imports := if preludeTk.isNone && includeInit then
        #[{ module := `Init : Import }, { module := `Init, isMeta := true : Import }]
      else #[]
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

/--
Check imported modules for deprecation and emit warnings.

The `-- deprecated_module: ignore` comment can be placed on the `module` keyword to suppress
all warnings, or on individual `import` statements to suppress specific ones.
This follows the same pattern as `-- shake: keep` in Lake shake.

The `headerStx?` parameter carries the header syntax used for checking trailing comments.
When called from the Language Server, the main header syntax may have its trailing trivia
stripped by `unsetTrailing` for caching purposes, so `origHeaderStx?` can supply the original
(untrimmed) syntax to preserve `-- deprecated_module: ignore` annotations on the last import.
-/
def checkDeprecatedImports
    (env : Environment) (imports : Array Import) (opts : Options)
    (inputCtx : Parser.InputContext) (startPos : String.Pos.Raw) (messages : MessageLog)
    (headerStx? : Option HeaderSyntax := none)
    (origHeaderStx? : Option HeaderSyntax := none)
    : MessageLog := Id.run do
  let mut opts := opts
  let mut ignoreDeprecatedImports : NameSet := {}
  if let some headerStx := origHeaderStx? <|> headerStx? then
    match headerStx with
    | `(Parser.Module.header| $[module%$moduleTk]? $[prelude%$_]? $importsStx*) =>
      if moduleTk.any (·.getTrailing?.any (·.toString.contains "deprecated_module: ignore")) then
        opts := linter.deprecated.module.set opts false
      for impStx in importsStx do
        if impStx.raw.getTrailing?.any (·.toString.contains "deprecated_module: ignore") then
          match impStx with
          | `(Parser.Module.import| $[public%$_]? $[meta%$_]? import $[all%$_]? $n) =>
            ignoreDeprecatedImports := ignoreDeprecatedImports.insert n.getId
          | _ => pure ()
    | _ => pure ()
  if !linter.deprecated.module.get opts then
    return messages
  imports.foldl (init := messages) fun messages imp =>
    if ignoreDeprecatedImports.contains imp.module then
      messages
    else
    match env.getModuleIdx? imp.module with
    | some idx =>
      match env.getDeprecatedModuleByIdx? idx with
      | some entry =>
        let pos := inputCtx.fileMap.toPosition startPos
        messages.add {
          fileName := inputCtx.fileName
          pos := pos
          severity := .warning
          data := .tagged ``deprecatedModuleExt <| formatDeprecatedModuleWarning env idx imp.module entry
        }
      | none => messages
    | none => messages

private def osForbiddenChars : Array Char :=
  #['<', '>', '"', '|', '?', '*', '!']

private def osForbiddenNames : Array String :=
  #["CON", "PRN", "AUX", "NUL",
    "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8", "COM9",
    "COM¹", "COM²", "COM³",
    "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9",
    "LPT¹", "LPT²", "LPT³"]

private def checkComponentPortability (comp : String) : Option String :=
  if osForbiddenNames.contains comp.toUpper then
    some s!"'{comp}' is a reserved file name on some operating systems"
  else if let some c := osForbiddenChars.find? (comp.contains ·) then
    some s!"contains character '{c}' which is forbidden on some operating systems"
  else
    none

def checkModuleNamePortability
    (mainModule : Name) (inputCtx : Parser.InputContext) (startPos : String.Pos.Raw)
    (messages : MessageLog) : MessageLog :=
  go mainModule messages
where
  go : Name → MessageLog → MessageLog
    | .anonymous, messages => messages
    | .str parent s, messages =>
      let messages := match checkComponentPortability s with
        | some reason => messages.add {
            fileName := inputCtx.fileName
            pos := inputCtx.fileMap.toPosition startPos
            severity := .error
            data := s!"module name '{mainModule}' is not portable: {reason}"
          }
        | none => messages
      go parent messages
    | .num parent _, messages => go parent messages

def processHeaderCore
    (startPos : String.Pos.Raw) (imports : Array Import) (isModule : Bool)
    (opts : Options) (messages : MessageLog) (inputCtx : Parser.InputContext)
    (trustLevel : UInt32 := 0) (plugins : Array System.FilePath := #[]) (leakEnv := false)
    (mainModule := Name.anonymous) (package? : Option PkgId := none)
    (arts : NameMap ImportArtifacts := {})
    (headerStx? : Option HeaderSyntax := none)
    (origHeaderStx? : Option HeaderSyntax := none)
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
  let messages := checkDeprecatedImports env imports opts inputCtx startPos messages headerStx? origHeaderStx?
  let messages := checkModuleNamePortability mainModule inputCtx startPos messages
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
    (headerStx? := header)

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
