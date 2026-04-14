/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

prelude
public import Lean.Linter.EnvLinter.Basic
import Lean.DeclarationRange
import Lean.Util.Path
import Lean.CoreM
import Lean.Elab.Command

public section

open Lean Meta

namespace Lean.Linter.EnvLinter

/-- Verbosity for the linter output. -/
inductive LintVerbosity
  /-- `low`: only print failing checks, print nothing on success. -/
  | low
  /-- `medium`: only print failing checks, print confirmation on success. -/
  | medium
  /-- `high`: print output of every check. -/
  | high
  deriving Inhabited, DecidableEq, Repr

/-- `getChecks clippy runOnly` produces a list of linters.
`runOnly` is an optional list of names that should resolve to declarations with type
`NamedEnvLinter`. If populated, only these linters are run (regardless of the default
configuration). Otherwise, it uses all enabled linters in the environment tagged with
`@[builtin_env_linter]`. If `clippy` is false, it only uses linters with `isDefault = true`. -/
def getChecks (clippy : Bool) (runOnly : Option (List Name)) :
    CoreM (Array NamedEnvLinter) := do
  let mut result := #[]
  for (name, declName, isDefault) in envLinterExt.getState (← getEnv) do
    let shouldRun := match runOnly with
      | some only => only.contains name
      | none => clippy || isDefault
    if shouldRun then
      let linter ← getEnvLinter name declName
      result := result.binInsert (·.name.lt ·.name) linter
  pure result


/--
Runs all the specified linters on all the specified declarations in parallel,
producing a list of results.
-/
def lintCore (decls : Array Name) (linters : Array NamedEnvLinter) :
    CoreM (Array (NamedEnvLinter × Std.HashMap Name MessageData)) := do
  let tasks : Array (NamedEnvLinter × Array (Name × Task (Except Exception <| Option MessageData))) ←
    linters.mapM fun linter => do
      let decls ← decls.filterM (shouldBeLinted linter.name)
      (linter, ·) <$> decls.mapM fun decl => (decl, ·) <$> do
        let act : MetaM (Option MessageData) := do
          linter.test decl
        EIO.asTask <| (← Core.wrapAsync (fun _ =>
          act |>.run' Elab.Command.mkMetaContext
        ) (cancelTk? := none)) ()

  let result ← tasks.mapM fun (linter, decls) => do
    let mut msgs : Std.HashMap Name MessageData := {}
    for (declName, msgTask) in decls do
      let msg? ← match msgTask.get with
      | Except.ok msg? => pure msg?
      | Except.error err => pure m!"LINTER FAILED:\n{err.toMessageData}"
      if let .some msg := msg? then
        msgs := msgs.insert declName msg
    pure (linter, msgs)
  return result

/-- Sorts a map with declaration keys as names by line number. -/
def sortResults (results : Std.HashMap Name α) : CoreM <| Array (Name × α) := do
  let mut key : Std.HashMap Name Nat := {}
  for (n, _) in results.toArray do
    if let some range ← findDeclarationRanges? n then
      key := key.insert n <| range.range.pos.line
  pure $ results.toArray.qsort fun (a, _) (b, _) => key.getD a 0 < key.getD b 0

/-- Formats a linter warning as `#check` command with comment. -/
def printWarning (declName : Name) (warning : MessageData) (useErrorFormat : Bool := false)
  (filePath : System.FilePath := default) : CoreM MessageData := do
  if useErrorFormat then
    if let some range ← findDeclarationRanges? declName then
      let msg ← addMessageContextPartial
        m!"{filePath}:{range.range.pos.line}:{range.range.pos.column + 1}: error: {
          ← mkConstWithLevelParams declName} {warning}"
      return msg
  addMessageContextPartial m!"#check {← mkConstWithLevelParams declName} /- {warning} -/"

/-- Formats a map of linter warnings using `printWarning`, sorted by line number. -/
def printWarnings (results : Std.HashMap Name MessageData) (filePath : System.FilePath := default)
    (useErrorFormat : Bool := false) : CoreM MessageData := do
  (MessageData.joinSep ·.toList Format.line) <$>
    (← sortResults results).mapM fun (declName, warning) =>
      printWarning declName warning (useErrorFormat := useErrorFormat) (filePath := filePath)

/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
-/
def groupedByFilename (results : Std.HashMap Name MessageData) (useErrorFormat : Bool := false) :
    CoreM MessageData := do
  let sp ← if useErrorFormat then getSrcSearchPath else pure {}
  let grouped : Std.HashMap Name (System.FilePath × Std.HashMap Name MessageData) ←
    results.foldM (init := {}) fun grouped declName msg => do
      let mod ← findModuleOf? declName
      let mod := mod.getD (← getEnv).mainModule
      grouped.insert mod <$>
        match grouped[mod]? with
        | some (fp, msgs) => pure (fp, msgs.insert declName msg)
        | none => do
          let fp ← if useErrorFormat then
            pure <| (← sp.findWithExt "lean" mod).getD (modToFilePath "." mod "lean")
          else pure default
          pure (fp, .insert {} declName msg)
  let grouped' := grouped.toArray.qsort fun (a, _) (b, _) => toString a < toString b
  (MessageData.joinSep · (Format.line ++ Format.line)) <$>
    grouped'.toList.mapM fun (mod, fp, msgs) => do
      pure m!"-- {mod}\n{← printWarnings msgs (filePath := fp) (useErrorFormat := useErrorFormat)}"

/--
Formats the linter results as Lean code with comments and `#check` commands.
-/
def formatLinterResults
    (results : Array (NamedEnvLinter × Std.HashMap Name MessageData))
    (decls : Array Name)
    (groupByFilename : Bool)
    (whereDesc : String) (runClippyLinters : Bool)
    (verbose : LintVerbosity) (numLinters : Nat) (useErrorFormat : Bool := false) :
    CoreM MessageData := do
  let formattedResults ← results.filterMapM fun (linter, results) => do
    if !results.isEmpty then
      let warnings ←
        if groupByFilename || useErrorFormat then
          groupedByFilename results (useErrorFormat := useErrorFormat)
        else
          printWarnings results
      pure $ some m!"/- The `{linter.name}` linter reports:\n{linter.errorsFound} -/\n{warnings}\n"
    else if verbose = LintVerbosity.high then
      pure $ some m!"/- OK: {linter.noErrorsFound} -/"
    else
      pure none
  let mut s := MessageData.joinSep formattedResults.toList Format.line
  let numAutoDecls := (← decls.filterM isAutoDecl).size
  let failed := results.map (·.2.size) |>.foldl (·+·) 0
  unless verbose matches LintVerbosity.low do
    s := m!"-- Found {failed} error{if failed == 1 then "" else "s"
      } in {decls.size - numAutoDecls} declarations (plus {
      numAutoDecls} automatically generated ones) {whereDesc
      } with {numLinters} linters\n\n{s}"
  unless runClippyLinters do s := m!"{s}-- (non-clippy linters skipped)\n"
  pure s

/-- Get the list of declarations in the current module. -/
def getDeclsInCurrModule : CoreM (Array Name) := do
  pure $ (← getEnv).constants.map₂.foldl (init := #[]) fun r k _ => r.push k

/-- Get the list of all declarations in the environment. -/
def getAllDecls : CoreM (Array Name) := do
  pure $ (← getEnv).constants.map₁.fold (init := ← getDeclsInCurrModule) fun r k _ => r.push k

/-- Get the list of all declarations in the specified package. -/
def getDeclsInPackage (pkg : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut decls ← getDeclsInCurrModule
  let modules := env.header.moduleNames.map (pkg.isPrefixOf ·)
  return env.constants.map₁.fold (init := decls) fun decls declName _ =>
    if modules[env.const2ModIdx[declName]?.get!]! then
      decls.push declName
    else decls

end Lean.Linter.EnvLinter
