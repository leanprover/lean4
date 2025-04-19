/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import Lean.Util.Paths
import Lean.DeclarationRange
import Lean.Elab.Command
import Lean.Linter.OtherLinter.Basic

/-!
# Linter frontend and commands

This file defines the linter commands which spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint in Pkg`: check all declarations in the package `Pkg`
  (so excluding core or other projects, and also excluding the current file)
* `#lint in all`: check all declarations in the environment
  (the current file and all imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint* in Std`) to omit the slow tests.

You can append a `-` to any command (e.g. `#lint- in Std`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint+ in Std`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments in Std`

You can add custom linters by defining a term of type `Linter` with the `@[std_linter]` attribute.
A linter defined with the name `Std.Tactic.Lint.myNewCheck` can be run with `#lint myNewCheck`
or `#lint only myNewCheck`.
If you add the attribute `@[std_linter disabled]` to `linter.myNewCheck` it will be registered,
but not run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/

namespace Std.Tactic.Lint
open Lean Std

/-- Verbosity for the linter output. -/
inductive LintVerbosity
  /-- `low`: only print failing checks, print nothing on success. -/
  | low
  /-- `medium`: only print failing checks, print confirmation on success. -/
  | medium
  /-- `high`: print output of every check. -/
  | high
  deriving Inhabited, DecidableEq, Repr

/-- `getChecks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `useOnly` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[std_linter]`.
If `slow` is false, it only uses the fast default tests. -/
def getChecks (slow : Bool) (useOnly : Bool) : CoreM (Array NamedLinter) := do
  let mut result := #[]
  unless useOnly do
    for (name, declName, dflt) in stdLinterExt.getState (← getEnv) do
      if dflt then
        let linter ← getLinter name declName
        if slow || linter.isFast then
          let _ := Inhabited.mk linter
          result := result.binInsert (·.name.lt ·.name) linter
  pure result

/--
Runs all the specified linters on all the specified declarations in parallel,
producing a list of results.
-/
def lintCore (decls : Array Name) (linters : Array NamedLinter) :
    CoreM (Array (NamedLinter × HashMap Name MessageData)) := do
  let env ← getEnv
  let options ← getOptions -- TODO: sanitize options?

  let tasks : Array (NamedLinter × Array (Name × Task (Option MessageData))) ←
    linters.mapM fun linter => do
      let decls ← decls.filterM (shouldBeLinted linter.name)
      (linter, ·) <$> decls.mapM fun decl => (decl, ·) <$> do
        BaseIO.asTask do
          match ← withCurrHeartbeats (linter.test decl)
              |>.run'.run' {options, fileName := "", fileMap := default} {env}
              |>.toBaseIO with
          | Except.ok msg? => pure msg?
          | Except.error err => pure m!"LINTER FAILED:\n{err.toMessageData}"

  tasks.mapM fun (linter, decls) => do
    let mut msgs : HashMap Name MessageData := {}
    for (declName, msg?) in decls do
      if let some msg := msg?.get then
        msgs := msgs.insert declName msg
    pure (linter, msgs)

/-- Sorts a map with declaration keys as names by line number. -/
def sortResults (results : HashMap Name α) : CoreM <| Array (Name × α) := do
  let mut key : HashMap Name Nat := {}
  for (n, _) in results.toArray do
    if let some range ← findDeclarationRanges? n then
      key := key.insert n <| range.range.pos.line
  pure $ results.toArray.qsort fun (a, _) (b, _) => key.findD a 0 < key.findD b 0

/-- Formats a linter warning as `#check` command with comment. -/
def printWarning (declName : Name) (warning : MessageData) (useErrorFormat : Bool := false)
  (filePath : System.FilePath := default) : CoreM MessageData := do
  if useErrorFormat then
    if let some range ← findDeclarationRanges? declName then
      return m!"{filePath}:{range.range.pos.line}:{range.range.pos.column + 1}: error: {
          ← mkConstWithLevelParams declName} {warning}"
  pure m!"#check {← mkConstWithLevelParams declName} /- {warning} -/"

/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
def printWarnings (results : HashMap Name MessageData) (filePath : System.FilePath := default)
    (useErrorFormat : Bool := false) : CoreM MessageData := do
  (MessageData.joinSep ·.toList Format.line) <$>
    (← sortResults results).mapM fun (declName, warning) =>
      printWarning declName warning (useErrorFormat := useErrorFormat) (filePath := filePath)

/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
def groupedByFilename (results : HashMap Name MessageData) (useErrorFormat : Bool := false) :
    CoreM MessageData := do
  let sp ← if useErrorFormat then initSrcSearchPath ["."] else pure {}
  let grouped : HashMap Name (System.FilePath × HashMap Name MessageData) ←
    results.foldM (init := {}) fun grouped declName msg => do
      let mod ← findModuleOf? declName
      let mod := mod.getD (← getEnv).mainModule
      grouped.insert mod <$>
        match grouped.find? mod with
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
    (results : Array (NamedLinter × HashMap Name MessageData))
    (decls : Array Name)
    (groupByFilename : Bool)
    (whereDesc : String) (runSlowLinters : Bool)
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
  unless runSlowLinters do s := m!"{s}-- (slow linters skipped)\n"
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
    if modules[env.const2ModIdx[declName].get! (α := Nat)]! then
      decls.push declName
    else decls

/-- The `in foo` config argument allows running the linter on a specified project. -/
syntax inProject := " in " ident

open Elab Command in
/-- The command `#lint` runs the linters on the current file (by default).

`#lint only someLinter` can be used to run only a single linter. -/
elab tk:"#lint" verbosity:("+" <|> "-")? fast:"*"? only:(&" only")?
    linters:(ppSpace ident)* project:(inProject)? : command => do
  let (decls, whereDesc, groupByFilename) ← match project with
    | none => do pure (← liftCoreM getDeclsInCurrModule, "in the current file", false)
    | some cfg => match cfg with
      | `(inProject| in $id) =>
        let id := id.getId.eraseMacroScopes
        if id == `all then
          pure (← liftCoreM getAllDecls, "in all files", true)
        else
          pure (← liftCoreM (getDeclsInPackage id), s!"in {id}", true)
      | _ => throwUnsupportedSyntax
  let verbosity : LintVerbosity ← match verbosity with
    | none => pure .medium
    | some ⟨.node _ `token.«+» _⟩ => pure .high
    | some ⟨.node _ `token.«-» _⟩ => pure .low
    | _ => throwUnsupportedSyntax
  let fast := fast.isSome
  let only := only.isSome
  let linters ← liftCoreM do
    let mut result ← getChecks (slow := !fast) only
    let linterState := stdLinterExt.getState (← getEnv)
    for id in linters do
      let name := id.getId.eraseMacroScopes
      let some (declName, _) := linterState.find? name | throwErrorAt id "not a linter: {name}"
      Elab.addConstInfo id declName
      let linter ← getLinter name declName
      result := result.binInsert (·.name.lt ·.name) linter
    pure result
  let results ← liftCoreM <| lintCore decls linters
  let failed := results.any (!·.2.isEmpty)
  let mut fmtResults ← liftCoreM <|
    formatLinterResults results decls (groupByFilename := groupByFilename)
      whereDesc (runSlowLinters := !fast) verbosity linters.size
  if failed then
    logError fmtResults
  else if verbosity != LintVerbosity.low then
    logInfoAt tk m!"{fmtResults}\n-- All linting checks passed!"

open Elab Command in
/-- The command `#list_linters` prints a list of all available linters. -/
elab "#list_linters" : command => do
  let mut result := #[]
  for (name, _, dflt) in stdLinterExt.getState (← getEnv) do
    result := result.binInsert (·.1.lt ·.1) (name, dflt)
  let mut msg := m!"Available linters (linters marked with (*) are in the default lint set):"
  for (name, dflt) in result do
    msg := msg ++ m!"\n{name}{if dflt then " (*)" else ""}"
  logInfo msg
