/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.EnvLinter
public import Lean.Linter.PersistentLintLog
import Lean.CoreM
import Lean.DocString.Extension
import Lean.Elab.DocString.Builtin.Postponed
import Lake.Config.Workspace
import Lean.Linter.CodeQuality

open Lean Lean.Core Meta Linter

namespace Lake.BuiltinLint

public inductive Mode where
  /-- Report linter findings and exit nonzero if any were found. -/
  | report
  /-- Record linter warnings as `set_option <linter> false in` exceptions by editing the
  source files in place. -/
  | recordExceptions
  /--
  Record linter warnings as code quality checks and run the registered code quality checks
  -/
  | codeQuality
  deriving BEq

/-- Arguments for builtin linting via `lake lint --builtin-lint`. -/
public structure Args where
  /-- Explicit linter-option overrides, applied to the build of each module.

  Each entry sets a `Lean.Option Bool` to the given value. Later entries override earlier
  ones at the same name. Populated from `--linters=linter.X,-linter.Y,...` on the CLI. -/
  linterOverrides : Array (Name × Bool) := #[]
  /-- The list of root modules to lint. -/
  mods : Array Name := #[]
  /-- Whether to only run the user provided linters -/
  lintOnly : Bool := false
  /-- Whether to record linter warnings as `set_option <linter> false in` exceptions
  by editing the source files in place. -/
  mode : Mode := .report
  /-- Source search path used to resolve modules to their `.lean` files when recording
  exceptions for environment linters. Populated from the workspace's `LEAN_SRC_PATH`, since
  `getSrcSearchPath` alone does not cover package sources during a `lake lint` run. -/
  srcSearchPath : SearchPath := {}

/--
Turns the `lake lint` extra arguments into an array of `Lean.Option`, that needs to be enabled
for the rebuild of the package, in order to turn on the appropriate linters.
-/
public def leanOptOverrides (args : Args) : LeanOptions :=
  let merged : NameMap Bool := args.linterOverrides.foldl (init := {}) fun m (n, b) => m.insert n b
  let base : Array LeanOption :=
    merged.toArray.map fun (n, b) => ⟨`weak ++ n, .ofBool b⟩
  let base :=
    if args.mode == .recordExceptions then
      base.push ⟨`internal.cmdlineSnapshots, .ofBool false⟩
    else
      base
  LeanOptions.ofArray base

/-- A linter warning to be recorded as a source exception.

Recording it inserts `set_option option false in` immediately before the declaration beginning
at `pos` in `file`, silencing the `option` linter for that declaration. -/
private structure ExceptionRecord where
  /-- Source file containing the flagged declaration. -/
  file : System.FilePath
  /-- Start position of the flagged declaration (1-based line, 0-based column). -/
  pos : Position
  /-- The linter option to disable, e.g. `linter.foo`. -/
  option : Name
  deriving Inhabited

/-- The result of linting according to its mode. -/
private inductive LintingOutcome where
  /-- Reporting mode: failures were printed to stderr, and `failed` determines the exit code. -/
  | reported (failed : Bool)
  /--
  Recording mode: `records` are the exceptions to write, and `unlocated` indicates that there were
  failures whose position could not be resolved.
  -/
  | recorded (records : Array ExceptionRecord) (unlocated : Bool)
  /-- Code-quality mode: `entries` are the aggregated code quality entries to emit as JSON. -/
  | codeQualityChecks (entries : Array CodeQuality.Entry)

/-- The result of the deferred docstring check for one lint target, according to its mode. -/
private inductive DeferredCheckOutcome where
  /-- Reporting mode: failures were printed to stderr, and `failed` determines the exit code. -/
  | reported (failed : Bool)
  /--
  Recording mode: `records` are the exceptions to write, and `unlocated` indicates that there were
  failures whose position could not be resolved.
  -/
  | recorded (records : Array ExceptionRecord) (unlocated : Bool)

private def collectTextLints
    (env : Environment) (pkgRoot : Name) :
    Array (Name × Array Linter.LintEntry) :=
  Linter.getAllLints env |>.foldl (init := #[]) fun acc (mod, entries) =>
    if pkgRoot.isPrefixOf mod && !entries.isEmpty then acc.push (mod, entries) else acc

@[noinline] private def getIsModule (modData : Lean.ModuleData) : BaseIO Bool :=
  return modData.isModule

private def recordedMarker : String := "-- recorded by `lake lint --record-exceptions`"

private def isIndentChar (c : Char) : Bool := c == ' ' || c == '\t'

private def leadingWhitespace (line : String) : String :=
  (line.toRawSubstring.takeWhile isIndentChar).toString

/--
Applies the collected exceptions to the source files: for each file, inserts a
`set_option <linter> false in <marker>` line before every flagged declaration.
-/
private def recordExceptionsToFiles (records : Array ExceptionRecord) : IO Unit := do
  let mut byFile : Std.HashMap String (System.FilePath × Array (Nat × Name)) := {}
  for r in records do
    let key := r.file.toString
    let (fp, arr) := byFile.getD key (r.file, #[])
    byFile := byFile.insert key (fp, arr.push (r.pos.line, r.option))
  for (_, file, lineOpts) in byFile.toArray do
    -- Deduplicate options per line.
    let mut perLine : Std.HashMap Nat (Array Name) := {}
    for (ln, opt) in lineOpts do
      let cur := perLine.getD ln #[]
      unless cur.contains opt do
        perLine := perLine.insert ln (cur.push opt)
    let some content ← (some <$> IO.FS.readFile file) <|> pure none
      | IO.eprintln s!"warning: could not read `{file}`; skipping its {lineOpts.size} exception(s)"
    let mut lines := (content.split '\n').toArray.map toString
    -- Process target lines back-to-front so insertions do not invalidate earlier line numbers.
    let targets := perLine.toArray.qsort (fun a b => a.1 > b.1)
    let mut fileInserted := 0
    for (ln, opts) in targets do
      let idx := ln - 1
      if h : idx < lines.size then
        let indent := leadingWhitespace lines[idx]
        let opts := opts.qsort (fun a b => toString a < toString b)
        let newLines := opts.map fun o => s!"{indent}set_option {o} false in {recordedMarker}"
        lines := lines.extract 0 idx ++ newLines ++ lines.extract idx lines.size
        fileInserted := fileInserted + newLines.size
    if fileInserted > 0 then
      IO.println s!"recording {fileInserted} exception{if fileInserted == 1 then "" else "s"} in {file}"
      IO.FS.writeFile file ("\n".intercalate lines.toList)

/--
The source position used to insert an exception for a Verso docstring with a failed check. `failMod`
is the module that recorded the deferred check.

Requires an environment imported at the `server` olean level, which carries the declaration ranges
and Verso module-doc snippets consulted here.
-/
private def deferredSitePos? (failMod : Name) (site : Doc.DeferredCheckSite) :
    CoreM (Option Position) := do
  match site with
  | .decl n =>
    return (← findDeclarationRanges? n).map (·.range.pos)
  | .moduleDoc i =>
    let some snippets := getVersoModuleDoc? (← getEnv) failMod | return none
    return snippets[i]?.map (·.declarationRange.pos)

/-- A deferred check site, described for error messages. -/
private def describeSite : Doc.DeferredCheckSite → String
  | .decl n => s!"the docstring of `{n}`"
  | .moduleDoc i => s!"module docstring #{i + 1}"

/-- The result of the deferred docstring check pass for one lint target. -/
private structure DeferredCheckResults where
  /-- The mode-specific outcome of the pass. -/
  outcome : DeferredCheckOutcome
  /-- Modules whose deferred checks have now been run. -/
  checkedModules : NameSet

/--
Runs deferred docstring checks (e.g. forward references) over the modules of the package rooted at
`pkgRoot` that are imported by `env`. These deferred checks may be found both in module docstrings
and in declaration docstrings, so a declaration-centric interface doesn't make sense. Because
deferred checks capture their local option values, the per-check predicate can honor a `set_option
linter.doc.deferred` by inspecting the captured values. The package-level toggle is read from the
command-line overrides: `--lint-only` requires explicit selection, otherwise the option defaults on
but honors an explicit `--linters=-linter.doc.deferred` (or `-linter.all`).

`docCheckedModules` names the package modules whose checks earlier lint targets already ran; a
module imported by several targets is thus checked only once. Its modules are skipped here, and the
result's `checkedModules` extends it with the ones this target covered, to thread into the next
target.

Failures are reported on stderr, unless `args.recordExceptions` is set, in which case they are
turned into exception records at the flagged docstring's positions for the caller to write.
-/
private def runDeferredChecks (args : Args) (linterOpts : Linter.LinterOptions) (sp : SearchPath)
    (env : Environment) (pkgRoot : Name) (docCheckedModules : NameSet) :
    IO DeferredCheckResults := do
  let selected :=
    if args.lintOnly then
      Lean.Linter.isLinterEnabledByOptions linter.doc.deferred.name linterOpts
    else
      Lean.Linter.getLinterValue linter.doc.deferred linterOpts
  unless selected do
    let outcome := if args.mode == .recordExceptions then .recorded #[] false else .reported false
    return { outcome, checkedModules := docCheckedModules }
  let (outcome, _) ←
      CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
    let failures ← Lean.Doc.DeferredCheck.run
      (fun m => pkgRoot.isPrefixOf m && !docCheckedModules.contains m)
      (shouldCheck := fun c =>
        return Linter.getLinterValue linter.doc.deferred (← c.options.toLinterOptions))
    if args.mode == .recordExceptions then
      let mut recs : Array ExceptionRecord := #[]
      let mut unlocated := false
      for (failMod, c, _) in failures do
        match ← deferredSitePos? failMod c.site with
        | some pos =>
          match ← sp.findWithExt "lean" failMod with
          | some file =>
            recs := recs.push { file, pos, option := linter.doc.deferred.name }
          | none =>
            IO.eprintln s!"\
              warning: could not locate source file for `{failMod}` \
              to record a `{linter.doc.deferred.name}` exception"
            unlocated := true
        | none =>
          IO.eprintln s!"\
            warning: could not determine the position of {describeSite c.site} in `{failMod}`; \
            cannot record a `{linter.doc.deferred.name}` exception"
          unlocated := true
      return DeferredCheckOutcome.recorded recs unlocated
    else
      for (failMod, c, msg) in failures do
        let context := if c.sourceString.isEmpty then "" else s!" ({c.sourceString})"
        match ← sp.findWithExt "lean" failMod with
        | some file =>
          IO.eprintln s!"{file}: error: in {describeSite c.site}{context}: {← msg.toString}"
        | none =>
          IO.eprintln s!"error: in module `{failMod}`, in {describeSite c.site}{context}: {← msg.toString}"
      return DeferredCheckOutcome.reported !failures.isEmpty
  -- Mark this target's transitive imports that are in the package so later targets don't re-run
  -- their checks.
  let mut checkedModules := docCheckedModules
  for m in env.header.moduleNames do
    if pkgRoot.isPrefixOf m then
      checkedModules := checkedModules.insert m
  return { outcome, checkedModules }

/--
Reports the text-linter warnings recorded for the modules of the package rooted at `mod.getRoot`
that are imported by `env`. Text linters run during elaboration, so this does not re-run them:
their warnings were persisted into `lintLogExt` when each module was built (with the linter
overrides applied via `leanOptOverrides`) and are recovered here from the `.olean`s, which requires
an environment imported at the `server` olean level. With `--lint-only`,
the recorded entries are additionally filtered to the explicitly enabled linters.

In `report` mode the warnings are printed to stdout. In `recordExceptions` mode, each entry
carrying a command position is turned into an exception record for the caller to write; entries
without one are reported on stderr and flagged as unlocated. In `codeQuality` mode, the warnings
are aggregated per module/linter pair into code quality entries whose scalar value is the number
of warnings, for the caller to emit as JSON.
-/
private def runTextLinters (args : Args) (linterOpts : Linter.LinterOptions)
    (env : Environment) (mod : Name) : IO LintingOutcome := do
  let textGroups := collectTextLints env mod.getRoot
  let textGroups :=
    if args.lintOnly then
      textGroups.filterMap fun (m, entries) =>
        let entries := entries.filter fun e =>
          Lean.Linter.isLinterEnabledByOptions e.linter linterOpts
        if entries.isEmpty then none else some (m, entries)
    else textGroups
  let textFailed := !textGroups.isEmpty
  match args.mode with
  | .report =>
      for (m, entries) in textGroups do
        IO.println s!"-- Text linter diagnostics in {m}:"
        for e in entries do
          IO.print e.message.toString
      return .reported textFailed
  | .recordExceptions =>
      let mut records : Array ExceptionRecord := #[]
      let mut anyUnlocated := false
      for (m, entries) in textGroups do
        for e in entries do
          match e.position? with
          | some pos =>
            records := records.push { file := e.file, pos, option := e.linter }
          | none =>
            IO.eprintln s!"\
              warning: could not determine the command position of a `{e.linter}` text-linter \
              warning in `{m}`; skipping its exception"
            anyUnlocated := true
      return .recorded records anyUnlocated
    | .codeQuality =>
      let mut codeQualityEntries : Array CodeQuality.Entry := #[]
      for (m, entries) in textGroups do
        let counts : NameMap Nat := entries.foldl (init := {}) fun counts e =>
          counts.insert e.linter (counts.getD e.linter 0 + 1)
        for (linter, count) in counts do
          codeQualityEntries := codeQualityEntries.push { name := linter.toString
                                                          source := .module m
                                                          value := .scalar count.toFloat }
      return .codeQualityChecks codeQualityEntries

/--
Runs the registered environment linters over the declarations of the package rooted at
`mod.getRoot` that are present in `env`. Unlike text linters, environment linters inspect fully
elaborated declarations, so they run here rather than during the build; per-declaration
`set_option` exceptions are honored via the linter option snapshots persisted with each module.
By default all registered linters run; with `--lint-only`, only those explicitly enabled by the
command-line overrides do.

In `report` mode the findings are printed to stdout (grouped by file). In `recordExceptions` mode,
each flagged declaration is resolved to a source position via its declaration range and to a file
via `sp`, yielding exception records for the caller to write; declarations whose range or source
file cannot be resolved are reported on stderr and flagged as unlocated. In `codeQuality` mode,
the findings are aggregated per module/declaration/linter triple into code quality entries whose
scalar value is the number of warnings, for the caller to emit as JSON.
-/
private def runEnvironmentLinters (args : Args) (linterOpts : Linter.LinterOptions) (sp : SearchPath)
    (env : Environment) (mod : Name) : IO LintingOutcome := do
  let (outcome, _) ← CoreM.toIO (ctx := { fileName := "", fileMap := default }) (s := { env }) do
    let decls ← Linter.EnvLinter.getDeclsInPackage mod.getRoot
    let linters ← Linter.EnvLinter.getEnvLinters (if args.lintOnly then some linterOpts else none)
    if linters.isEmpty && args.mode == .report then do
      IO.println s!"-- No environment linters were run for {mod}."
      return .reported false
    let results ← Linter.EnvLinter.lintCore decls linters
    let failed := results.any (!·.2.isEmpty)
    match args.mode with
    | .report =>
        if failed then
          let fmtResults ←
            Linter.EnvLinter.formatLinterResults results decls
              (groupByFilename := true) (useErrorFormat := true)
              s!"in {mod}" linters.size
          IO.print (← fmtResults.toString)
        else
          IO.println s!"-- Environment linting passed for {mod}."
        return .reported failed
    | .recordExceptions =>
      let mainModule := (← getEnv).mainModule
      let mut recs : Array ExceptionRecord := #[]
      let mut unlocated := false
      for (linter, msgs) in results do
        for (declName, _) in msgs.toArray do
          match ← findDeclarationRanges? declName with
          | some ranges =>
            let declMod := (← findModuleOf? declName).getD mainModule
            match ← sp.findWithExt "lean" declMod with
            | some file =>
              recs := recs.push { file, pos := ranges.range.pos, option := linter.optName }
            | none =>
              IO.eprintln s!"\
                warning: could not locate source file for `{declMod}` \
                to record a `{linter.optName}` exception"
              unlocated := true
          | none =>
            IO.eprintln s!"\
              warning: no declaration range for `{declName}`; \
              cannot record a `{linter.optName}` exception"
            unlocated := true
      return .recorded recs unlocated
    | .codeQuality =>
      let mainModule := (← getEnv).mainModule
      let mut codeQualityEntries : Array CodeQuality.Entry := #[]
      for (linter, msgs) in results do
        -- (module, declaration) → warning count
        let mut counts : Std.TreeMap (Name × Name) Nat
            (fun a b => (a.1.quickCmp b.1).then (a.2.quickCmp b.2)) := {}
        for (declName, _) in msgs.toArray do
          let declMod := (← findModuleOf? declName).getD mainModule
          let key := (declMod, declName)
          counts := counts.insert key (counts.getD key 0 + 1)
        for ((declMod, declName), count) in counts do
          codeQualityEntries := codeQualityEntries.push { name := linter.optName.toString
                                                          source := .declaration declMod declName
                                                          value := .scalar count.toFloat }
      return .codeQualityChecks codeQualityEntries
  return outcome

public def run (args : Args) : IO UInt32 := do
  let mods := args.mods
  if mods.isEmpty then
    IO.eprintln "lake lint: no modules specified for builtin linting"
    return 1
  let envLinterModule : Import := { module := `Lean.Linter.EnvLinter }

  let sp := args.srcSearchPath ++ (← getSrcSearchPath)

  let mut anyFailed := false
  let mut anyUnlocated := false

  -- Accumulated exceptions to record (only populated when `args.recordExceptions` is set).
  let mut records : Array ExceptionRecord := #[]
  -- Accumulated code quality entries(only populated when `args.codeQuality` is set).
  let mut codeQualityEntries : Array CodeQuality.Entry := #[]
  -- Modules whose deferred docstring checks have already been run. A module can appear in
  -- several targets' import closures, so this runs each such module's checks only once.
  let mut docCheckedModules : NameSet := {}
  for mod in mods do
    unsafe Lean.enableInitializersExecution
    -- Peek at the .olean header to learn whether `mod` participates in the module system.
    -- If so, import at the server level level, mirroring `processHeaderCore`, while
    -- exposing server-level data (i.e. the state of `lintLogExt`).
    let modFile ← findOLean mod
    let (modData, region) ← readModuleData modFile
    let isModule ← getIsModule modData
    let level := if isModule then OLeanLevel.server else OLeanLevel.private
    unsafe region.free
    let env ← importModules #[{ module := mod }, envLinterModule] {}
      (trustLevel := 1024) (loadExts := true) (level := level)

    -- We create `LinterOptions` out of the passed overrides
    let linterOpts : Lean.Linter.LinterOptions := {
      toOptions := args.linterOverrides.foldl (init := {}) fun o (n, b) => o.setBool n b
      linterSets := (Lean.Linter.linterSetsExt.getState env).merged
    }

    let textLintingOutcome ← runTextLinters args linterOpts env mod
    match textLintingOutcome with
    | .reported textFailed =>
      anyFailed := anyFailed || textFailed
    | .recorded textRecords unlocated =>
      records := records ++ textRecords
      if unlocated then anyUnlocated := true
    | .codeQualityChecks entries =>
      codeQualityEntries := codeQualityEntries ++ entries

    let environmentLintingOutcome ← runEnvironmentLinters args linterOpts sp env mod

    match environmentLintingOutcome with
    | .reported declFailed =>
      if declFailed then anyFailed := true
    | .recorded envRecords envUnlocated =>
      records := records ++ envRecords
      if envUnlocated then anyUnlocated := true
    | .codeQualityChecks entries =>
      codeQualityEntries := codeQualityEntries ++ entries

    unless args.mode == .codeQuality do
      let deferredResults ← runDeferredChecks args linterOpts sp env mod.getRoot docCheckedModules
      docCheckedModules := deferredResults.checkedModules
      match deferredResults.outcome with
      | .reported failed =>
        if failed then anyFailed := true
      | .recorded recs unlocated =>
        records := records ++ recs
        if unlocated then anyUnlocated := true

  match args.mode with
  | .report =>
    return if anyFailed then 1 else 0
  | .recordExceptions =>
    recordExceptionsToFiles records
    return if anyUnlocated then 1 else 0
  | .codeQuality =>
    for entry in codeQualityEntries do
      IO.println <| toJson entry
    return 0

end Lake.BuiltinLint
