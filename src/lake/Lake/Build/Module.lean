/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone, Siddharth Bhat
-/
prelude
import Lake.Util.OrdHashSet
import Lake.Util.List
import Lean.Elab.ParseImportsFast
import Lake.Build.Common
import Lake.Build.Target

/-! # Module Facet Builds
Build function definitions for a module's builtin facets.
-/

open System Lean

namespace Lake

/-- Compute library directories and build external library Jobs of the given packages. -/
@[deprecated "Deprecated without replacement" (since := "2025-03-28")]
def recBuildExternDynlibs (pkgs : Array Package)
: FetchM (Array (Job Dynlib) × Array FilePath) := do
  let mut libDirs := #[]
  let mut jobs : Array (Job Dynlib) := #[]
  for pkg in pkgs do
    libDirs := libDirs.push pkg.sharedLibDir
    jobs := jobs.append <| ← pkg.externLibs.mapM (·.dynlib.fetch)
  return (jobs, libDirs)

/-- The `ModuleFacetConfig` for the builtin `srcFacet`. -/
def Module.srcFacetConfig : ModuleFacetConfig srcFacet :=
  mkFacetJobConfig fun mod => inputFile mod.leanFile (text := true)

/-- Parse the header of a Lean file from its source. -/
def Module.recParseHeader (mod : Module) : FetchM (Job ModuleHeader) := do
  (← mod.src.fetch).mapM fun srcFile => do
    setTraceCaption s!"{mod.name}:header"
    let contents ← IO.FS.readFile srcFile
    Lean.parseImports' contents srcFile.toString

/-- The `ModuleFacetConfig` for the builtin `headerFacet`. -/
def Module.headerFacetConfig : ModuleFacetConfig headerFacet :=
  mkFacetJobConfig recParseHeader (buildable := false)

/-- Compute an `Array` of a module's direct local imports from its header. -/
def Module.recParseImports (mod : Module) : FetchM (Job (Array Module)) := do
  (← mod.header.fetch).mapM (sync := true) fun header => do
    let mods ← header.imports.foldlM (init := OrdModuleSet.empty) fun set imp =>
      findModule? imp.module <&> fun | some mod => set.insert mod | none => set
    return mods.toArray

/-- The `ModuleFacetConfig` for the builtin `importsFacet`. -/
def Module.importsFacetConfig : ModuleFacetConfig importsFacet :=
  mkFacetJobConfig recParseImports (buildable := false)

private def computeAllImportsAux
  (leanFile : FilePath) (libName? : Option Name) (imports : Array Import)
: FetchM (Job ModuleImports) := do
  let task : JobTask ModuleImports := .pure (.ok {libName? := libName?} {})
  let task ← imports.foldlM (init := task) fun task imp => do
    let some mod ← findModule? imp.module
      | return task
    let impsJob ← mod.allImports.fetch
    let task :=
      task.bind (sync := true) fun r =>
      impsJob.task.map (sync := true) fun
      | .ok transImps _ =>
        match r with
        | .ok imps s => Id.run do
          let imps := imps.append transImps
          let imps := imps.insert mod imp.isExported
          return .ok imps s
        | .error e s => .error e s
      | .error _ _ =>
        let entry := LogEntry.error s!"{leanFile}: bad import '{mod.name}'"
        match r with
        | .ok _ s => .error 0 (s.logEntry entry)
        | .error e s => .error e (s.logEntry entry)
    return task
  return Job.ofTask task

def Module.recComputeAllImports (self : Module) : FetchM (Job ModuleImports) := do
  (← self.header.fetch).bindM fun header =>
    computeAllImportsAux self.relLeanFile self.lib.name header.imports

/-- The `ModuleFacetConfig` for the builtin `allImportsFacet`. -/
def Module.allImportsFacetConfig : ModuleFacetConfig allImportsFacet :=
  mkFacetJobConfig recComputeAllImports (buildable := false)

/-- Recursively compute a module's transitive imports. -/
def Module.recComputeTransImports (mod : Module) : FetchM (Job (Array Module)) := ensureJob do
  return (← mod.allImports.fetch).map (sync := true) (·.transImports)

/-- The `ModuleFacetConfig` for the builtin `transImportsFacet`. -/
def Module.transImportsFacetConfig : ModuleFacetConfig transImportsFacet :=
  mkFacetJobConfig recComputeTransImports (buildable := false)

/-- Recursively compute a module's precompiled imports. -/
def Module.recComputePrecompileImports (mod : Module) : FetchM (Job (Array Module)) := ensureJob do
  return (← mod.allImports.fetch).map (sync := true) fun imps =>
    if mod.shouldPrecompile then
      imps.transImports
    else
      imps.transImports.filter (·.shouldPrecompile)

/-- The `ModuleFacetConfig` for the builtin `precompileImportsFacet`. -/
def Module.precompileImportsFacetConfig : ModuleFacetConfig precompileImportsFacet :=
  mkFacetJobConfig recComputePrecompileImports (buildable := false)

/--
Computes the transitive dynamic libraries of a module's imports.
Modules from the same library are loaded individually, while modules
from other libraries are loaded as part of the whole library.
-/
private def Module.fetchImportLibs
  (self : Module) (imps : Array Module) (compileSelf : Bool)
: FetchM (Array (Job Dynlib)) := do
  let (_, jobs) ← imps.foldlM (init := (({} : NameSet), #[])) fun (libs, jobs) imp => do
    if libs.contains imp.lib.name then
      return (libs, jobs)
    else if compileSelf && self.lib.name = imp.lib.name then
      let job ← imp.dynlib.fetch
      return (libs, jobs.push job)
    else if compileSelf || imp.shouldPrecompile then
      let jobs ← jobs.push <$> imp.lib.shared.fetch
      return (libs.insert imp.lib.name, jobs)
    else
      return (libs, jobs)
  return jobs

/--
Topologically sorts the library dependency tree by name.
Libraries come *after* their dependencies.
-/
private partial def mkLoadOrder (libs : Array Dynlib) : FetchM (Array Dynlib) := do
  let r := libs.foldlM (m := Except (Cycle String)) (init := ({}, #[])) fun (v, o) lib =>
    go lib [] v o
  match r with
  | .ok (_, order) => pure order
  | .error cycle => error s!"library dependency cycle:\n{formatCycle cycle}"
where
  go lib (ps : List String) (v : RBMap String Unit compare) (o : Array Dynlib) := do
    if v.contains lib.name then
      return (v, o)
    if ps.contains lib.name then
      throw (lib.name :: ps)
    let ps := lib.name :: ps
    let v := v.insert lib.name ()
    let (v, o) ← lib.deps.foldlM (init := (v, o)) fun (v, o) lib =>
      go lib ps v o
    let o := o.push lib
    return (v, o)

private def computeModuleDeps
  (impLibs : Array Dynlib) (externLibs : Array Dynlib)
  (dynlibs : Array Dynlib) (plugins : Array Dynlib)
: FetchM ModuleDeps := do
  /-
  Requirements:
  * Lean wants the external library symbols before module symbols.
  * Unix requires the file extension of the dynlib.
  * For some reason, building from the Lean server requires full paths.
    Everything else loads fine with just the augmented library path.
  * Linux needs the augmented path to resolve nested dependencies in dynlibs.
  -/
  let impLibs ← mkLoadOrder impLibs
  let mut dynlibs := externLibs ++ dynlibs
  let mut plugins := plugins
  for impLib in impLibs do
    if impLib.plugin then
      plugins := plugins.push impLib
    else
      dynlibs := dynlibs.push impLib
  /-
  On MacOS, Lake must be loaded as a plugin for
  `import Lake` to work with precompiled modules.
  https://github.com/leanprover/lean4/issues/7388
  -/
  if Platform.isOSX && !(plugins.isEmpty && dynlibs.isEmpty) then
    plugins := plugins.push (← getLakeInstall).sharedDynlib
  return {dynlibs, plugins}

private def Module.fetchOLeanArts
  (mod : Module) (importAll : Bool := false)
: FetchM (Job ModuleArtifacts) := do
  let eJob ← mod.olean.fetch
  if importAll then
    fetchAll eJob
  else
    (← mod.header.fetch).bindM fun header => do
      if header.isModule then
        fetchAll eJob
      else
        newTrace mod.name.toString
        eJob.mapM (sync := true) fun olean => do
          return {olean? := olean}
where
  fetchAll eJob := do
    let sJob ← mod.oleanServer.fetch
    let pJob ← mod.oleanPrivate.fetch
    eJob.bindM (sync := true) fun oe =>
    sJob.bindM (sync := true) fun os =>
    pJob.mapM (sync := true) fun op => do
      setTraceCaption mod.name.toString
      return {olean? := oe, oleanServer? := os, oleanPrivate? := op}

/--
Recursively build a module's dependencies, including:
* Transitive local imports
* Shared libraries (e.g., `extern_lib` targets or precompiled modules)
* `extraDepTargets` of its library
-/
def Module.recFetchSetup (mod : Module) : FetchM (Job ModuleSetup) := ensureJob do
  let extraDepJob ← mod.lib.extraDep.fetch

  let headerJob ← mod.header.fetch
  let impsJob ← mod.allImports.fetch
  let impArtsJob ←
    headerJob.bindM fun header => do
      let artsJobMap : NameMap (Job ModuleArtifacts) := {}
      /-
      Remark: Errors in the transitive import graph will prevent downstream builds.
      Thus, we fetch the direct import artifacts first so they can still potentially
      succeed even if the overall graph is erroneous.
      -/
      let artsJobMap ← header.imports.foldlM (init := artsJobMap) fun s imp => do
        if s.contains imp.module then
          return s
        if mod.name = imp.module then
          logError s!"{mod.relLeanFile}: module imports itself"
          return s
        let some mod ← findModule? imp.module
          | return s
        return s.insert mod.name (← mod.fetchOLeanArts imp.importAll)
      impsJob.bindM fun imps => do
        let artsJobMap ← imps.publicImports.foldlM (init := artsJobMap) fun s mod =>
          if s.contains mod.name then
            return s
          else
            return s.insert mod.name (← mod.fetchOLeanArts)
        return Job.collectNameMap artsJobMap "import artifacts"
  let impLibsJob ← impsJob.bindM fun imps => do
    let jobs ←
      if mod.shouldPrecompile then
        let jobs := #[]
        let jobs ← imps.localImports.foldlM (·.push <$> ·.dynlib.fetch) jobs
        imps.libs.foldlM (·.push <$> ·.shared.fetch) jobs
      else
        imps.libs.foldlM (init := #[]) fun jobs lib =>
          if lib.precompileModules then jobs.push <$> lib.shared.fetch else pure jobs
    return Job.collectArray jobs "import dynlibs"
  let externLibsJob ← Job.collectArray (traceCaption := "package external libraries") <$>
    if mod.shouldPrecompile then mod.pkg.externLibs.mapM (·.dynlib.fetch) else pure #[]
  let dynlibsJob ← mod.dynlibs.fetchIn mod.pkg "module dynlibs"
  let pluginsJob ← mod.plugins.fetchIn mod.pkg "module plugins"

  extraDepJob.bindM (sync := true) fun _ => do
  headerJob.bindM (sync := true) fun header => do
  impArtsJob.bindM (sync := true) fun modules => do
  let depTrace ← takeTrace
  impLibsJob.bindM (sync := true) fun impLibs => do
  externLibsJob.bindM (sync := true) fun externLibs => do
  dynlibsJob.bindM (sync := true) fun dynlibs => do
  pluginsJob.mapM fun plugins => do
    let libTrace ← takeTrace
    setTraceCaption s!"{mod.name.toString}:deps"
    let depTrace := depTrace.withCaption "deps"
    let libTrace := libTrace.withCaption "libs"
    match mod.platformIndependent with
    | none => addTrace depTrace; addTrace libTrace
    | some false => addTrace depTrace; addTrace libTrace; addPlatformTrace
    | some true => addTrace depTrace
    let {dynlibs, plugins} ← computeModuleDeps impLibs externLibs dynlibs plugins
    return {
      name := mod.name
      isModule := header.isModule
      imports := header.imports
      modules := modules
      dynlibs := dynlibs.map (·.path.toString)
      plugins := plugins.map (·.path.toString)
      options := mod.leanOptions
    }

/-- The `ModuleFacetConfig` for the builtin `setupFacet`. -/
def Module.setupFacetConfig : ModuleFacetConfig setupFacet :=
  mkFacetJobConfig recFetchSetup

/-- The `ModuleFacetConfig` for the builtin `depsFacet`. -/
def Module.depsFacetConfig : ModuleFacetConfig depsFacet :=
  mkFacetJobConfig fun mod => (·.toOpaque) <$> mod.setup.fetch

/-- Remove any cached file hashes of the module build outputs (in `.hash` files). -/
def Module.clearOutputHashes (mod : Module) : IO PUnit := do
  clearFileHash mod.oleanFile
  clearFileHash mod.oleanServerFile
  clearFileHash mod.oleanPrivateFile
  clearFileHash mod.ileanFile
  clearFileHash mod.cFile
  clearFileHash mod.bcFile

/-- Cache the file hashes of the module build outputs in `.hash` files. -/
def Module.cacheOutputHashes (mod : Module) : IO PUnit := do
  cacheFileHash mod.oleanFile
  if (← mod.oleanServerFile.pathExists) then
    cacheFileHash mod.oleanServerFile
  if (← mod.oleanPrivateFile.pathExists)  then
    cacheFileHash mod.oleanPrivateFile
  cacheFileHash mod.ileanFile
  cacheFileHash mod.cFile
  if Lean.Internal.hasLLVMBackend () then
    cacheFileHash mod.bcFile

private def traceOptions (opts : LeanOptions) (caption := "opts") : BuildTrace :=
  opts.values.fold (init := .nil caption) fun t n v =>
    let opt := s!"-D{n}={v.asCliFlagValue}"
    t.mix <| .ofHash (pureHash opt) opt

/--
Recursively build a Lean module.
Fetch its dependencies and then elaborate the Lean source file, producing
all possible artifacts (e.g., `.olean`, `.ilean`, `.c`, `.bc`).
-/
def Module.recBuildLean (mod : Module) : FetchM (Job ModuleArtifacts) := do
  withRegisterJob mod.name.toString do
  (← mod.src.fetch).bindM fun srcFile => do
  let srcTrace ← getTrace
  (← mod.setup.fetch).mapM fun setup => do
    addLeanTrace
    addTrace <| traceOptions setup.options "options"
    addPureTrace mod.leanArgs "Module.leanArgs"
    setTraceCaption s!"{mod.name.toString}:leanArts"
    let arts : ModuleArtifacts := {
      lean? := srcFile
      olean? := mod.oleanFile
      oleanServer? := if setup.isModule then some mod.oleanServerFile else none
      oleanPrivate? := if setup.isModule then some mod.oleanPrivateFile else none
      ilean? := mod.ileanFile
      c? := mod.cFile
      bc? := if Lean.Internal.hasLLVMBackend () then some mod.bcFile else none
    }
    let upToDate ← buildUnlessUpToDate? (oldTrace := srcTrace.mtime) mod (← getTrace) mod.traceFile do
      let args := mod.weakLeanArgs ++ mod.leanArgs
      let relSrcFile := relPathFrom mod.pkg.dir srcFile
      compileLeanModule srcFile relSrcFile setup mod.setupFile arts args
        (← getLeanPath) mod.rootDir (← getLean)
      mod.clearOutputHashes
    unless upToDate && (← getTrustHash) do
      mod.cacheOutputHashes
    return arts

/-- The `ModuleFacetConfig` for the builtin `leanArtsFacet`. -/
def Module.leanArtsFacetConfig : ModuleFacetConfig leanArtsFacet :=
  mkFacetJobConfig recBuildLean

@[inline] private def Module.fetchOLeanCore
  (facet : String) (f : ModuleArtifacts → Option FilePath) (errMsg : String) (mod : Module)
: FetchM (Job FilePath) := do
  (← mod.leanArts.fetch).mapM fun arts => do
      let some oleanFile := f arts
        | error errMsg
      /-
      Avoid recompiling unchanged OLean files.
      While OLean files transitively include their imports,
      Lake also traverses this graph itself, so the transtive imports
      are not included in this trace.
      -/
      newTrace s!"{mod.name.toString}:{facet}"
      addTrace (← fetchFileTrace oleanFile)
      return oleanFile

/-- The `ModuleFacetConfig` for the builtin `oleanFacet`. -/
def Module.oleanFacetConfig : ModuleFacetConfig oleanFacet :=
  mkFacetJobConfig <| fetchOLeanCore "olean" (·.olean?)
    "No olean generated. This is likely an error in Lean or Lake."

/-- The `ModuleFacetConfig` for the builtin `oleanServerFacet`. -/
def Module.oleanServerFacetConfig : ModuleFacetConfig oleanServerFacet :=
  mkFacetJobConfig <| fetchOLeanCore "olean.server" (·.oleanServer?)
    "No server olean generated. Ensure the module system is enabled."

/-- The `ModuleFacetConfig` for the builtin `oleanPrivateFacet`. -/
def Module.oleanPrivateFacetConfig : ModuleFacetConfig oleanPrivateFacet :=
  mkFacetJobConfig <| fetchOLeanCore "olean.private" (·.oleanPrivate?)
    "No private olean generated. Ensure the module system is enabled."

/-- The `ModuleFacetConfig` for the builtin `ileanFacet`. -/
def Module.ileanFacetConfig : ModuleFacetConfig ileanFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun arts => do
      let some ileanFile := arts.ilean?
        | error "No ilean generated. This is likely an error in Lean or Lake."
      /-
      Avoid recompiling unchanged Ilean files.
      Ilean files are assumed to only incorporate their own content
      and not transitively include their inputs (e.g., imports).
      Lean also produces LF-only Ilean files, so no line ending normalization.
      -/
      newTrace s!"{mod.name.toString}:ilean"
      addTrace (← fetchFileTrace ileanFile)
      return ileanFile

/-- The `ModuleFacetConfig` for the builtin `cFacet`. -/
def Module.cFacetConfig : ModuleFacetConfig cFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun arts => do
      let some cFile := arts.c?
        | error "No C file generated. This is likely an error in Lean or Lake."
      /-
      Avoid recompiling unchanged C files.
      C files are assumed to incorporate their own content
      and not transitively include their inputs (e.g., imports).
      They do, however, include `lean/lean.h`.
      Lean also produces LF-only C files, so no line ending normalization.
      -/
      newTrace s!"{mod.name.toString}:c"
      addTrace (← fetchFileTrace cFile)
      addLeanTrace
      return cFile

/-- The `ModuleFacetConfig` for the builtin `bcFacet`. -/
def Module.bcFacetConfig : ModuleFacetConfig bcFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun arts => do
      let some bcFile := arts.bc?
        | error "No LLVM bitcode generated. Ensure your Lean version supports the LLVM backend."
      /-
      Avoid recompiling unchanged bitcode files.
      Bitcode files are assumed to only depend on their content
      and not transitively on their inputs (e.g., imports).
      -/
      newTrace s!"{mod.name.toString}:bc"
      addTrace (← fetchFileTrace bcFile)
      return bcFile

/--
Recursively build the module's object file from its C file produced by `lean`
with `-DLEAN_EXPORTING` set, which exports Lean symbols defined within the C files.
-/
def Module.recBuildLeanCToOExport (self : Module) : FetchM (Job FilePath) := do
  let suffix := if (← getIsVerbose) then " (with exports)" else ""
  withRegisterJob s!"{self.name}:c.o{suffix}" do
  -- TODO: add option to pass a target triplet for cross compilation
  let leancArgs := self.leancArgs ++ #["-DLEAN_EXPORTING"]
  buildLeanO self.coExportFile (← self.c.fetch) self.weakLeancArgs leancArgs self.leanIncludeDir?

/-- The `ModuleFacetConfig` for the builtin `coExportFacet`. -/
def Module.coExportFacetConfig : ModuleFacetConfig coExportFacet :=
  mkFacetJobConfig Module.recBuildLeanCToOExport

/--
Recursively build the module's object file from its C file produced by `lean`.
This version does not export any Lean symbols.
-/
def Module.recBuildLeanCToONoExport (self : Module) : FetchM (Job FilePath) := do
  let suffix := if (← getIsVerbose) then " (without exports)" else ""
  withRegisterJob s!"{self.name}:c.o{suffix}" do
  -- TODO: add option to pass a target triplet for cross compilation
  buildLeanO self.coNoExportFile (← self.c.fetch) self.weakLeancArgs self.leancArgs self.leanIncludeDir?

/-- The `ModuleFacetConfig` for the builtin `coNoExportFacet`. -/
def Module.coNoExportFacetConfig : ModuleFacetConfig coNoExportFacet :=
  mkFacetJobConfig recBuildLeanCToONoExport

/-- The `ModuleFacetConfig` for the builtin `coFacet`. -/
def Module.coFacetConfig : ModuleFacetConfig coFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    if Platform.isWindows then mod.coNoExport.fetch else mod.coExport.fetch

/-- Recursively build the module's object file from its bitcode file produced by `lean`. -/
def Module.recBuildLeanBcToO (self : Module) : FetchM (Job FilePath) := do
  withRegisterJob s!"{self.name}:bc.o" do
  -- TODO: add option to pass a target triplet for cross compilation
  buildLeanO self.bcoFile (← self.bc.fetch) self.weakLeancArgs self.leancArgs

/-- The `ModuleFacetConfig` for the builtin `bcoFacet`. -/
def Module.bcoFacetConfig : ModuleFacetConfig bcoFacet :=
  mkFacetJobConfig recBuildLeanBcToO

/-- The `ModuleFacetConfig` for the builtin `oExportFacet`. -/
def Module.oExportFacetConfig : ModuleFacetConfig oExportFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    match mod.backend with
    | .default | .c => mod.coExport.fetch
    | .llvm => mod.bco.fetch

/-- The `ModuleFacetConfig` for the builtin `oNoExportFacet`. -/
def Module.oNoExportFacetConfig : ModuleFacetConfig oNoExportFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    match mod.backend with
    | .default | .c => mod.coNoExport.fetch
    | .llvm => error "the LLVM backend only supports exporting Lean symbols"

/-- The `ModuleFacetConfig` for the builtin `oFacet`. -/
def Module.oFacetConfig : ModuleFacetConfig oFacet :=
  mkFacetJobConfig (memoize := false) fun mod =>
    match mod.backend with
    | .default | .c => mod.co.fetch
    | .llvm => mod.bco.fetch

/--
Recursively build the shared library of a module
(e.g., for `--load-dynlib` or `--plugin`).
-/
def Module.recBuildDynlib (mod : Module) : FetchM (Job Dynlib) :=
  withRegisterJob s!"{mod.name}:dynlib" do
  /-
  Fetch the module's object files.

  NOTE: The `moreLinkObjs` of the module's library are not included
  here because they would then be linked to the dynlib of each module of the library.
  On Windows, were module dynlibs must be linked with those of their imports, this would
  result in duplicate symbols when one library module imports another of the same library.
  -/
  let objJobs ← (mod.nativeFacets true).mapM (·.fetch mod)
  -- Fetch dependencies' dynlibs
  let libJobs ← id do
    let imps ← (← mod.imports.fetch).await
    let libJobs ← mod.fetchImportLibs imps true
    let libJobs ← mod.lib.moreLinkLibs.foldlM
      (·.push <$> ·.fetchIn mod.pkg) libJobs
    let libJobs ← mod.pkg.externLibs.foldlM
      (·.push <$> ·.dynlib.fetch) libJobs
    return libJobs
  buildLeanSharedLib mod.dynlibName mod.dynlibFile objJobs libJobs
    mod.weakLinkArgs mod.linkArgs (plugin := true)

/-- The `ModuleFacetConfig` for the builtin `dynlibFacet`. -/
def Module.dynlibFacetConfig : ModuleFacetConfig dynlibFacet :=
  mkFacetJobConfig recBuildDynlib

/--
A name-configuration map for the initial set of
Lake module facets (e.g., `imports`, `c`, `o`, `dynlib`).
-/
def Module.initFacetConfigs : DNameMap ModuleFacetConfig :=
  DNameMap.empty
  |>.insert srcFacet srcFacetConfig
  |>.insert headerFacet headerFacetConfig
  |>.insert importsFacet importsFacetConfig
  |>.insert transImportsFacet transImportsFacetConfig
  |>.insert precompileImportsFacet precompileImportsFacetConfig
  |>.insert allImportsFacet allImportsFacetConfig
  |>.insert setupFacet setupFacetConfig
  |>.insert depsFacet depsFacetConfig
  |>.insert leanArtsFacet leanArtsFacetConfig
  |>.insert oleanFacet oleanFacetConfig
  |>.insert oleanServerFacet oleanServerFacetConfig
  |>.insert oleanPrivateFacet oleanPrivateFacetConfig
  |>.insert ileanFacet ileanFacetConfig
  |>.insert cFacet cFacetConfig
  |>.insert bcFacet bcFacetConfig
  |>.insert coFacet coFacetConfig
  |>.insert coExportFacet coExportFacetConfig
  |>.insert coNoExportFacet coNoExportFacetConfig
  |>.insert bcoFacet bcoFacetConfig
  |>.insert oFacet oFacetConfig
  |>.insert oExportFacet oExportFacetConfig
  |>.insert oNoExportFacet oNoExportFacetConfig
  |>.insert dynlibFacet dynlibFacetConfig

@[inherit_doc Module.initFacetConfigs]
abbrev initModuleFacetConfigs := Module.initFacetConfigs

/-!
Definitions to support `lake setup-file` builds.
-/

/--
Builds an `Array` of module imports for a Lean file.
Used by `lake setup-file` to build modules for the Lean server and
by `lake lean` to build the imports of a file.
Returns the dynlibs and plugins built (so they can be loaded by Lean).
-/
def buildImportsAndDeps
  (leanFile : FilePath) (imports : Array Import)
: FetchM (Job ModuleDeps) := do
  withRegisterJob s!"setup ({leanFile})" do
  let root ← getRootPackage
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    root.extraDep.fetch <&> (·.map fun _ => {})
  else
    -- build local imports from list
    let modJob ← imports.foldlM (init := Job.pure ()) fun job imp => do
      let some mod ← findModule? imp.module
        | return job
      job.mix <$> mod.fetchOLeanArts imp.importAll
    let impsJob ← computeAllImportsAux leanFile none imports
    let externLibsJob ← Job.collectArray <$>
      if root.precompileModules then root.externLibs.mapM (·.dynlib.fetch) else pure #[]
    let impLibsJob ← impsJob.bindM fun {libs, ..} =>
      Job.collectArray <$> libs.foldlM (init := #[]) fun jobs lib =>
        if lib.precompileModules then jobs.push <$> lib.shared.fetch else pure jobs
    let dynlibsJob ← root.dynlibs.fetchIn root
    let pluginsJob ← root.plugins.fetchIn root
    modJob.bindM (sync := true) fun _ =>
    impLibsJob.bindM (sync := true) fun impLibs =>
    dynlibsJob.bindM (sync := true) fun dynlibs =>
    pluginsJob.bindM (sync := true) fun plugins =>
    externLibsJob.mapM fun externLibs => do
      computeModuleDeps impLibs externLibs dynlibs plugins
