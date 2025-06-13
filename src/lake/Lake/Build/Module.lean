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

/--
Recursively parse the Lean files of a module and its imports
building an `Array` product of its direct local imports.
-/
def Module.recParseImports (mod : Module) : FetchM (Job (Array Module)) := Job.async do
  let contents ← IO.FS.readFile mod.leanFile
  let res ← Lean.parseImports' contents mod.leanFile.toString
  let mods ← res.imports.foldlM (init := OrdModuleSet.empty) fun set imp =>
    findModule? imp.module <&> fun | some mod => set.insert mod | none => set
  return mods.toArray

/-- The `ModuleFacetConfig` for the builtin `importsFacet`. -/
def Module.importsFacetConfig : ModuleFacetConfig importsFacet :=
  mkFacetJobConfig recParseImports (buildable := false)

structure ModuleImportData where
  module : Module
  transImports : Job (Array Module)
  includeSelf : Bool

@[inline] def collectImportsAux
  (leanFile : FilePath) (imports : Array Module)
  (f : Module → FetchM (Bool × Job (Array Module)))
: FetchM (Job (Array Module)) := do
  let imps ← imports.mapM fun imp => do
    let (includeSelf, transImports) ← f imp
    return {module := imp, transImports, includeSelf : ModuleImportData}
  let task : JobTask OrdModuleSet := imps.foldl (init := .pure (.ok .empty {})) fun r imp =>
    r.bind (sync := true) fun r =>
    imp.transImports.task.map (sync := true) fun
    | .ok transImps _ =>
      match r with
      | .ok impSet s =>
        let impSet := impSet.appendArray transImps
        let impSet := if imp.includeSelf then impSet.insert imp.module else impSet
        .ok impSet s
      | .error e s => .error e s
    | .error _ _ =>
      let entry := LogEntry.error s!"{leanFile}: bad import '{imp.module.name}'"
      match r with
      | .ok _ s => .error 0 (s.logEntry entry)
      | .error e s => .error e (s.logEntry entry)
  return Job.ofTask <| task.map (sync := true) fun
    | .ok impSet s => .ok impSet.toArray s
    | .error e s => .error e s

/-- Recursively compute a module's transitive imports. -/
def Module.recComputeTransImports (mod : Module) : FetchM (Job (Array Module)) := ensureJob do
  collectImportsAux mod.leanFile (← (← mod.imports.fetch).await) fun imp =>
    (true, ·) <$> imp.transImports.fetch

/-- The `ModuleFacetConfig` for the builtin `transImportsFacet`. -/
def Module.transImportsFacetConfig : ModuleFacetConfig transImportsFacet :=
  mkFacetJobConfig recComputeTransImports (buildable := false)

def computePrecompileImportsAux
  (leanFile : FilePath) (imports : Array Module)
: FetchM (Job (Array Module)) := do
  collectImportsAux leanFile imports fun imp =>
    if imp.shouldPrecompile then
      (true, ·) <$> imp.transImports.fetch
    else
      (false, ·) <$> imp.precompileImports.fetch

/-- Recursively compute a module's precompiled imports. -/
def Module.recComputePrecompileImports (mod : Module) : FetchM (Job (Array Module)) := ensureJob do
  inline <| computePrecompileImportsAux mod.leanFile (← (← mod.imports.fetch).await)

/-- The `ModuleFacetConfig` for the builtin `precompileImportsFacet`. -/
def Module.precompileImportsFacetConfig : ModuleFacetConfig precompileImportsFacet :=
  mkFacetJobConfig recComputePrecompileImports (buildable := false)

/-- Fetch dynlibs of the packages' external libraries. **For internal use.** -/
def fetchExternLibs (pkgs : Array Package) : FetchM (Job (Array Dynlib)) :=
  Job.collectArray <$> pkgs.flatMapM (·.externLibs.mapM (·.dynlib.fetch))

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
**For internal use.**

Fetches the library dynlibs of a list of non-local imports.
Modules are loaded as part of their whole library.
-/
def fetchImportLibs
  (mods : Array Module) : FetchM (Job (Array Dynlib))
:= do
  let (_, jobs) ← mods.foldlM (init := (({} : NameSet), #[])) fun (libs, jobs) imp => do
    if libs.contains imp.lib.name then
      return (libs, jobs)
    else if imp.shouldPrecompile then
      let jobs ← jobs.push <$> imp.lib.shared.fetch
      return (libs.insert imp.lib.name, jobs)
    else
      return (libs, jobs)
  return Job.collectArray jobs "import dynlibs"

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

def computeModuleDeps
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

/--
Recursively build a module's dependencies, including:
* Transitive local imports
* Shared libraries (e.g., `extern_lib` targets or precompiled modules)
* `extraDepTargets` of its library
-/
def Module.recBuildDeps (mod : Module) : FetchM (Job ModuleDeps) := ensureJob do
  let extraDepJob ← mod.lib.extraDep.fetch

  /-
  Remark: We must build direct imports before we fetch the transitive
  precompiled imports so that errors in the import block of transitive imports
  will not kill this job before the direct imports are built.
  -/
  let directImports ← (← mod.imports.fetch).await
  let importJobs ← directImports.mapM fun imp => do
    if imp.name = mod.name then
      logError s!"{mod.leanFile}: module imports itself"
    imp.olean.fetch
  let importJob := Job.mixArray importJobs "import oleans"
  /-
  Remark: It should be possible to avoid transitive imports here when the module
  itself is precompiled, but they are currently kept to preserve the "bad import" errors.
  -/
  let precompileImports ← if mod.shouldPrecompile then
    mod.transImports.fetch else mod.precompileImports.fetch
  let precompileImports ← precompileImports.await
  let impLibsJob ← Job.collectArray (traceCaption := "import dynlibs") <$>
    mod.fetchImportLibs precompileImports mod.shouldPrecompile
  let externLibsJob ← Job.collectArray (traceCaption := "package external libraries") <$>
    if mod.shouldPrecompile then mod.pkg.externLibs.mapM (·.dynlib.fetch) else pure #[]
  let dynlibsJob ← mod.dynlibs.fetchIn mod.pkg "module dynlibs"
  let pluginsJob ← mod.plugins.fetchIn mod.pkg "module plugins"

  extraDepJob.bindM (sync := true) fun _ => do
  importJob.bindM (sync := true) fun _ => do
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
    computeModuleDeps impLibs externLibs dynlibs plugins

/-- The `ModuleFacetConfig` for the builtin `depsFacet`. -/
def Module.depsFacetConfig : ModuleFacetConfig depsFacet :=
  mkFacetJobConfig recBuildDeps

/-- Remove cached file hashes of the module build outputs (in `.hash` files). -/
def Module.clearOutputHashes (mod : Module) : IO PUnit := do
  clearFileHash mod.oleanFile
  clearFileHash mod.ileanFile
  clearFileHash mod.cFile
  if Lean.Internal.hasLLVMBackend () then
    clearFileHash mod.bcFile

/-- Cache the file hashes of the module build outputs in `.hash` files. -/
def Module.cacheOutputHashes (mod : Module) : IO PUnit := do
  cacheFileHash mod.oleanFile
  cacheFileHash mod.ileanFile
  cacheFileHash mod.cFile
  if Lean.Internal.hasLLVMBackend () then
    cacheFileHash mod.bcFile

/--
Recursively build a Lean module.
Fetch its dependencies and then elaborate the Lean source file, producing
all possible artifacts (i.e., `.olean`, `ilean`, `.c`, and `.bc`).
-/
def Module.recBuildLean (mod : Module) : FetchM (Job Unit) := do
  withRegisterJob mod.name.toString do
  (← mod.deps.fetch).mapM fun {dynlibs, plugins} => do
    addLeanTrace
    addPureTrace mod.leanArgs "Module.leanArgs"
    let srcTrace ← computeTrace (TextFilePath.mk mod.leanFile)
    addTrace srcTrace
    setTraceCaption s!"{mod.name.toString}:leanArts"
    let upToDate ← buildUnlessUpToDate? (oldTrace := srcTrace.mtime) mod (← getTrace) mod.traceFile do
      compileLeanModule mod.leanFile mod.relLeanFile mod.oleanFile mod.ileanFile mod.cFile mod.bcFile?
        (← getLeanPath) mod.rootDir dynlibs plugins
        (mod.weakLeanArgs ++ mod.leanArgs) (← getLean)
      mod.clearOutputHashes
    unless upToDate && (← getTrustHash) do
      mod.cacheOutputHashes

/-- The `ModuleFacetConfig` for the builtin `leanArtsFacet`. -/
def Module.leanArtsFacetConfig : ModuleFacetConfig leanArtsFacet :=
  mkFacetJobConfig recBuildLean

/-- The `ModuleFacetConfig` for the builtin `oleanFacet`. -/
def Module.oleanFacetConfig : ModuleFacetConfig oleanFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      /-
      Avoid recompiling unchanged Olean files.
      Olean files incorporate not only their own content, but also their
      transitive imports. However, they are independent of their module sources.
      -/
      newTrace s!"{mod.name.toString}:olean"
      addTrace (← mod.deps.fetch).getTrace.withoutInputs
      addTrace (← fetchFileTrace mod.oleanFile)
      return mod.oleanFile

/-- The `ModuleFacetConfig` for the builtin `ileanFacet`. -/
def Module.ileanFacetConfig : ModuleFacetConfig ileanFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      /-
      Avoid recompiling unchanged Ilean files.
      Ilean files are assumed to only incorporate their own content
      and not transitively include their inputs (e.g., imports).
      Lean also produces LF-only Ilean files, so no line ending normalization.
      -/
      newTrace s!"{mod.name.toString}:ilean"
      addTrace (← fetchFileTrace mod.ileanFile)
      return mod.ileanFile

/-- The `ModuleFacetConfig` for the builtin `cFacet`. -/
def Module.cFacetConfig : ModuleFacetConfig cFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      /-
      Avoid recompiling unchanged C files.
      C files are assumed to incorporate their own content
      and not transitively include their inputs (e.g., imports).
      They do, however, include `lean/lean.h`.
      Lean also produces LF-only C files, so no line ending normalization.
      -/
      newTrace s!"{mod.name.toString}:c"
      addTrace (← fetchFileTrace mod.cFile)
      addLeanTrace
      return mod.cFile

/-- The `ModuleFacetConfig` for the builtin `bcFacet`. -/
def Module.bcFacetConfig : ModuleFacetConfig bcFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      /-
      Avoid recompiling unchanged bitcode files.
      Bitcode files are assumed to only depend on their content
      and not transitively on their inputs (e.g., imports).
      -/
      newTrace s!"{mod.name.toString}:bc"
      addTrace (← fetchFileTrace mod.bcFile)
      return mod.bcFile

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
  |>.insert importsFacet importsFacetConfig
  |>.insert transImportsFacet transImportsFacetConfig
  |>.insert precompileImportsFacet precompileImportsFacetConfig
  |>.insert depsFacet depsFacetConfig
  |>.insert leanArtsFacet leanArtsFacetConfig
  |>.insert oleanFacet oleanFacetConfig
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
  (leanFile : FilePath) (imports : Array Module)
: FetchM (Job ModuleDeps) := do
  withRegisterJob s!"setup ({leanFile})" do
  let root ← getRootPackage
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    root.extraDep.fetch <&> (·.map fun _ => {})
  else
    -- build local imports from list
    let modJob := Job.mixArray <| ← imports.mapM (·.olean.fetch)
    let precompileImports ← (← computePrecompileImportsAux leanFile imports).await
    let pkgs := precompileImports.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
    let externLibsJob ← fetchExternLibs pkgs
    let impLibsJob ← fetchImportLibs precompileImports
    let dynlibsJob ← root.dynlibs.fetchIn root
    let pluginsJob ← root.plugins.fetchIn root
    modJob.bindM (sync := true) fun _ =>
    impLibsJob.bindM (sync := true) fun impLibs =>
    dynlibsJob.bindM (sync := true) fun dynlibs =>
    pluginsJob.bindM (sync := true) fun plugins =>
    externLibsJob.mapM fun externLibs => do
      computeModuleDeps impLibs externLibs dynlibs plugins
