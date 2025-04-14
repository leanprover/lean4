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
  let imports ← Lean.parseImports' contents mod.leanFile.toString
  let mods ← imports.foldlM (init := OrdModuleSet.empty) fun set imp =>
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

private def Module.fetchImportLibsCore
  (self : Module) (imps : Array Module) (compileSelf : Bool)
  (init : NameSet × Array (Job Dynlib))
: FetchM (NameSet × Array (Job Dynlib)) :=
  imps.foldlM (init := init) fun (libs, jobs) imp => do
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
/--
Computes the transitive dynamic libraries of a module's imports.
Modules from the same library are loaded individually, while modules
from other libraries are loaded as part of the whole library.
-/
@[inline] private def Module.fetchImportLibs
  (self : Module) (imps : Array Module) (compileSelf : Bool)
: FetchM (Array (Job Dynlib)) :=
  (·.2) <$> self.fetchImportLibsCore imps compileSelf ({}, #[])

/-- Fetch the dynlibs of a list of imports. **For internal use.**  -/
@[inline] def fetchImportLibs
  (mods : Array Module) : FetchM (Job (Array Dynlib))
:= do
  let (_, jobs) ← mods.foldlM (init := ({}, #[])) fun s mod => do
    let imports ← (← mod.imports.fetch).await
    mod.fetchImportLibsCore imports mod.shouldPrecompile s
  let jobs ← mods.foldlM (init := jobs) fun jobs mod => do
    if mod.shouldPrecompile then
      jobs.push <$> mod.dynlib.fetch
    else return jobs
  return Job.collectArray jobs

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
  let importJob := Job.mixArray <| ← directImports.mapM fun imp => do
    if imp.name = mod.name then
      logError s!"{mod.leanFile}: module imports itself"
    imp.olean.fetch
  let impLibsJob ← Job.collectArray <$>
    mod.fetchImportLibs directImports mod.shouldPrecompile
  let externLibsJob ← Job.collectArray <$>
    mod.pkg.externLibs.mapM (·.dynlib.fetch)
  let dynlibsJob ← mod.dynlibs.fetchIn mod.pkg
  let pluginsJob ← mod.plugins.fetchIn mod.pkg

  extraDepJob.bindM fun _ => do
  importJob.bindM (sync := true) fun _ => do
  let depTrace ← takeTrace
  impLibsJob.bindM (sync := true) fun impLibs => do
  externLibsJob.bindM (sync := true) fun externLibs => do
  dynlibsJob.bindM (sync := true) fun dynlibs => do
  pluginsJob.mapM (sync := true) fun plugins => do
    match mod.platformIndependent with
    | none => addTrace depTrace
    | some false => addTrace depTrace; addPlatformTrace
    | some true => setTrace depTrace
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
    addPureTrace mod.leanArgs
    let srcTrace ← computeTrace (TextFilePath.mk mod.leanFile)
    addTrace srcTrace
    let upToDate ← buildUnlessUpToDate? (oldTrace := srcTrace.mtime) mod (← getTrace) mod.traceFile do
      compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile mod.cFile mod.bcFile?
        (← getLeanPath) mod.rootDir dynlibs plugins
        (mod.weakLeanArgs ++ mod.leanArgs) (← getLean)
      mod.clearOutputHashes
    unless upToDate && (← getTrustHash) do
      mod.cacheOutputHashes

/-- The `ModuleFacetConfig` for the builtin `leanArtsFacet`. -/
def Module.leanArtsFacetConfig : ModuleFacetConfig leanArtsFacet :=
  mkFacetJobConfig (·.recBuildLean)

/-- The `ModuleFacetConfig` for the builtin `oleanFacet`. -/
def Module.oleanFacetConfig : ModuleFacetConfig oleanFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      addTrace (← fetchFileTrace mod.oleanFile)
      return mod.oleanFile

/-- The `ModuleFacetConfig` for the builtin `ileanFacet`. -/
def Module.ileanFacetConfig : ModuleFacetConfig ileanFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      addTrace (← fetchFileTrace mod.ileanFile)
      return mod.ileanFile

/-- The `ModuleFacetConfig` for the builtin `cFacet`. -/
def Module.cFacetConfig : ModuleFacetConfig cFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      /-
      Avoid recompiling unchanged C files
      C files are assumed to only depend on their content
      and not transitively on their inputs (e.g., module sources).
      Lean also produces LF-only C files, so no line ending normalization.
      -/
      setTrace (← fetchFileTrace mod.cFile)
      addLeanTrace -- Lean C files include `lean/lean.h`
      return mod.cFile

/-- The `ModuleFacetConfig` for the builtin `bcFacet`. -/
def Module.bcFacetConfig : ModuleFacetConfig bcFacet :=
  mkFacetJobConfig fun mod => do
    (← mod.leanArts.fetch).mapM fun _ => do
      /-
      Avoid recompiling unchanged bitcode files
      Bitcode files are assumed to only depend on their content
      and not transitively on their inputs (e.g., module sources)
      -/
      setTrace (← fetchFileTrace mod.bcFile)
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
  buildLeanO self.coExportFile (← self.c.fetch) self.weakLeancArgs leancArgs

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
  buildLeanO self.coNoExportFile (← self.c.fetch) self.weakLeancArgs self.leancArgs

/-- The `ModuleFacetConfig` for the builtin `coNoExportFacet`. -/
def Module.coNoExportFacetConfig : ModuleFacetConfig coNoExportFacet :=
  mkFacetJobConfig Module.recBuildLeanCToONoExport

/-- The `ModuleFacetConfig` for the builtin `coFacet`. -/
def Module.coFacetConfig : ModuleFacetConfig coFacet :=
  mkFacetJobConfig fun mod =>
    if Platform.isWindows then mod.coNoExport.fetch else mod.coExport.fetch

/-- Recursively build the module's object file from its bitcode file produced by `lean`. -/
def Module.recBuildLeanBcToO (self : Module) : FetchM (Job FilePath) := do
  withRegisterJob s!"{self.name}:bc.o" do
  -- TODO: add option to pass a target triplet for cross compilation
  buildLeanO self.bcoFile (← self.bc.fetch) self.weakLeancArgs self.leancArgs

/-- The `ModuleFacetConfig` for the builtin `bcoFacet`. -/
def Module.bcoFacetConfig : ModuleFacetConfig bcoFacet :=
  mkFacetJobConfig Module.recBuildLeanBcToO

/-- The `ModuleFacetConfig` for the builtin `oExportFacet`. -/
def Module.oExportFacetConfig : ModuleFacetConfig oExportFacet :=
  mkFacetJobConfig fun mod =>
    match mod.backend with
    | .default | .c => mod.coExport.fetch
    | .llvm => mod.bco.fetch

/-- The `ModuleFacetConfig` for the builtin `oNoExportFacet`. -/
def Module.oNoExportFacetConfig : ModuleFacetConfig oNoExportFacet :=
  mkFacetJobConfig fun mod =>
    match mod.backend with
    | .default | .c => mod.coNoExport.fetch
    | .llvm => error "the LLVM backend only supports exporting Lean symbols"

/-- The `ModuleFacetConfig` for the builtin `oFacet`. -/
def Module.oFacetConfig : ModuleFacetConfig oFacet :=
  mkFacetJobConfig fun mod =>
    match mod.backend with
    | .default | .c => mod.co.fetch
    | .llvm => mod.bco.fetch

/--
Recursively build the shared library of a module
(e.g., for `--load-dynlib` or `--plugin`).
-/
def Module.recBuildDynlib (mod : Module) : FetchM (Job Dynlib) :=
  withRegisterJob s!"{mod.name}:dynlib" do
  -- Fetch object files
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
  mkFacetJobConfig Module.recBuildDynlib

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
