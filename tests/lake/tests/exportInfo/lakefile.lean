module

import Lake
open Lake DSL

/-!
Regression tests for #14612. Export computations must capture their metadata jobs
before their artifact continuation runs and wait for pending metadata through the
job graph, preserving dependency failures and cancellation. Promises reproduce
pending and replaced build-store entries without depending on a particular
thread interleaving.
-/

package test
lean_lib Test

def storeJob (info : BuildInfo) [FamilyOut BuildData info.key α] (job : Job α) : FetchM Unit := do
  let job : Job (BuildData info.key) := cast (by simp) job
  modifyThe BuildStore (·.insert info.key job)

script probe args do
  let testMeta := args.contains "meta"
  let testInput := args.contains "input"
  let replace := args.contains "replace"
  let fail := args.contains "fail"
  let cancel := args.contains "cancel"
  let input : ModuleInput := {
    path := "Test.lean", header := {isModule := false, imports := #[]}, imports := #[]
    trace := .ofHash (pureHash "source") "source"
  }
  let importInfo : ModuleImportInfo := {(default : ModuleImportInfo) with
    transTrace := .ofHash (pureHash "imports") "imports"
    metaTransTrace := .ofHash (pureHash "meta imports") "meta imports"
  }
  let arts : ModuleOutputArtifacts := {
    isModule := false
    olean := {(default : Artifact) with path := "Test.olean", hash := pureHash "olean"}
    ilean := default
  }
  let inputPromise ← IO.Promise.new (α := JobResult ModuleInput)
  let importPromise ← IO.Promise.new (α := JobResult ModuleImportInfo)
  let artsPromise ← IO.Promise.new (α := JobResult ModuleOutputArtifacts)
  let inputJob : Job ModuleInput := .ofTask inputPromise.result!
  let importJob : Job ModuleImportInfo := .ofTask importPromise.result!
  let artsJob : Job ModuleOutputArtifacts := .ofTask artsPromise.result!
  let info? ← runBuild do
    let some mod ← findModule? `Test | error "missing Test"
    storeJob mod.input <|
      if testInput && !replace then inputJob else Job.pure input
    storeJob mod.importInfo <|
      if !testInput && !replace then importJob else Job.pure importInfo
    let job ← if testMeta then do
      storeJob mod.irArts artsJob
      storeJob mod.exportInfo <|
        Job.pure {(default : ModuleExportInfo) with srcTrace := input.trace}
      (← mod.metaExportInfo.fetch).mapM (sync := true) fun info => do
        unless info.metaTransTrace.hash == importInfo.metaTransTrace.hash do
          error "incorrect transitive meta import trace"
        return info.toModuleExportInfo
    else do
      storeJob mod.elabArts artsJob
      mod.exportInfo.fetch
    if replace then
      if testInput then
        storeJob mod.input inputJob
      else
        storeJob mod.importInfo importJob
    artsPromise.resolve (.ok arts {})
    unless replace do
      if ← IO.hasFinished job.task then
        error "export completed before its metadata"
    let failure : JobState :=
      if cancel then {canceled := true} else {log := Log.empty.push (.error "metadata failed")}
    let failed := fail || cancel
    let replacementTrace := BuildTrace.ofHash (pureHash "replacement") "replacement"
    let laterInput := if replace then {input with trace := replacementTrace} else input
    let laterImports := if replace then {importInfo with transTrace := replacementTrace} else importInfo
    inputPromise.resolve <| if failed && testInput then .error 0 failure else .ok laterInput {}
    importPromise.resolve <| if failed && !testInput then .error 0 failure else .ok laterImports {}
    if cancel then
      let result ← job.wait
      unless result.isCanceled && result.state.log.isEmpty do
        error "metadata cancellation was not propagated"
      pure (Job.pure none)
    else
      return (← registerJob "export metadata" job).map (sync := true) some
  if let some info := info? then
    unless info.srcTrace.hash == input.trace.hash do
      error "incorrect source trace"
    unless info.transTrace.hash == importInfo.transTrace.hash do
      error "incorrect transitive import trace"
  IO.println "export metadata checked"
  return 0
