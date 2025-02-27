import Lean
import Lean.Compiler.LCNF.Probing
open Lean.Compiler.LCNF

-- Note: 2024-05-15: At the time of adding #guard_msgs here, the tests seem to all be failing.

-- Find functions that have jps which take a lambda
/-- info: #["Lean.«_aux_Init_NotationExtra___macroRules_Lean_command__Unif_hint____Where_|_-⊢__1»",
  "_private.Lean.MetavarContext.0.Lean.MetavarContext.MkBinding.elimMVar",
  "Array.foldlMUnsafe.fold._at_._private.Lean.Data.PersistentArray.0.Lean.PersistentArray.foldlMAux._at_._private.Lean.Data.PersistentArray.0.Lean.PersistentArray.foldlFromMAux._at_.Lean.PersistentArray.foldlM._at_.Lean.LocalContext.foldlM._at_.Lean.MetavarContext.MkBinding.collectForwardDeps.spec_2.spec_2.spec_2.spec_2.spec_3._redArg",
  "Lean.MessageData.formatAux", "Lean.Xml.Parser.content",
  "Lean.withTraceNode._at_.Lean.Core.wrapAsyncAsSnapshot.spec_25._redArg",
  "IO.FS.withIsolatedStreams._at_.Lean.Core.wrapAsyncAsSnapshot.spec_33._redArg",
  "Lean.withTraceNode._at_.Lean.Meta.processPostponed.spec_0._redArg", "Lean.Meta.withRestoreOrSaveFull._redArg",
  "_private.Lean.Compiler.ExternAttr.0.Lean.syntaxToExternAttrData", "Lean.IR.EmitC.emitDeclAux",
  "_private.Lean.Meta.WHNF.0.Lean.Meta.toCtorWhenK", "_private.Lean.Meta.DiscrTree.0.Lean.Meta.DiscrTree.pushArgs",
  "Lean.Compiler.LCNF.Simp.inlineApp?", "Lean.Compiler.LCNF.Simp.simp._lam_1",
  "Std.Range.forIn'.loop._at_.Lean.Compiler.LCNF.saveSpecParamInfo.spec_20._redArg",
  "Std.Range.forIn'.loop._at_.Std.Range.forIn'.loop._at_.Lean.Compiler.LCNF.saveSpecParamInfo.spec_20.spec_20._redArg",
  "Lean.Compiler.LCNF.Decl.reduceArity", "Lean.withTraceNode._at_.Lean.Compiler.LCNF.PassManager.run.spec_0._redArg",
  "Lean.Parser.Tactic.Doc.initFn._lam_2._@.Lean.Parser.Tactic.Doc._hyg.1042",
  "Lean.withTraceNode._at_.Lean.withTraceNode'._at_.Lean.Meta.SynthInstance.newSubgoal.spec_1.spec_1._redArg",
  "Lean.Elab.Term.isLetRecAuxMVar", "Lean.withTraceNode._at_.Lean.Elab.Term.mkCoe.spec_1._redArg",
  "Lean.PrettyPrinter.Delaborator.delabOfScientific._lam_1",
  "_private.Lean.PrettyPrinter.Delaborator.Builtins.0.Lean.PrettyPrinter.Delaborator.delabForallBinders",
  "Lean.PrettyPrinter.Delaborator.delabLetFun._lam_1", "Lean.PrettyPrinter.Delaborator.delabAppExplicitCore._lam_1",
  "Lean.PrettyPrinter.Delaborator.delabAppImplicitCore", "Lean.Elab.Tactic.withRestoreOrSaveFull._redArg",
  "Lean.withTraceNode._at_.Lean.Elab.Tactic.evalTactic.spec_0._redArg",
  "_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.resumePostponed._lam_1", "Lean.Elab.Command.elabCommandTopLevel",
  "IO.FS.withIsolatedStreams._at_.Lean.Elab.Command.wrapAsyncAsSnapshot.spec_9._redArg",
  "Lean.withTraceNode._at_.Lean.Elab.Command.runLinters.spec_9._redArg", "Lean.Elab.Term.ElabElim.finalize",
  "_private.Lean.Elab.App.0.Lean.Elab.Term.elabAppFn", "_private.Lean.Elab.App.0.Lean.Elab.Term.ElabAppArgs.finalize",
  "_private.Lean.Elab.App.0.Lean.Elab.Term.resolveDotName.go", "Lean.Elab.Command.elabSyntax",
  "Lean.Meta.mkCongrSimpCore?.mk?.go", "Lean.Linter.MissingDocs.initFn._lam_2._@.Lean.Linter.MissingDocs._hyg.1276",
  "Lean.Elab.elabTerminationHints._at_._private.Lean.Elab.LetRec.0.Lean.Elab.Term.mkLetRecDeclView.spec_4",
  "Lean.Elab.elabTerminationHints._at_._private.Lean.Elab.LetRec.0.Lean.Elab.Term.mkLetRecDeclView.spec_4._lam_5",
  "Lean.Language.SnapshotTree.trace.go", "Lean.Language.Lean.process.doElab", "Lean.Language.Lean.processCommands",
  "IO.FS.withIsolatedStreams._at_.Lean.Language.Lean.process.doElab.spec_0._redArg",
  "Lean.Language.Lean.process.parseCmd",
  "Array.mapMUnsafe.map._at_.Array.mapMUnsafe.map._at_.Lean.Firefox.Profile.export.spec_15.spec_15",
  "Array.mapMUnsafe.map._at_.Lean.Firefox.Profile.export.spec_15", ⋯]
-/
#guard_msgs in
#eval
  Probe.runGlobally (phase := .mono) <|
  Probe.filterByJp (·.params.anyM (fun param => return param.type.isForall)) >=>
  Probe.declNames >=>
  Probe.toString

-- Count lambda lifted functions
def lambdaCounter : Probe Decl Nat :=
  Probe.filter (fun decl =>
    if let .str _ val := decl.name then
      return val.startsWith "_lam"
    else
      return false) >=>
  Probe.declNames >=>
  Probe.count

-- Run everywhere
#eval do
  let probeResult ← Probe.runGlobally (phase := .mono) <| lambdaCounter
  let #[numLiftedFunctions] := probeResult | panic! "unexpected probe result"
  assert! numLiftedFunctions ≥ 7000

-- Run limited
/-- info: #[19] -/
#guard_msgs in
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  lambdaCounter

-- Find most commonly used function with threshold
/-- info: #[("USize.ofNat", 111), ("EStateM.Result.ok", 145)] -/
#guard_msgs in
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  Probe.getLetValues >=>
  Probe.filter (fun e => return e matches .const ..) >=>
  Probe.map (fun | .const declName .. => return s!"{declName}" | _ => unreachable!) >=>
  Probe.countUniqueSorted >=>
  Probe.filter (fun (_, count) => return count > 100)
