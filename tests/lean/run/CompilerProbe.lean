import Lean
import Lean.Compiler.LCNF.Probing
open Lean.Compiler.LCNF

-- Note: 2024-05-15: At the time of adding #guard_msgs here, the tests seem to all be failing.

-- Find functions that have jps which take a lambda
/-- info: #["_private.Lean.MetavarContext.0.Lean.MetavarContext.MkBinding.elimMVar",
  "Array.foldlMUnsafe.fold._at_._private.Lean.Data.PersistentArray.0.Lean.PersistentArray.foldlMAux._at_._private.Lean.Data.PersistentArray.0.Lean.PersistentArray.foldlFromMAux._at_.Lean.PersistentArray.foldlM._at_.Lean.LocalContext.foldlM._at_.Lean.MetavarContext.MkBinding.collectForwardDeps.spec_3.spec_3.spec_3.spec_3.spec_4._redArg",
  "Lean.MessageData.formatAux",
  "_private.Lean.Data.Lsp.Diagnostics.0.Lean.Lsp.DiagnosticWith.ordUserVisible._redArg._@.Lean.Data.Lsp.Diagnostics._hyg.2056",
  "IO.FS.withIsolatedStreams._at_.Lean.Core.wrapAsyncAsSnapshot.spec_28._redArg",
  "IO.FS.withIsolatedStreams._at_.Lean.Meta.realizeConst.realizeAndReport.spec_10._redArg",
  "Lean.Meta.withRestoreOrSaveFull._redArg", "Lean.addDecl", "Lean.IR.EmitC.emitDeclAux",
  "Lean.computeStructureResolutionOrder.selectParent._redArg._lam_6",
  "Lean.computeStructureResolutionOrder._redArg._lam_16", "Lean.Meta.evalNat",
  "_private.Lean.Meta.WHNF.0.Lean.Meta.toCtorWhenK", "Lean.IR.ToIR.lowerLetValue",
  "Lean.Compiler.LCNF.toMonoType.visitApp", "Lean.Compiler.LCNF.Simp.inlineApp?", "Lean.Compiler.LCNF.Simp.simp",
  "Lean.Compiler.LCNF.Specialize.specializeApp?", "Lean.Compiler.LCNF.Decl.reduceArity",
  "Lean.Compiler.LCNF.UnreachableBranches.Value.getLiteral.go", "Lean.Parser.registerBuiltinParserAttribute",
  "Lean.Elab.elabTerminationHints._redArg._lam_3", "Lean.Elab.Term.isLetRecAuxMVar",
  "Lean.Elab.mkDeclName._at_.Lean.Elab.expandDeclId._at_.Lean.Elab.Term.expandDeclId.spec_0.spec_1._lam_3",
  "_private.Lean.PrettyPrinter.Delaborator.Builtins.0.Lean.PrettyPrinter.Delaborator.delabForallBinders",
  "Lean.PrettyPrinter.Delaborator.delabAppExplicitCore._lam_2", "Lean.PrettyPrinter.Delaborator.delabLetFun._lam_1",
  "Lean.PrettyPrinter.Delaborator.delabAppImplicitCore", "Lean.Elab.Tactic.withRestoreOrSaveFull._redArg",
  "Lean.Elab.Tactic.evalTactic.expandEval._lam_2",
  "Lean.Elab.Term.withNarrowedTacticReuse._at_.Lean.Elab.Term.withNarrowedArgTacticReuse._at_.Lean.Elab.Term.runTactic.spec_9.spec_9._redArg",
  "_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.resumePostponed._lam_1",
  "Lean.Elab.Command.elabCommandTopLevel._lam_3",
  "IO.FS.withIsolatedStreams._at_.Lean.Elab.Command.wrapAsyncAsSnapshot.spec_9._redArg",
  "Lean.Elab.Term.ElabElim.finalize", "_private.Lean.Elab.App.0.Lean.Elab.Term.ElabAppArgs.finalize",
  "_private.Lean.Elab.App.0.Lean.Elab.Term.resolveDotName.go", "Lean.Elab.Command.elabSyntax",
  "Lean.Meta.mkCongrSimpCore?.mk?.go", "Lean.Linter.MissingDocs.initFn._lam_2._@.Lean.Linter.MissingDocs._hyg.802",
  "Lean.Elab.elabTerminationHints._at_._private.Lean.Elab.LetRec.0.Lean.Elab.Term.mkLetRecDeclView.spec_4._lam_2",
  "Lean.Language.Lean.process.doElab", "Lean.Language.Lean.processCommands",
  "IO.FS.withIsolatedStreams._at_.Lean.Language.Lean.process.doElab.spec_0._redArg",
  "Lean.Language.Lean.process.parseCmd", "Lean.Elab.Term.elabSubst._lam_6",
  "Lean.Meta.Simp.Arith.Nat.ToLinear.toLinearExpr",
  "Array.forIn'Unsafe.loop._at_.Array.forIn'Unsafe.loop._at_.Lean.Meta.Simp.trySimpCongrTheorem?.spec_0.spec_0",
  "Lean.Meta.Simp.simpForall", "Array.forIn'Unsafe.loop._at_.Lean.Meta.Simp.trySimpCongrTheorem?.spec_0", ⋯]
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
/-- info: #[18] -/
#guard_msgs in
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  lambdaCounter

-- Find most commonly used function with threshold
/-- info: #[("USize.ofNat", 111), ("EStateM.Result.ok", 141)] -/
#guard_msgs in
#eval
  Probe.runOnModule `Lean.Compiler.LCNF.JoinPoints (phase := .mono) <|
  Probe.getLetValues >=>
  Probe.filter (fun e => return e matches .const ..) >=>
  Probe.map (fun | .const declName .. => return s!"{declName}" | _ => unreachable!) >=>
  Probe.countUniqueSorted >=>
  Probe.filter (fun (_, count) => return count > 100)
