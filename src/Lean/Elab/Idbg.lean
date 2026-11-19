/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
public import Lean.Idbg

/-!
# Interactive Debug Expression Evaluator (`idbg`)

Elaborator for `idbg`. The runtime support for compiled programs is in `Lean.Idbg`.
-/

open Lean Lean.Elab Lean.Elab.Term Lean.Meta

namespace Lean.Elab.Do

open Lean.Idbg

@[builtin_doElem_control_info Lean.Parser.Term.doIdbg]
def controlInfoIdbg : ControlInfoHandler := fun _ => return default

/-- Core elaboration logic shared by term and do-element forms.
Elaborates `e`, wraps the result in `toString ∘ repr`, abstracts over all local declarations,
and generates both the server-side TCP exchange and the runtime client loop code. -/
def elabIdbgCore (e : Syntax) (body : TSyntax `term) (ref : Syntax) (expectedType? : Option Expr) :
    TermElabM Expr := do
  let fileName ← IO.FS.realPath (← getFileName)
  let siteId := toString (hash s!"{fileName}:{ref.getPos?.getD 0}")

  -- Collect ALL non-aux local declarations.
  -- We need all of them (not just those used in the current expression)
  -- because the expression can change on the server side while the
  -- compiled program's apply closure is fixed.
  let lctx ← getLCtx
  let mut localDecls : Array LocalDecl := #[]
  for decl in lctx do
    if decl.isAuxDecl then continue
    localDecls := localDecls.push decl
  let localFVars := localDecls.map (mkFVar ·.fvarId)

  -- Elaborate e, wrap in `toString ∘ repr`.
  -- `synthesizeSyntheticMVarsNoPostponing` forces pending instance resolution
  -- so that `instantiateMVars` can fully resolve all metavariables.
  let eExpr ← Term.elabTerm e none
  Term.synthesizeSyntheticMVarsNoPostponing
  let eExpr ← instantiateMVars eExpr
  let reprExpr ← Meta.mkAppM ``repr #[eExpr]
  let reprStrExpr ← Meta.mkAppM ``toString #[reprExpr]
  Term.synthesizeSyntheticMVarsNoPostponing
  let reprStrExpr ← instantiateMVars reprStrExpr

  -- Abstract over ALL locals as lambdas (not lets).
  -- Do-notation let-bindings have `nondep := false`, so `mkLambdaFVars` would
  -- create `letE` for them. We temporarily set `nondep := true` so that
  -- `generalizeNondepLet` (the default) turns them all into lambdas.
  let lctx' := localDecls.foldl (init := ← getLCtx) fun lctx decl =>
    lctx.modifyLocalDecl decl.fvarId (·.setNondep true)
  let (abstractedValue, abstractedType) ← withLCtx' lctx' do
    let abstractedValue ← Meta.mkLambdaFVars localFVars reprStrExpr
    let abstractedType ← Meta.inferType abstractedValue
    return (← instantiateMVars abstractedValue, ← instantiateMVars abstractedType)

  if abstractedValue.hasMVar then
    throwError "idbg: abstracted value still has metavariables"
  if abstractedType.hasMVar then
    throwError "idbg: abstracted type still has metavariables"

  -- Server mode: serialize and serve in a background snapshot task.
  -- Skip if expression contains sorry (partial input during editing).
  if Elab.inServer.get (← getOptions) && !abstractedValue.hasSorry then
    let json := Json.mkObj [
      ("type", exprToJson abstractedType),
      ("value", exprToJson abstractedValue)
    ]
    let cancelTk ← IO.CancelToken.new
    let act ← Core.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun () => do
      if let some result ← idbgServer siteId json then
        logInfoAt ref m!"idbg: {result}"
    Core.logSnapshotTask {
      stx? := some ref
      task := (← BaseIO.asTask (act ()))
      cancelTk? := cancelTk
    }

  -- Generate runtime code: `idbgClientLoop siteId imports apply >>= fun _ => body`
  let siteLit := Syntax.mkStrLit siteId
  let applyClosure ← withLocalDecl `f .default abstractedType fun fVar => do
    let appBody := mkAppN fVar localFVars
    Meta.mkLambdaFVars #[fVar] appBody
  let closureStx ← Term.exprToSyntax applyClosure
  -- Include the current module so the client can access same-file declarations.
  -- The `.olean` should exist since the program was compiled from it.
  let imports := (← getEnv).header.imports.push { module := (← getEnv).mainModule }
  let importExprs ← imports.mapM fun imp => do
    let nameExpr := toExpr imp.module
    let importAllExpr := toExpr imp.importAll
    let isExportedExpr := toExpr imp.isExported
    let isMetaExpr := toExpr imp.isMeta
    return mkAppN (.const ``Import.mk []) #[nameExpr, importAllExpr, isExportedExpr, isMetaExpr]
  let importsExpr := mkApp2 (.const ``List.toArray [.zero])
    (.const ``Import [])
    (importExprs.toList.foldr (fun e acc => mkApp3 (.const ``List.cons [.zero]) (.const ``Import []) e acc)
      (mkApp (.const ``List.nil [.zero]) (.const ``Import [])))
  let importsStx ← Term.exprToSyntax importsExpr
  Term.elabTerm (← `(
    Lean.Idbg.idbgClientLoop $siteLit $importsStx $closureStx >>= fun _ => $body
  )) expectedType?

@[builtin_term_elab Lean.Parser.Term.idbg]
def elabIdbgTerm : TermElab := fun stx expectedType? => do
  let `(Lean.Parser.Term.idbg| idbg $e; $body) := stx | throwUnsupportedSyntax
  elabIdbgCore (e := e) (body := body) (ref := stx) expectedType?

@[builtin_doElem_elab Lean.Parser.Term.doIdbg]
def elabDoIdbg : DoElab := fun stx dec => do
  let `(Lean.Parser.Term.doIdbg| idbg%$tk $e) := stx | throwUnsupportedSyntax
  let mγ ← mkMonadApp (← read).doBlockResultType
  let dec ← dec.ensureUnitAt tk
  doElabToSyntax "idbg body" dec.continueWithUnit fun body => do
    elabIdbgCore (e := e) (body := body) (ref := stx) mγ

end Lean.Elab.Do
