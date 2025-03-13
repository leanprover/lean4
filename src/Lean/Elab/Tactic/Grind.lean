/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Tactics
import Lean.Meta.Tactic.Grind
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Config

namespace Lean.Elab.Tactic
open Meta

declare_config_elab elabGrindConfig Grind.Config

open Command Term in
@[builtin_command_elab Lean.Parser.Command.grindPattern]
def elabGrindPattern : CommandElab := fun stx => do
  match stx with
  | `(grind_pattern $thmName:ident => $terms,*) => do
    liftTermElabM do
      let declName ← resolveGlobalConstNoOverload thmName
      discard <| addTermInfo thmName (← mkConstWithLevelParams declName)
      let info ← getConstInfo declName
      forallTelescope info.type fun xs _ => do
        let patterns ← terms.getElems.mapM fun term => do
          let pattern ← elabTerm term none
          synthesizeSyntheticMVarsUsingDefault
          let pattern ← instantiateMVars pattern
          let pattern ← Grind.preprocessPattern pattern
          return pattern.abstract xs
        Grind.addEMatchTheorem declName xs.size patterns.toList .user
  | _ => throwUnsupportedSyntax

open Command in
@[builtin_command_elab Lean.Parser.resetGrindAttrs]
def elabResetGrindAttrs : CommandElab := fun _ => liftTermElabM do
  Grind.resetCasesExt
  Grind.resetEMatchTheoremsExt

open Command Term in
@[builtin_command_elab Lean.Parser.Command.initGrindNorm]
def elabInitGrindNorm : CommandElab := fun stx =>
  match stx with
  | `(init_grind_norm $pre:ident* | $post*) =>
    Command.liftTermElabM do
      let pre ← pre.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
      let post ← post.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
      Grind.registerNormTheorems pre post
  | _ => throwUnsupportedSyntax

def elabGrindParams (params : Grind.Params) (ps :  TSyntaxArray ``Parser.Tactic.grindParam) (only : Bool) : MetaM Grind.Params := do
  let mut params := params
  for p in ps do
    match p with
    | `(Parser.Tactic.grindParam| - $id:ident) =>
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      if let some declName ← Grind.isCasesAttrCandidate? declName false then
        Grind.ensureNotBuiltinCases declName
        params := { params with casesTypes := (← params.casesTypes.eraseDecl declName) }
      else
        params := { params with ematch := (← params.ematch.eraseDecl declName) }
    | `(Parser.Tactic.grindParam| $[$mod?:grindMod]? $id:ident) =>
      let declName ← realizeGlobalConstNoOverloadWithInfo id
      let kind ← if let some mod := mod? then Grind.getAttrKindCore mod else pure .infer
      match kind with
      | .ematch .user =>
        unless only do
          withRef p <| Grind.throwInvalidUsrModifier
        let s ← Grind.getEMatchTheorems
        let thms := s.find (.decl declName)
        let thms := thms.filter fun thm => thm.kind == .user
        if thms.isEmpty then
          throwErrorAt p "invalid use of `usr` modifier, `{declName}` does not have patterns specified with the command `grind_pattern`"
        for thm in thms do
          params := { params with extra := params.extra.push thm }
      | .ematch kind =>
        params ← withRef p <| addEMatchTheorem params declName kind
      | .cases eager =>
        withRef p <| Grind.validateCasesAttr declName eager
        params := { params with casesTypes := params.casesTypes.insert declName eager }
      | .intro =>
        if let some info ← Grind.isCasesAttrPredicateCandidate? declName false then
          for ctor in info.ctors do
            params ← withRef p <| addEMatchTheorem params ctor .default
        else
          throwError "invalid use of `intro` modifier, `{declName}` is not an inductive predicate"
      | .infer =>
        if let some declName ← Grind.isCasesAttrCandidate? declName false then
          params := { params with casesTypes := params.casesTypes.insert declName false }
          if let some info ← isInductivePredicate? declName then
            -- If it is an inductive predicate,
            -- we also add the contructors (intro rules) as E-matching rules
            for ctor in info.ctors do
              params ← withRef p <| addEMatchTheorem params ctor .default
        else
          params ← withRef p <| addEMatchTheorem params declName .default
    | _ => throwError "unexpected `grind` parameter{indentD p}"
  return params
where
  addEMatchTheorem (params : Grind.Params) (declName : Name) (kind : Grind.EMatchTheoremKind) : MetaM Grind.Params := do
    let info ← getConstInfo declName
    match info with
    | .thmInfo _ | .axiomInfo _ | .ctorInfo _ =>
      if kind == .eqBoth then
        let params := { params with extra := params.extra.push (← Grind.mkEMatchTheoremForDecl declName .eqLhs) }
        return { params with extra := params.extra.push (← Grind.mkEMatchTheoremForDecl declName .eqRhs) }
      else
        return { params with extra := params.extra.push (← Grind.mkEMatchTheoremForDecl declName kind) }
    | .defnInfo _ =>
      if (← isReducible declName) then
        throwError "`{declName}` is a reducible definition, `grind` automatically unfolds them"
      if kind != .eqLhs && kind != .default then
        throwError "invalid `grind` parameter, `{declName}` is a definition, the only acceptable (and redundant) modifier is '='"
      let some thms ← Grind.mkEMatchEqTheoremsForDef? declName
        | throwError "failed to genereate equation theorems for `{declName}`"
      return { params with extra := params.extra ++ thms.toPArray' }
    | _ =>
      throwError "invalid `grind` parameter, `{declName}` is not a theorem, definition, or inductive type"

def mkGrindParams (config : Grind.Config) (only : Bool) (ps :  TSyntaxArray ``Parser.Tactic.grindParam) : MetaM Grind.Params := do
  let params ← Grind.mkParams config
  let ematch ← if only then pure {} else Grind.getEMatchTheorems
  let casesTypes ← if only then pure {} else Grind.getCasesTypes
  let params := { params with ematch, casesTypes }
  elabGrindParams params ps only

def grind
    (mvarId : MVarId) (config : Grind.Config)
    (only : Bool)
    (ps   :  TSyntaxArray ``Parser.Tactic.grindParam)
    (mainDeclName : Name) (fallback : Grind.Fallback) : MetaM Grind.Trace := do
  let params ← mkGrindParams config only ps
  let result ← Grind.main mvarId params mainDeclName fallback
  if result.hasFailures then
    throwError "`grind` failed\n{← result.toMessageData}"
  return result.trace

private def elabFallback (fallback? : Option Term) : TermElabM (Grind.GoalM Unit) := do
  let some fallback := fallback? | return (pure ())
  let type := mkApp (mkConst ``Grind.GoalM) (mkConst ``Unit)
  let value ← withLCtx {} {} do Term.elabTermAndSynthesize fallback type
  let auxDeclName ← if let .const declName _ := value then
    pure declName
  else
    let auxDeclName ← Term.mkAuxName `_grind_fallback
    let decl := Declaration.defnDecl {
      name := auxDeclName
      levelParams := []
      type, value, hints := .opaque, safety := .safe
    }
    addAndCompile decl
    pure auxDeclName
  unsafe evalConst (Grind.GoalM Unit) auxDeclName

def evalGrindCore
    (ref : Syntax)
    (config : Grind.Config)
    (only : Option Syntax)
    (params : Option (Syntax.TSepArray `Lean.Parser.Tactic.grindParam ","))
    (fallback? : Option Term)
    : TacticM Grind.Trace := do
  let fallback ← elabFallback fallback?
  let only := only.isSome
  let params := if let some params := params then params.getElems else #[]
  if Grind.grind.warning.get (← getOptions) then
    logWarningAt ref "The `grind` tactic is experimental and still under development. Avoid using it in production projects."
  let declName := (← Term.getDeclName?).getD `_grind
  withMainContext do
    let result ← grind (← getMainGoal) config only params declName fallback
    replaceMainGoal []
    return result

/-- Position for the `[..]` child syntax in the `grind` tactic. -/
def grindParamsPos := 3

/-- Position for the `only` child syntax in the `grind` tactic. -/
def grindOnlyPos := 2

def isGrindOnly (stx : TSyntax `tactic) : Bool :=
  stx.raw.getKind == ``Parser.Tactic.grind && !stx.raw[grindOnlyPos].isNone

def setGrindParams (stx : TSyntax `tactic) (params : Array Syntax) : TSyntax `tactic :=
  if params.isEmpty then
    ⟨stx.raw.setArg grindParamsPos (mkNullNode)⟩
  else
    let paramsStx := #[mkAtom "[", (mkAtom ",").mkSep params, mkAtom "]"]
    ⟨stx.raw.setArg grindParamsPos (mkNullNode paramsStx)⟩

def getGrindParams (stx : TSyntax `tactic) : Array Syntax :=
  stx.raw[grindParamsPos][1].getSepArgs

def mkGrindOnly
    (config : TSyntax ``Lean.Parser.Tactic.optConfig)
    (fallback? : Option Term)
    (trace : Grind.Trace)
    : MetaM (TSyntax `tactic) := do
  let mut params := #[]
  let mut foundFns : NameSet := {}
  for { origin, kind } in trace.thms.toList do
    if let .decl declName := origin then
      unless Match.isMatchEqnTheorem (← getEnv) declName do
        if let some declName ← isEqnThm? declName then
          unless foundFns.contains declName do
            foundFns := foundFns.insert declName
            let decl : Ident := mkIdent (← unresolveNameGlobalAvoidingLocals declName)
            let param ← `(Parser.Tactic.grindParam| $decl:ident)
            params := params.push param
        else
          let decl : Ident := mkIdent (← unresolveNameGlobalAvoidingLocals declName)
          let param ← match kind with
            | .eqLhs     => `(Parser.Tactic.grindParam| = $decl)
            | .eqRhs     => `(Parser.Tactic.grindParam| =_ $decl)
            | .eqBoth    => `(Parser.Tactic.grindParam| _=_ $decl)
            | .eqBwd     => `(Parser.Tactic.grindParam| ←= $decl)
            | .bwd       => `(Parser.Tactic.grindParam| ← $decl)
            | .fwd       => `(Parser.Tactic.grindParam| → $decl)
            | .leftRight => `(Parser.Tactic.grindParam| => $decl)
            | .rightLeft => `(Parser.Tactic.grindParam| <= $decl)
            | .user      => `(Parser.Tactic.grindParam| usr $decl)
            | .default   => `(Parser.Tactic.grindParam| $decl:ident)
          params := params.push param
  for declName in trace.eagerCases.toList do
    unless Grind.isBuiltinEagerCases declName do
      let decl : Ident := mkIdent (← unresolveNameGlobalAvoidingLocals declName)
      let param ← `(Parser.Tactic.grindParam| cases eager $decl)
      params := params.push param
  for declName in trace.cases.toList do
    unless trace.eagerCases.contains declName || Grind.isBuiltinEagerCases declName do
      let decl : Ident := mkIdent (← unresolveNameGlobalAvoidingLocals declName)
      let param ← `(Parser.Tactic.grindParam| cases $decl)
      params := params.push param
  let result ← if let some fallback := fallback? then
    `(tactic| grind $config:optConfig only on_failure $fallback)
  else
    `(tactic| grind $config:optConfig only)
  return setGrindParams result params

@[builtin_tactic Lean.Parser.Tactic.grind] def evalGrind : Tactic := fun stx => do
  match stx with
  | `(tactic| grind $config:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[on_failure $fallback?]?) =>
    let config ← elabGrindConfig config
    discard <| evalGrindCore stx config only params fallback?
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.grindTrace] def evalGrindTrace : Tactic := fun stx => do
  match stx with
  | `(tactic| grind?%$tk $configStx:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[on_failure $fallback?]?) =>
    let config ← elabGrindConfig configStx
    let config := { config with trace := true }
    let trace ← evalGrindCore stx config only params fallback?
    let stx ← mkGrindOnly configStx fallback? trace
    Tactic.TryThis.addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
