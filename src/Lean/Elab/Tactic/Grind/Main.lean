/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Main
public import Lean.Meta.Tactic.TryThis
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Config
public import Lean.LibrarySuggestions.Basic
import Lean.Meta.Tactic.Grind.SimpUtil
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.EMatchTheoremParam
import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.Grind.Param
import Lean.Meta.Tactic.Grind.Action
import Lean.Elab.Tactic.Grind.Trace
import Lean.Meta.Tactic.Grind.Finish
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.CollectParams
import Lean.Elab.MutualDef
meta import Lean.Meta.Tactic.Grind.Parser
public section
namespace Lean.Elab.Tactic
open Meta
declare_config_elab elabGrindConfig Grind.Config
declare_config_elab elabGrindConfigInteractive Grind.ConfigInteractive
declare_config_elab elabCutsatConfig Grind.CutsatConfig
declare_config_elab elabGrobnerConfig Grind.GrobnerConfig

open Command Term in
open Lean.Parser.Command.GrindCnstr in
@[builtin_command_elab Lean.Parser.Command.grindPattern]
def elabGrindPattern : CommandElab := fun stx => do
  match stx with
  | `(grind_pattern $[[ $attr?:ident ]]? $thmName:ident => $terms,* $[$cnstrs?:grindPatternCnstrs]?) => go attr? thmName terms cnstrs? .global
  | `(scoped grind_pattern $[[ $attr?:ident ]]? $thmName:ident => $terms,* $[$cnstrs?:grindPatternCnstrs]?) => go attr? thmName terms cnstrs? .scoped
  | `(local grind_pattern $[[ $attr?:ident ]]? $thmName:ident => $terms,* $[$cnstrs?:grindPatternCnstrs]?) => go attr? thmName terms cnstrs? .local
  | _ => throwUnsupportedSyntax
where
  findLHS (xs : Array Expr) (lhs : Syntax) : TermElabM (LocalDecl × Nat) := do
    let lhsId := lhs.getId
    let mut i := 0
    for x in xs do
      let xDecl ← x.fvarId!.getDecl
      if xDecl.userName == lhsId then
        return (xDecl, xs.size - i - 1)
      i := i + 1
    throwErrorAt lhs "invalid constraint, `{lhsId}` is not local variable of the theorem"

  elabCnstrRHS (xs : Array Expr) (rhs : Syntax) (expectedType : Expr) : TermElabM Grind.CnstrRHS := do
    /-
    **Note**: We need better sanity checking here.
    We must check whether the type of `rhs` is type correct with respect to
    an arbitrary instantiation of `xs`. That is, we should use meta-variables
    in the check. It is incorrect to use `xDecl.type`. For example, suppose the
    type of `xDecl` is `α → β` where `α` and `β` are variables in `xs` occurring before
    `xDecl`, and `rhsExpr` is `some : ?m → ?m`. The types `α → β =?= ?m → ?m` are
    not definitionally equal, but `?α → ?β =?= ?m → ?m` are.
    -/
    let rhsExpr ← Term.elabTerm rhs expectedType
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let rhsExpr ← instantiateMVars rhsExpr
    if rhsExpr.hasSyntheticSorry then
      throwErrorAt rhs "invalid constraint, rhs contains a synthetic `sorry`"
    let rhsExpr := rhsExpr.eta
    let { paramNames := levelNames, mvars, expr := rhs } ← abstractMVars rhsExpr
    let numMVars := mvars.size
    let rhs := rhs.abstract xs
    return { levelNames, numMVars, expr := rhs }

  elabProp (xs : Array Expr) (term : Syntax) : TermElabM Expr := do
    let e ← Term.elabTermAndSynthesize term (Expr.sort 0)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      throwErrorAt term "invalid proposition, it contains a synthetic `sorry`"
    if e.hasMVar then
      throwErrorAt term "invalid proposition, it contains metavariables{indentExpr e}"
    return e.abstract xs

  elabNotDefEq (xs : Array Expr) (lhs rhs : Syntax) : TermElabM Grind.EMatchTheoremConstraint := do
    let (localDecl, lhsBVarIdx) ← findLHS xs lhs
    let rhs ← elabCnstrRHS xs rhs localDecl.type
    return .notDefEq lhsBVarIdx rhs

  elabDefEq (xs : Array Expr) (lhs rhs : Syntax) : TermElabM Grind.EMatchTheoremConstraint := do
    let (localDecl, lhsBVarIdx) ← findLHS xs lhs
    let rhs ← elabCnstrRHS xs rhs localDecl.type
    return .defEq lhsBVarIdx rhs

  elabCnstrs (xs : Array Expr) (cnstrs? : Option (TSyntax ``Parser.Command.grindPatternCnstrs))
      : TermElabM (List (Grind.EMatchTheoremConstraint)) := do
    let some cnstrs := cnstrs? | return []
    let cnstrs := cnstrs.raw[1].getArgs
    cnstrs.toList.mapM fun cnstr => do
      let kind := cnstr.getKind
      if kind == ``notDefEq then
        elabNotDefEq xs cnstr[0] cnstr[2]
      else if kind == ``defEq then
        elabDefEq xs cnstr[0] cnstr[2]
      else if kind == ``genLt then
        return .genLt cnstr[2].toNat
      else if kind == ``sizeLt then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .sizeLt lhs cnstr[3].toNat
      else if kind == ``depthLt then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .depthLt lhs cnstr[3].toNat
      else if kind == ``maxInsts then
        return .maxInsts cnstr[2].toNat
      else if kind == ``isValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .isValue lhs false
      else if kind == ``isStrictValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .isValue lhs true
      else if kind == ``notValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .notValue lhs false
      else if kind == ``notStrictValue then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .notValue lhs true
      else if kind == ``isGround then
        let (_, lhs) ← findLHS xs cnstr[1]
        return .isGround lhs
      else if kind == ``Parser.Command.GrindCnstr.check then
        return .check (← elabProp xs cnstr[1])
      else if kind == ``Parser.Command.GrindCnstr.guard then
        return .guard (← elabProp xs cnstr[1])
      else
        throwErrorAt cnstr "unexpected constraint"

  go (attrName? : Option (TSyntax `ident)) (thmName : TSyntax `ident) (terms : Syntax.TSepArray `term ",")
      (cnstrs? : Option (TSyntax ``Parser.Command.grindPatternCnstrs))
      (kind : AttributeKind) : CommandElabM Unit := liftTermElabM do
    let attrName := if let some attrName := attrName? then attrName.getId else `grind
    let some ext ← Grind.getExtension? attrName | throwError "unknown `grind` attribute `{attrName}`"
    let declName ← realizeGlobalConstNoOverloadWithInfo thmName
    let info ← getConstVal declName
    forallTelescope info.type fun xs _ => do
      let patterns ← terms.getElems.mapM fun term => do
        let pattern ← Term.elabTerm term none
        synthesizeSyntheticMVarsUsingDefault
        let pattern ← instantiateMVars pattern
        let pattern ← Grind.preprocessPattern pattern
        return pattern.abstract xs
      let cnstrs ← elabCnstrs xs cnstrs?
      ext.addEMatchTheorem declName xs.size patterns.toList .user kind cnstrs (minIndexable := false)

open Command in
@[builtin_command_elab Lean.Parser.resetGrindAttrs]
def elabResetGrindAttrs : CommandElab := fun _ => liftTermElabM do
  -- Remark: we do not reset symbol priorities because we would have to then set
  -- `[grind symbol 0] Eq` after a `reset_grind_attr%` command.
  -- Grind.resetSymbolPrioExt
  modifyEnv fun env => Grind.grindExt.modifyState env fun ext => { ext with casesTypes := {}, inj := {}, ematch := {} }

open Command Term in
@[builtin_command_elab Lean.Parser.Command.initGrindNorm]
def elabInitGrindNorm : CommandElab := fun stx =>
  withExporting do  -- should generate public aux decls
  match stx with
  | `(init_grind_norm $pre:ident* | $post*) =>
    Command.liftTermElabM do
      let pre ← pre.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
      let post ← post.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
      -- Creates `Lean.Grind._simp_1` etc.. As we do not use this command in independent modules,
      -- there is no chance of name conflicts.
      withDeclNameForAuxNaming `Lean.Grind do
        Grind.registerNormTheorems pre post
  | _ => throwUnsupportedSyntax

private def parseModifier (s : String) : CoreM Grind.AttrKind := do
  let stx := Parser.runParserCategory (← getEnv) `Lean.Parser.Attr.grindMod s
  match stx with
  | .ok stx => Grind.getAttrKindCore stx
  | _ => throwError "unexpected modifier {s}"

open LibrarySuggestions in
def elabGrindSuggestions
    (params : Grind.Params) (suggestions : Array Suggestion := #[]) : MetaM Grind.Params := do
  let mut params := params
  let mut added : Array Name := #[]
  for p in suggestions do
    let attr ← match p.flag with
    | some flag => parseModifier flag
    | none => pure <| .ematch (.default false)
    match attr with
    | .ematch kind =>
      try
        params ← addEMatchTheorem params (mkIdent p.name) p.name kind false (warn := false)
        added := added.push p.name
      catch _ => pure () -- Don't worry if library suggestions gave bad theorems.
    | _ =>
      -- We could actually support arbitrary grind modifiers,
      -- and call `processParam` rather than `addEMatchTheorem`,
      -- but this would require a larger refactor.
      -- Let's only do this if there is a prospect of a library suggestion engine supporting this.
      throwError "unexpected modifier {p.flag}"
  unless added.isEmpty do
    trace[grind.debug.suggestions] "{added}"
  return params

/-- Add all definitions from the current file. -/
def elabGrindLocals (params : Grind.Params) : MetaM Grind.Params := do
  let env ← getEnv
  let mut params := params
  let mut added : Array Name := #[]
  for (name, ci) in env.constants.map₂.toList do
    -- Filter similar to LibrarySuggestions.isDeniedPremise (but inlined to avoid dependency)
    -- Skip internal details, but allow private names (which are accessible from current module)
    if name.isInternalDetail && !isPrivateName name then continue
    if (← Meta.isInstance name) then continue
    match ci with
    | .defnInfo _ =>
      try
        params ← addEMatchTheorem params (mkIdent name) name (.default false) false (warn := false)
        added := added.push name
      catch _ => pure ()
    | _ => continue
  unless added.isEmpty do
    trace[grind.debug.locals] "{added}"
  return params

def mkGrindParams
    (config : Grind.Config) (only : Bool) (ps : TSyntaxArray ``Parser.Tactic.grindParam) (mvarId : MVarId) :
    TermElabM Grind.Params := do
  let params ← if only then Grind.mkOnlyParams config else Grind.mkDefaultParams config
  let mut params ← elabGrindParams params ps (lax := config.lax) (only := only)
  if config.suggestions then
    params ← elabGrindSuggestions params (← LibrarySuggestions.select mvarId { caller := some "grind" })
  if config.locals then
    params ← elabGrindLocals params
  trace[grind.debug.inj] "{params.extensions[0]!.inj.getOrigins.map (·.pp)}"
  if params.anchorRefs?.isSome then
    /-
    **Note**: anchors are automatically computed in interactive mode where
    hygiene is turned on. So, we must disable hypotheses id cleanup since
    different ids will affect the anchor values.
    **TODO**: a more robust solution since users may use `grind +clean => finish?`
    -/
    params := { params with config.clean := false }
  return params

def grind
    (mvarId : MVarId) (config : Grind.Config)
    (only : Bool)
    (ps   :  TSyntaxArray ``Parser.Tactic.grindParam)
    (seq? : Option (TSyntax `Lean.Parser.Tactic.Grind.grindSeq))
    : TacticM Unit := do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
    return ()
  mvarId.withContext do
    let params ← mkGrindParams config only ps mvarId
    Grind.withProtectedMCtx config mvarId fun mvarId' => do
      let finalize (result : Grind.Result) : TacticM Unit := do
        if result.hasFailed then
          throwError "`grind` failed\n{← result.toMessageData}"
        return ()
      if let some seq := seq? then
        let (result, _) ← Grind.GrindTacticM.runAtGoal mvarId' params do
          Grind.evalGrindTactic seq
          -- **Note**: We are returning only the first goal that could not be solved.
          let goal? := if let goal :: _ := (← get).goals then some goal else none
          Grind.liftGrindM <| Grind.mkResult params goal?
        finalize result
      else
        let result ← Grind.main mvarId' params
        finalize result

def evalGrindCore
    (ref : Syntax)
    (config : Grind.Config)
    (only : Option Syntax)
    (params? : Option (Syntax.TSepArray `Lean.Parser.Tactic.grindParam ","))
    (seq? : Option (TSyntax `Lean.Parser.Tactic.Grind.grindSeq))
    : TacticM Unit := do
  let only := only.isSome
  let params := if let some params := params? then params.getElems else #[]
  if Grind.grind.warning.get (← getOptions) then
    logWarningAt ref "The `grind` tactic is new and its behavior may change in the future. This project has used `set_option grind.warning true` to discourage its use."
  withMainContext do
    grind (← getMainGoal) config only params seq?
    replaceMainGoal []

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

/-- Filter out `+suggestions` and `+locals` from the config syntax -/
def filterSuggestionsAndLocalsFromGrindConfig (config : TSyntax ``Lean.Parser.Tactic.optConfig) :
    TSyntax ``Lean.Parser.Tactic.optConfig :=
  -- optConfig structure: (Tactic.optConfig [configItem1, configItem2, ...])
  -- config.raw.getArgs returns #[null_node], so we need to filter the null node's children
  let nullNode := config.raw[0]!
  let configItems := nullNode.getArgs
  let filteredItems := configItems.filter fun configItem =>
    -- Keep all items except +suggestions and +locals
    -- Structure: configItem -> posConfigItem -> ["+", ident]
    match configItem[0]? with
    | some posConfigItem => match posConfigItem[1]? with
      | some ident =>
        let id := ident.getId.eraseMacroScopes
        !(posConfigItem.getKind == ``Lean.Parser.Tactic.posConfigItem && (id == `suggestions || id == `locals))
      | none => true
    | none => true
  ⟨config.raw.setArg 0 (nullNode.setArgs filteredItems)⟩

private def elabGrindConfig' (config : TSyntax ``Lean.Parser.Tactic.optConfig) (interactive : Bool) : TacticM Grind.Config := do
  if interactive then
    return (← elabGrindConfigInteractive config).toConfig
  else
    elabGrindConfig config

@[builtin_tactic Lean.Parser.Tactic.grind] def evalGrind : Tactic := fun stx => do
  -- Preserve this import in core; all others import `Init` anyway
  recordExtraModUse (isMeta := false) `Init.Grind.Tactics
  let `(tactic| grind $config:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[=> $seq:grindSeq]?) := stx
    | throwUnsupportedSyntax
  let interactive := seq.isSome
  let config ← elabGrindConfig' config interactive
  evalGrindCore stx config only params seq

def evalGrindTraceCore (stx : Syntax) (trace := true) (verbose := true) (useSorry := true) : TacticM (Array (TSyntax `tactic)) := withMainContext do
  let `(tactic| grind? $configStx:optConfig $[only%$only]?  $[ [$params?:grindParam,*] ]?) := stx
    | throwUnsupportedSyntax
  let config ← elabGrindConfig configStx
  let config := { config with clean := false, trace, verbose, useSorry }
  let only := only.isSome
  let paramStxs := if let some params := params? then params.getElems else #[]
  -- Extract term parameters (non-ident params) to include in the suggestion.
  -- These are not tracked via E-matching, so we conservatively include them all.
  -- Ident params resolve to global declarations and are tracked via E-matching.
  -- Non-ident terms (like `show P by tac`) need to be preserved explicitly.
  let termParamStxs : Array Grind.TParam := paramStxs.filter fun p =>
    match p with
    | `(Parser.Tactic.grindParam| $[$_:grindMod]? $_:ident) => false
    | `(Parser.Tactic.grindParam| ! $[$_:grindMod]? $_:ident) => false
    | `(Parser.Tactic.grindParam| - $_:ident) => false
    | `(Parser.Tactic.grindParam| #$_:hexnum) => false
    | _ => true
  let mvarId ← getMainGoal
  let params ← mkGrindParams config only paramStxs mvarId
  Grind.withProtectedMCtx config mvarId fun mvarId' => do
    let (tacs, _) ← Grind.GrindTacticM.runAtGoal mvarId' params do
      let finish ← Grind.Action.mkFinish
      let goal :: _ ← Grind.getGoals
        | -- Goal was closed during initialization
          let configStx' := filterSuggestionsAndLocalsFromGrindConfig configStx
          if termParamStxs.isEmpty then
            let tac ← `(tactic| grind $configStx':optConfig only)
            return #[tac]
          else
            let tac ← `(tactic| grind $configStx':optConfig only [$termParamStxs,*])
            return #[tac]
      Grind.liftGrindM do
        -- **Note**: If we get failures when using the first suggestion, we should test is using `saved`
        -- let saved ← saveState
        match (← finish.run goal) with
        | .closed seq =>
          let configStx' := filterSuggestionsAndLocalsFromGrindConfig configStx
          let tacs ← Grind.mkGrindOnlyTactics configStx' seq termParamStxs
          let seq := Grind.Action.mkGrindSeq seq
          let tac ← `(tactic| grind $configStx':optConfig => $seq:grindSeq)
          let tacs := tacs.push tac
          return tacs
        | .stuck gs =>
          let goal :: _ := gs | throwError "`grind?` failed, but resulting goal is not available"
          let result ← Grind.mkResult params (some goal)
          throwError "`grind?` failed\n{← result.toMessageData}"
    return tacs

@[builtin_tactic Lean.Parser.Tactic.grindTrace] def evalGrindTrace : Tactic := fun stx => do
  let tacs ← evalGrindTraceCore stx
  if tacs.size == 1 then
    Tactic.TryThis.addSuggestion stx { suggestion := .tsyntax tacs[0]! }
  else
    Tactic.TryThis.addSuggestions stx <| tacs.map fun tac => { suggestion := .tsyntax tac }

@[builtin_tactic Lean.Parser.Tactic.lia] def evalLia : Tactic := fun stx => do
  let `(tactic| lia $config:optConfig) := stx | throwUnsupportedSyntax
  let config ← elabCutsatConfig config
  evalGrindCore stx { config with } none none none

@[builtin_tactic Lean.Parser.Tactic.cutsat] def evalCutsat : Tactic := fun stx => do
  let `(tactic| cutsat $config:optConfig) := stx | throwUnsupportedSyntax
  -- Emit deprecation warning
  logWarning "`cutsat` has been deprecated, use `lia` instead"
  -- Emit a "try this:" suggestion to replace `cutsat` with `lia`
  let liaTac ← `(tactic| lia $config:optConfig)
  Tactic.TryThis.addSuggestion stx { suggestion := .tsyntax liaTac }
  -- Execute the same logic as lia
  let config ← elabCutsatConfig config
  evalGrindCore stx { config with } none none none

@[builtin_tactic Lean.Parser.Tactic.grobner] def evalGrobner : Tactic := fun stx => do
  let `(tactic| grobner $config:optConfig) := stx | throwUnsupportedSyntax
  let config ← elabGrobnerConfig config
  evalGrindCore stx { config with } none none none

end Lean.Elab.Tactic
