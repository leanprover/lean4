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
import Lean.Meta.Tactic.Grind.EMatchTheoremParam
import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.Grind.Param
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
@[builtin_command_elab Lean.Parser.Command.grindPattern]
def elabGrindPattern : CommandElab := fun stx => do
  match stx with
  | `(grind_pattern $thmName:ident => $terms,*) => go thmName terms .global
  | `(scoped grind_pattern $thmName:ident => $terms,*) => go thmName terms .scoped
  | `(local grind_pattern $thmName:ident => $terms,*) => go thmName terms .local
  | _ => throwUnsupportedSyntax
where
  go (thmName : TSyntax `ident) (terms : Syntax.TSepArray `term ",") (kind : AttributeKind) : CommandElabM Unit := liftTermElabM do
    let declName ← realizeGlobalConstNoOverloadWithInfo thmName
    let info ← getConstVal declName
    forallTelescope info.type fun xs _ => do
      let patterns ← terms.getElems.mapM fun term => do
        let pattern ← Term.elabTerm term none
        synthesizeSyntheticMVarsUsingDefault
        let pattern ← instantiateMVars pattern
        let pattern ← Grind.preprocessPattern pattern
        return pattern.abstract xs
      Grind.addEMatchTheorem declName xs.size patterns.toList .user kind (minIndexable := false)

open Command in
@[builtin_command_elab Lean.Parser.resetGrindAttrs]
def elabResetGrindAttrs : CommandElab := fun _ => liftTermElabM do
  Grind.resetCasesExt
  Grind.resetEMatchTheoremsExt
  Grind.resetInjectiveTheoremsExt
  -- Remark: we do not reset symbol priorities because we would have to then set
  -- `[grind symbol 0] Eq` after a `reset_grind_attr%` command.
  -- Grind.resetSymbolPrioExt

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
  for p in suggestions do
    let attr ← match p.flag with
    | some flag => parseModifier flag
    | none => pure <| .ematch (.default false)
    match attr with
    | .ematch kind =>
      try
        params ← addEMatchTheorem params (mkIdent p.name) p.name kind false (warn := false)
      catch _ => pure () -- Don't worry if library suggestions gave bad theorems.
    | _ =>
      -- We could actually support arbitrary grind modifiers,
      -- and call `processParam` rather than `addEMatchTheorem`,
      -- but this would require a larger refactor.
      -- Let's only do this if there is a prospect of a library suggestion engine supporting this.
      throwError "unexpected modifier {p.flag}"
  return params

open LibrarySuggestions in
def elabGrindParamsAndSuggestions
    (params : Grind.Params)
    (ps : TSyntaxArray ``Parser.Tactic.grindParam)
    (suggestions : Array Suggestion := #[])
    (only : Bool) (lax : Bool := false) : MetaM Grind.Params := do
  let params ← elabGrindParams params ps (lax := lax) (only := only)
  elabGrindSuggestions params suggestions

def mkGrindParams
    (config : Grind.Config) (only : Bool) (ps : TSyntaxArray ``Parser.Tactic.grindParam) (mvarId : MVarId) :
    MetaM Grind.Params := do
  let params ← Grind.mkParams config
  let ematch ← if only then pure default else Grind.getEMatchTheorems
  let inj ← if only then pure default else Grind.getInjectiveTheorems
  /-
  **Note**: We used to skip the global cases attribute when `only = true`, but
  this is not very effective. We now use anchors to restrict the set of case-splits.
  -/
  let casesTypes ← Grind.getCasesTypes
  let params := { params with ematch, casesTypes, inj }
  let suggestions ← if config.suggestions then
    LibrarySuggestions.select mvarId
  else
    pure #[]
  let params ← elabGrindParamsAndSuggestions params ps suggestions (only := only) (lax := config.lax)
  trace[grind.debug.inj] "{params.inj.getOrigins.map (·.pp)}"
  return params

def grind
    (mvarId : MVarId) (config : Grind.Config)
    (only : Bool)
    (ps   :  TSyntaxArray ``Parser.Tactic.grindParam)
    (seq? : Option (TSyntax `Lean.Parser.Tactic.Grind.grindSeq))
    : TacticM Grind.Trace := do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
    return {}
  mvarId.withContext do
    let params ← mkGrindParams config only ps mvarId
    let type ← mvarId.getType
    let mvar' ← mkFreshExprSyntheticOpaqueMVar type
    let finalize (result : Grind.Result) : TacticM Grind.Trace := do
      if result.hasFailed then
        throwError "`grind` failed\n{← result.toMessageData}"
      trace[grind.debug.proof] "{← instantiateMVars mvar'}"
      -- `grind` proofs are often big, if `abstractProof` is true, we create an auxiliary theorem.
      let e ← if !config.abstractProof then
        instantiateMVarsProfiling mvar'
      else if (← isProp type) then
        mkAuxTheorem type (← instantiateMVarsProfiling mvar') (zetaDelta := true)
      else
        let auxName ← Term.mkAuxName `grind
        mkAuxDefinition auxName type (← instantiateMVarsProfiling mvar') (zetaDelta := true)
      mvarId.assign e
      return result.trace
    if let some seq := seq? then
      let (result, _) ← Grind.GrindTacticM.runAtGoal mvar'.mvarId! params do
        Grind.evalGrindTactic seq
        -- **Note**: We are returning only the first goal that could not be solved.
        let goal? := if let goal :: _ := (← get).goals then some goal else none
        Grind.liftGrindM <| Grind.mkResult params goal?
      finalize result
    else
      let result ← Grind.main mvar'.mvarId! params
      finalize result

def evalGrindCore
    (ref : Syntax)
    (config : Grind.Config)
    (only : Option Syntax)
    (params? : Option (Syntax.TSepArray `Lean.Parser.Tactic.grindParam ","))
    (seq? : Option (TSyntax `Lean.Parser.Tactic.Grind.grindSeq))
    : TacticM Grind.Trace := do
  let only := only.isSome
  let params := if let some params := params? then params.getElems else #[]
  if Grind.grind.warning.get (← getOptions) then
    logWarningAt ref "The `grind` tactic is new and its behavior may change in the future. This project has used `set_option grind.warning true` to discourage its use."
  withMainContext do
    let result ← grind (← getMainGoal) config only params seq?
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
    (trace : Grind.Trace)
    : MetaM (TSyntax `tactic) := do
  let mut params := #[]
  let mut foundFns : NameSet := {}
  for { origin, kind, minIndexable } in trace.thms.toList do
    if let .decl declName := origin then
      if let some fnName ← isEqnThm? declName then
        unless foundFns.contains fnName do
          foundFns := foundFns.insert fnName
          let param ← Grind.globalDeclToGrindParamSyntax declName kind minIndexable
          params := params.push param
      else
        let param ← Grind.globalDeclToGrindParamSyntax declName kind minIndexable
        params := params.push param
  let result ← `(tactic| grind $config:optConfig only)
  return setGrindParams result params

private def elabGrindConfig' (config : TSyntax ``Lean.Parser.Tactic.optConfig) (interactive : Bool) : TacticM Grind.Config := do
  if interactive then
    return (← elabGrindConfigInteractive config).toConfig
  else
    elabGrindConfig config

@[builtin_tactic Lean.Parser.Tactic.grind] def evalGrind : Tactic := fun stx => do
  -- Preserve this import in core; all others import `Init` anyway
  recordExtraModUse (isMeta := false) `Init.Grind.Tactics
  match stx with
  | `(tactic| grind $config:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[=> $seq:grindSeq]?) =>
    let interactive := seq.isSome
    let config ← elabGrindConfig' config interactive
    discard <| evalGrindCore stx config only params seq
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.grindTrace] def evalGrindTrace : Tactic := fun stx => do
  match stx with
  | `(tactic| grind?%$tk $configStx:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]?) =>
    let config ← elabGrindConfig configStx
    let config := { config with trace := true }
    let trace ← evalGrindCore stx config only params none
    let stx ← mkGrindOnly configStx trace
    Tactic.TryThis.addSuggestion tk stx (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.cutsat] def evalCutsat : Tactic := fun stx => do
  match stx with
  | `(tactic| cutsat $config:optConfig) =>
    let config ← elabCutsatConfig config
    discard <| evalGrindCore stx { config with } none none none
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.grobner] def evalGrobner : Tactic := fun stx => do
  match stx with
  | `(tactic| grobner $config:optConfig) =>
    let config ← elabGrobnerConfig config
    discard <| evalGrindCore stx { config with } none none none
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
