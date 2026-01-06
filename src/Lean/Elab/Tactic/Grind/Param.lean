/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.Tactic.Grind.Main
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.ForallProp
import Lean.Meta.Tactic.Grind.Main
import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.Grind.Anchor
import Lean.Elab.SyntheticMVars
namespace Lean.Elab.Tactic
open Meta

/-!
`grind` parameter elaboration
-/

def _root_.Lean.Meta.Grind.Params.insertCasesTypes (params : Grind.Params) (declName : Name) (eager : Bool) : Grind.Params :=
  { params with extensions := params.extensions.modify 0 fun ext => { ext with casesTypes := ext.casesTypes.insert declName eager } }

def _root_.Lean.Meta.Grind.Params.eraseCasesTypes (params : Grind.Params) (declName : Name) : CoreM Grind.Params := do
  unless params.extensions.any fun ext => ext.casesTypes.contains declName do
    Grind.throwNotMarkedWithGrindAttribute declName
  return { params with extensions := params.extensions.modify 0 fun ext => { ext with casesTypes := ext.casesTypes.erase declName } }

def _root_.Lean.Meta.Grind.Params.insertFunCC (params : Grind.Params) (declName : Name) : Grind.Params :=
  { params with extensions := params.extensions.modify 0 fun ext => { ext with funCC := ext.funCC.insert declName } }

def _root_.Lean.Meta.Grind.Params.containsEMatch (params : Grind.Params) (declName : Name) : Bool :=
  params.extensions.any fun ext => ext.ematch.contains (.decl declName)

def _root_.Lean.Meta.Grind.Params.isInjectiveTheorem (params : Grind.Params) (declName : Name) : Bool :=
  params.extensions.any fun ext => ext.inj.contains (.decl declName)

def _root_.Lean.Meta.Grind.Params.eraseEMatchCore (params : Grind.Params) (declName : Name) : Grind.Params :=
  { params with extensions := params.extensions.modify 0 fun ext => { ext with ematch := ext.ematch.erase (.decl declName) } }

def _root_.Lean.Meta.Grind.Params.eraseEMatch (params : Grind.Params) (declName : Name) : MetaM Grind.Params := do
  if !wasOriginallyTheorem (← getEnv) declName then
    if let some eqns ← getEqnsFor? declName then
      unless eqns.all fun eqn => params.containsEMatch eqn do
        Grind.throwNotMarkedWithGrindAttribute declName
      return eqns.foldl (init := params) fun params eqn => params.eraseEMatchCore eqn
    else
      Grind.throwNotMarkedWithGrindAttribute declName
  else
    unless params.containsEMatch declName do
      Grind.throwNotMarkedWithGrindAttribute declName
    return params.eraseEMatchCore declName

def _root_.Lean.Meta.Grind.Params.eraseInj (params : Grind.Params) (declName : Name) : Grind.Params :=
  { params with extensions := params.extensions.modify 0 fun ext => { ext with inj := ext.inj.erase (.decl declName) } }

def _root_.Lean.Meta.Grind.ExtensionStateArray.getKindsFor (s : Grind.ExtensionStateArray) (origin : Grind.Origin) : List Grind.EMatchTheoremKind := Id.run do
  let mut result := []
  for ext in s do
    let s : Grind.EMatchTheorems := ext.ematch
    let ks := s.getKindsFor origin
    unless ks.isEmpty do
      result := result ++ ks
  return result

public def _root_.Lean.Meta.Grind.ExtensionStateArray.find (s : Grind.ExtensionStateArray) (origin : Grind.Origin) : List Grind.EMatchTheorem := Id.run do
  let mut r := []
  for h : i in *...s.size do
    let thms := s[i].ematch.find origin
    unless thms.isEmpty do
      r := r ++ thms
  return r

def warnRedundantEMatchArg (s : Grind.ExtensionStateArray) (declName : Name) : MetaM Unit := do
  let minIndexable := false -- TODO: infer it
  let kinds ← match s.getKindsFor (.decl declName) with
    | [] => return ()
    | [k] => pure m!"@{k.toAttribute minIndexable}"
    | [.eqLhs gen, .eqRhs _]
    | [.eqRhs gen, .eqLhs _] => pure m!"@{(Grind.EMatchTheoremKind.eqBoth gen).toAttribute minIndexable}"
    | ks =>
      let ks := ks.map fun k => m!"@{k.toAttribute minIndexable}"
      pure m!"{ks}"
  logWarning m!"this parameter is redundant, environment already contains `{declName}` annotated with `{kinds}`"

def parseModifier (s : String) : CoreM Grind.AttrKind := do
  let stx := Parser.runParserCategory (← getEnv) `Lean.Parser.Attr.grindMod s
  match stx with
  | .ok stx => Grind.getAttrKindCore stx
  | _ => throwError "unexpected modifier {s}"

def ensureNoMinIndexable (minIndexable : Bool) : MetaM Unit := do
  if minIndexable then
    throwError "redundant modifier `!` in `grind` parameter"

public def addEMatchTheorem (params : Grind.Params) (id : Ident) (declName : Name)
    (kind : Grind.EMatchTheoremKind)
    (minIndexable : Bool) (suggest : Bool := false) (warn := true) : MetaM Grind.Params := do
  let info ← getAsyncConstInfo declName
  match info.kind with
  | .thm | .axiom | .ctor =>
    match kind with
    | .eqBoth gen =>
      ensureNoMinIndexable minIndexable
      let thm₁ ← Grind.mkEMatchTheoremForDecl declName (.eqLhs gen) params.symPrios
      let thm₂ ← Grind.mkEMatchTheoremForDecl declName (.eqRhs gen) params.symPrios
      if warn &&
          params.extensions.containsWithSamePatterns thm₁.origin thm₁.patterns thm₁.cnstrs &&
          params.extensions.containsWithSamePatterns thm₂.origin thm₂.patterns thm₂.cnstrs then
        warnRedundantEMatchArg params.extensions declName
      return { params with extra := params.extra.push thm₁ |>.push thm₂ }
    | _ =>
      if kind matches .eqLhs _ | .eqRhs _ then
        ensureNoMinIndexable minIndexable
      let thm ← if suggest && !Grind.backward.grind.inferPattern.get (← getOptions) then
        Grind.mkEMatchTheoremAndSuggest id declName params.symPrios minIndexable (isParam := true)
      else
        Grind.mkEMatchTheoremForDecl declName kind params.symPrios (minIndexable := minIndexable)
      if warn && params.extensions.containsWithSamePatterns thm.origin thm.patterns thm.cnstrs then
        warnRedundantEMatchArg params.extensions declName
      return { params with extra := params.extra.push thm }
  | .defn =>
    if (← isReducible declName) then
      throwError "`{.ofConstName declName}` is a reducible definition, `grind` automatically unfolds them"
    if !kind.isEqLhs && !kind.isDefault then
      throwError "invalid `grind` parameter, `{.ofConstName declName}` is a definition, the only acceptable (and redundant) modifier is '='"
    ensureNoMinIndexable minIndexable
    let some thms ← Grind.mkEMatchEqTheoremsForDef? declName
      | throwError "failed to generate equation theorems for `{.ofConstName declName}`"
    return { params with extra := params.extra ++ thms.toPArray' }
  | _ =>
    throwError "invalid `grind` parameter, `{.ofConstName declName}` is not a theorem, definition, or inductive type"

def processAnchor (params : Grind.Params) (val : TSyntax `hexnum) : CoreM Grind.Params := do
  let anchorRefs := params.anchorRefs?.getD #[]
  let anchorRef ← Grind.elabAnchorRef val
  return { params with anchorRefs? := some <| anchorRefs.push anchorRef }

def checkNoRevert (params : Grind.Params) : CoreM Unit := do
  if params.config.revert then
    throwError "invalid `grind` parameter, only global declarations are allowed when `+revert` is used"

def processTermParam (params : Grind.Params)
    (p : TSyntax `Lean.Parser.Tactic.grindParam)
    (mod? : Option (TSyntax `Lean.Parser.Attr.grindMod))
    (term : Term)
    (minIndexable : Bool)
    : TermElabM Grind.Params := withRef p do
  checkNoRevert params
  let kind ← if let some mod := mod? then Grind.getAttrKindCore mod else pure .infer
  let kind ← match kind with
    | .ematch .user | .cases _ | .intro | .inj | .ext | .symbol _ | .funCC | .norm .. | .unfold =>
      throwError "invalid `grind` parameter, only global declarations are allowed with this kind of modifier"
    | .ematch kind => pure kind
    | .infer => pure <| .default false
  let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef p do
    let e ← Term.elabTerm term .none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      return .none
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return some (r.paramNames, r.expr)
    else
      return some (#[], e)
  let some (levelParams, proof) := thm? | return params
  let type ← inferType proof
  unless (← isProp type) do
    throwError "invalid `grind` parameter, proof term expected"
  if type.isForall then
    let mkThm (kind : Grind.EMatchTheoremKind) (idx : Nat) : MetaM Grind.EMatchTheorem := do
      let id := ((`extra).appendIndexAfter idx)
      let some thm ← Grind.mkEMatchTheoremWithKind? (.stx id p) levelParams proof kind params.symPrios (minIndexable := minIndexable)
        | throwError "invalid `grind` parameter, failed to infer patterns"
      return thm
    let idx := params.extra.size
    match kind with
    | .eqBoth gen =>
      ensureNoMinIndexable minIndexable
      return { params with extra := params.extra.push (← mkThm (.eqLhs gen) idx) |>.push (← mkThm (.eqRhs gen) idx) }
    | _ =>
      if kind matches .eqLhs _ | .eqRhs _ then
        ensureNoMinIndexable minIndexable
      return { params with extra := params.extra.push (← mkThm kind idx) }
  else
    unless mod?.isNone do
      throwError "invalid `grind` parameter, modifier is redundant since the parameter type is not a `forall`{indentExpr type}"
    unless levelParams.isEmpty do
      throwError "invalid `grind` parameter, parameter type is not a `forall` and is universe polymorphic{indentExpr type}"
    return { params with extraFacts := params.extraFacts.push proof }

def processParam (params : Grind.Params)
    (p : TSyntax `Lean.Parser.Tactic.grindParam)
    (mod? : Option (TSyntax `Lean.Parser.Attr.grindMod))
    (id : TSyntax `ident)
    (minIndexable : Bool)
    (only : Bool)
    (incremental : Bool)
    : TermElabM Grind.Params := do
  let mut params := params
  let declName ← try
    realizeGlobalConstNoOverloadWithInfo id
  catch err =>
    if (← resolveLocalName id.getId).isSome then
      throwErrorAt id "redundant parameter `{id}`, `grind` uses local hypotheses automatically"
    else if let some ext ← Grind.getExtension? id.getId then
      if let some mod := mod? then
        throwErrorAt mod "invalid use of modifier in `grind` attribute `{id.getId}`"
      return { params with extensions := params.extensions.push (ext.getState (← getEnv)) }
    else if !id.getId.getPrefix.isAnonymous then
      -- Fall back to term elaboration for compound identifiers like `foo.le` (dot notation on declarations)
      return (← processTermParam params p mod? id minIndexable)
    else
      throw err
  Linter.checkDeprecated declName
  let kind ← if let some mod := mod? then Grind.getAttrKindCore mod else pure .infer
  match kind with
  | .ematch .user =>
    unless only do
      withRef p <| Grind.throwInvalidUsrModifier
    ensureNoMinIndexable minIndexable
    -- **Note**: This check is hard-coded to the default `grind` attribute. Possible improvement: `usr` modifier that specifies the attribute where
    -- the user pattern is coming from.
    let thms := (← Grind.grindExt.getEMatchTheorems).find (.decl declName)
    let thms := thms.filter fun thm => thm.kind == .user
    if thms.isEmpty then
      throwErrorAt p "invalid use of `usr` modifier, `{.ofConstName declName}` does not have patterns specified with the command `grind_pattern`"
    for thm in thms do
      params := { params with extra := params.extra.push thm }
  | .ematch kind =>
    params ← withRef p <| addEMatchTheorem params id declName kind minIndexable
  | .cases eager =>
    if incremental then throwError "`cases` parameter are not supported here"
    ensureNoMinIndexable minIndexable
    withRef p <| Grind.validateCasesAttr declName eager
    params := params.insertCasesTypes declName eager
  | .intro =>
    if let some info ← Grind.isCasesAttrPredicateCandidate? declName false then
      if incremental then throwError "`cases` parameter are not supported here"
      for ctor in info.ctors do
        params ← withRef p <| addEMatchTheorem params id ctor (.default false) minIndexable
    else
      throwError "invalid use of `intro` modifier, `{.ofConstName declName}` is not an inductive predicate"
  | .inj =>
    let thm ← Grind.mkInjectiveTheorem declName
    params := { params with extraInj := params.extraInj.push thm }
  | .ext =>
    throwError "`[grind ext]` cannot be set using parameters"
  | .infer =>
    if let some declName ← Grind.isCasesAttrCandidate? declName false then
      params := params.insertCasesTypes declName false
      if let some info ← isInductivePredicate? declName then
        -- If it is an inductive predicate,
        -- we also add the constructors (intro rules) as E-matching rules
        for ctor in info.ctors do
          -- **Note**: We should not warn if `declName` is an inductive
          params ← withRef p <| addEMatchTheorem params id ctor (.default false) minIndexable (warn := False)
    else
      params ← withRef p <| addEMatchTheorem params id declName (.default false) minIndexable (suggest := true)
  | .symbol prio =>
    ensureNoMinIndexable minIndexable
    params := { params with symPrios := params.symPrios.insert declName prio }
  | .funCC =>
    params := params.insertFunCC declName
  | .norm .. => throwError "normalization theorems should be registered using the `@[grind norm]` attribute"
  | .unfold => throwError "declarations to be unfolded during normalization should be registered using the `@[grind unfold]` attribute"
  return params

/--
Elaborates `grind` parameters.
`incremental = true` for tactics such as `finish`, in this case, we disable some kinds of parameters
such as `- ident`.
-/
public def elabGrindParams (params : Grind.Params) (ps : TSyntaxArray ``Parser.Tactic.grindParam)
    (only : Bool) (lax : Bool := false) (incremental := false) : TermElabM Grind.Params := do
  let mut params := params
  for p in ps do
    try
      match p with
      | `(Parser.Tactic.grindParam| - $id:ident) =>
        if incremental then
          throwErrorAt p "invalid `-` occurrence, it can only used at the `grind` tactic entry point"
        let declName ← realizeGlobalConstNoOverloadWithInfo id
        Linter.checkDeprecated declName
        if let some declName ← Grind.isCasesAttrCandidate? declName false then
          Grind.ensureNotBuiltinCases declName
          params ← params.eraseCasesTypes declName
        else if params.isInjectiveTheorem declName then
          params := params.eraseInj declName
        else
          params ← params.eraseEMatch declName
      | `(Parser.Tactic.grindParam| $[$mod?:grindMod]? $id:ident) =>
        -- Check if this is dot notation on a local variable (e.g., `n.triv` for `Nat.triv n`).
        -- If so, process as term to let elaboration resolve the dot notation properly.
        if let some (_, _ :: _) := (← resolveLocalName id.getId) then
          params ← processTermParam params p mod? id (minIndexable := false)
        else
          params ← processParam params p mod? id (minIndexable := false) (only := only) (incremental := incremental)
      | `(Parser.Tactic.grindParam| ! $[$mod?:grindMod]? $id:ident) =>
        if let some (_, _ :: _) := (← resolveLocalName id.getId) then
          params ← processTermParam params p mod? id (minIndexable := true)
        else
          params ← processParam params p mod? id (minIndexable := true) (only := only) (incremental := incremental)
      | `(Parser.Tactic.grindParam| $[$mod?:grindMod]? $e:term) =>
        params ← processTermParam params p mod? e (minIndexable := false)
      | `(Parser.Tactic.grindParam| ! $[$mod?:grindMod]? $e:term) =>
        params ← processTermParam params p mod? e (minIndexable := true)
      | `(Parser.Tactic.grindParam| #$anchor:hexnum) =>
        unless only do
          throwErrorAt anchor "invalid anchor, `only` modifier expected"
        params ← processAnchor params anchor
      | _ => throwError "unexpected `grind` parameter{indentD p}"
    catch ex =>
      if !lax then throw ex
  return params

namespace Grind
open Meta Grind

/--
Returns `true` if we should keep the theorem when `only` is used.
We keep
1- Local theorems. We use anchors to restrict their instantiation.
2- `match`-equations. They are always active.
-/
def shouldKeep (thm : EMatchTheorem) : GrindM Bool := do
  if let .decl declName := thm.origin then
    isMatchEqLikeDeclName declName
  else
    checkAnchorRefsEMatchTheoremProof thm.proof

/--
Removes all theorems that are not `match`-equations nor local theorems.
-/
def filterThms (thms : PArray EMatchTheorem) : GrindM (PArray EMatchTheorem) := do
  let mut result := {}
  for thm in thms do
    if (← shouldKeep thm) then
      result := result.push thm
  return result

/--
Helper method for processing parameters in tactics such as `finish` and `finish?`
-/
public def withParams (params : Grind.Params) (ps : TSyntaxArray ``Parser.Tactic.grindParam) (only : Bool)
    (k : GrindTacticM α) : GrindTacticM α := do
  if !only && ps.isEmpty then
    k
  else
    let mut params := params
    if only then
      params := { params with
        extensions  := params.extensions.map fun ext => { ext with ematch := {} }
        anchorRefs? := none
      }
    params ← elabGrindParams params ps (only := only) (incremental := true)
    let anchorRefs? := params.anchorRefs?
    withReader (fun c => { c with params, ctx.anchorRefs? := anchorRefs? }) do
    if only then
      -- Cleanup main goal before adding new facts
      let goal ← getMainGoal
      let goal ← liftGrindM do
        pure { goal with
        -- **TODO**: cleanup injective theorems
        ematch.thmMap  := {}
        ematch.thms    := (← filterThms goal.ematch.thms)
        ematch.newThms := (← filterThms goal.ematch.newThms)
      }
      replaceMainGoal [goal]
    liftGoalM do
      Grind.assertExtra params
      -- **TODO**: `cases` parameters
    k

end Grind
end Lean.Elab.Tactic
