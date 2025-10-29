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
import Lean.Elab.Tactic.Grind.Basic
import Lean.Elab.Tactic.Grind.Anchor
namespace Lean.Elab.Tactic
open Meta

/-!
`grind` parameter elaboration
-/

def warnRedundantEMatchArg (s : Grind.EMatchTheorems) (declName : Name) : MetaM Unit := do
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
          params.ematch.containsWithSamePatterns thm₁.origin thm₁.patterns &&
          params.ematch.containsWithSamePatterns thm₂.origin thm₂.patterns then
        warnRedundantEMatchArg params.ematch declName
      return { params with extra := params.extra.push thm₁ |>.push thm₂ }
    | _ =>
      if kind matches .eqLhs _ | .eqRhs _ then
        ensureNoMinIndexable minIndexable
      let thm ← if suggest && !Grind.backward.grind.inferPattern.get (← getOptions) then
        Grind.mkEMatchTheoremAndSuggest id declName params.symPrios minIndexable (isParam := true)
      else
        Grind.mkEMatchTheoremForDecl declName kind params.symPrios (minIndexable := minIndexable)
      if warn && params.ematch.containsWithSamePatterns thm.origin thm.patterns then
        warnRedundantEMatchArg params.ematch declName
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

def processParam (params : Grind.Params)
    (p : TSyntax `Lean.Parser.Tactic.grindParam)
    (mod? : Option (TSyntax `Lean.Parser.Attr.grindMod))
    (id : TSyntax `ident)
    (minIndexable : Bool)
    (only : Bool)
    (incremental : Bool)
    : MetaM Grind.Params := do
  let mut params := params
  let declName ← try
    realizeGlobalConstNoOverloadWithInfo id
  catch err =>
    if (← resolveLocalName id.getId).isSome then
      throwErrorAt id "redundant parameter `{id}`, `grind` uses local hypotheses automatically"
    else
      throw err
  let kind ← if let some mod := mod? then Grind.getAttrKindCore mod else pure .infer
  match kind with
  | .ematch .user =>
    unless only do
      withRef p <| Grind.throwInvalidUsrModifier
    ensureNoMinIndexable minIndexable
    let s ← Grind.getEMatchTheorems
    let thms := s.find (.decl declName)
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
    params := { params with casesTypes := params.casesTypes.insert declName eager }
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
      params := { params with casesTypes := params.casesTypes.insert declName false }
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
  return params

def processAnchor (params : Grind.Params) (val : TSyntax `hexnum) : CoreM Grind.Params := do
  let anchorRefs := params.anchorRefs?.getD #[]
  let anchorRef ← Grind.elabAnchorRef val
  return { params with anchorRefs? := some <| anchorRefs.push anchorRef }

/--
Elaborates `grind` parameters.
`incremental = true` for tactics such as `finish`, in this case, we disable some kinds of parameters
such as `- ident`.
-/
public def elabGrindParams (params : Grind.Params) (ps : TSyntaxArray ``Parser.Tactic.grindParam)
    (only : Bool) (lax : Bool := false) (incremental := false) : MetaM Grind.Params := do
  let mut params := params
  for p in ps do
    try
      match p with
      | `(Parser.Tactic.grindParam| - $id:ident) =>
        if incremental then
          throwErrorAt p "invalid `-` occurrence, it can only used at the `grind` tactic entry point"
        let declName ← realizeGlobalConstNoOverloadWithInfo id
        if let some declName ← Grind.isCasesAttrCandidate? declName false then
          Grind.ensureNotBuiltinCases declName
          params := { params with casesTypes := (← params.casesTypes.eraseDecl declName) }
        else if (← Grind.isInjectiveTheorem declName) then
          params := { params with inj := params.inj.erase (.decl declName) }
        else
          params := { params with ematch := (← params.ematch.eraseDecl declName) }
      | `(Parser.Tactic.grindParam| $[$mod?:grindMod]? $id:ident) =>
        params ← processParam params p mod? id (minIndexable := false) (only := only) (incremental := incremental)
      | `(Parser.Tactic.grindParam| ! $[$mod?:grindMod]? $id:ident) =>
        params ← processParam params p mod? id (minIndexable := true) (only := only) (incremental := incremental)
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
      params := { params with anchorRefs? := none }
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
      for thm in params.extra do
        activateTheorem thm 0
      for thm in params.extraInj do
        activateInjectiveTheorem thm 0
      -- **TODO**: `cases` parameters
    k

end Grind
end Lean.Elab.Tactic
