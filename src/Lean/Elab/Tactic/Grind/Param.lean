/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Main
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
    ensureNoMinIndexable minIndexable
    withRef p <| Grind.validateCasesAttr declName eager
    params := { params with casesTypes := params.casesTypes.insert declName eager }
  | .intro =>
    if let some info ← Grind.isCasesAttrPredicateCandidate? declName false then
      for ctor in info.ctors do
        params ← withRef p <| addEMatchTheorem params id ctor (.default false) minIndexable
    else
      throwError "invalid use of `intro` modifier, `{.ofConstName declName}` is not an inductive predicate"
  | .inj =>
    let thm ← Grind.mkInjectiveTheorem declName
    params := { params with inj := params.inj.insert thm }
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
  let anchors := params.anchors?.getD #[]
  let anchor ← Grind.elabAnchor val
  return { params with anchors? := some <| anchors.push anchor }

public def elabGrindParams (params : Grind.Params) (ps : TSyntaxArray ``Parser.Tactic.grindParam)
    (only : Bool) (lax : Bool := false) : MetaM Grind.Params := do
  let mut params := params
  for p in ps do
    try
      match p with
      | `(Parser.Tactic.grindParam| - $id:ident) =>
        let declName ← realizeGlobalConstNoOverloadWithInfo id
        if let some declName ← Grind.isCasesAttrCandidate? declName false then
          Grind.ensureNotBuiltinCases declName
          params := { params with casesTypes := (← params.casesTypes.eraseDecl declName) }
        else if (← Grind.isInjectiveTheorem declName) then
          params := { params with inj := params.inj.erase (.decl declName) }
        else
          params := { params with ematch := (← params.ematch.eraseDecl declName) }
      | `(Parser.Tactic.grindParam| $[$mod?:grindMod]? $id:ident) =>
        params ← processParam params p mod? id (minIndexable := false) (only := only)
      | `(Parser.Tactic.grindParam| ! $[$mod?:grindMod]? $id:ident) =>
        params ← processParam params p mod? id (minIndexable := true) (only := only)
      | `(Parser.Tactic.grindParam| #$anchor:hexnum) =>
        params ← processAnchor params anchor
      | _ => throwError "unexpected `grind` parameter{indentD p}"
    catch ex =>
      if !lax then throw ex
  return params

end Lean.Elab.Tactic
