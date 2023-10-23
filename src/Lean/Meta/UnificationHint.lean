/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers
import Lean.Meta.DiscrTree
import Lean.Meta.SynthInstance

namespace Lean.Meta

abbrev UnificationHintKey := DiscrTree.Key

structure UnificationHintEntry where
  keys        : Array UnificationHintKey
  val         : Name
  deriving Inhabited

abbrev UnificationHintTree := DiscrTree Name

structure UnificationHints where
  discrTree : UnificationHintTree := DiscrTree.empty
  deriving Inhabited

instance : ToFormat UnificationHints where
  format h := format h.discrTree

def UnificationHints.config : WhnfCoreConfig := { iota := false, proj := .no }

def UnificationHints.add (hints : UnificationHints) (e : UnificationHintEntry) : UnificationHints :=
  { hints with discrTree := hints.discrTree.insertCore e.keys e.val config }

builtin_initialize unificationHintExtension : SimpleScopedEnvExtension UnificationHintEntry UnificationHints ←
  registerSimpleScopedEnvExtension {
    addEntry := UnificationHints.add
    initial  := {}
  }

structure UnificationConstraint where
  lhs : Expr
  rhs : Expr

structure UnificationHint where
  pattern     : UnificationConstraint
  constraints : List UnificationConstraint

private partial def decodeUnificationHint (e : Expr) : ExceptT MessageData Id UnificationHint := do
  decode e #[]
where
  decodeConstraint (e : Expr) : ExceptT MessageData Id UnificationConstraint :=
    match e.eq? with
    | some (_, lhs, rhs) => return UnificationConstraint.mk lhs rhs
    | none => throw m!"invalid unification hint constraint, unexpected term{indentExpr e}"
  decode (e : Expr) (cs : Array UnificationConstraint) : ExceptT MessageData Id UnificationHint := do
    match e with
    | Expr.forallE _ d b _ => do
      let c ← decodeConstraint d
      if b.hasLooseBVars then
        throw m!"invalid unification hint constraint, unexpected dependency{indentExpr e}"
      decode b (cs.push c)
    | _ => do
      let p ← decodeConstraint e
      return { pattern := p, constraints := cs.toList }

private partial def validateHint (hint : UnificationHint) : MetaM Unit := do
  hint.constraints.forM fun c => do
    unless (← isDefEq c.lhs c.rhs) do
      throwError "invalid unification hint, failed to unify constraint left-hand-side{indentExpr c.lhs}\nwith right-hand-side{indentExpr c.rhs}"
  unless (← isDefEq hint.pattern.lhs hint.pattern.rhs) do
    throwError "invalid unification hint, failed to unify pattern left-hand-side{indentExpr hint.pattern.lhs}\nwith right-hand-side{indentExpr hint.pattern.rhs}"

def addUnificationHint (declName : Name) (kind : AttributeKind) : MetaM Unit :=
  withNewMCtxDepth do
    let info ← getConstInfo declName
    match info.value? with
    | none => throwError "invalid unification hint, it must be a definition"
    | some val =>
      let (_, _, body) ← lambdaMetaTelescope val
      match decodeUnificationHint body with
      | Except.error msg => throwError msg
      | Except.ok hint =>
        let keys ← DiscrTree.mkPath hint.pattern.lhs UnificationHints.config
        validateHint hint
        unificationHintExtension.add { keys := keys, val := declName } kind

builtin_initialize
  registerBuiltinAttribute {
    name  := `unification_hint
    descr := "unification hint"
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      discard <| addUnificationHint declName kind |>.run
  }

def tryUnificationHints (t s : Expr) : MetaM Bool := do
  trace[Meta.isDefEq.hint] "{t} =?= {s}"
  unless (← read).config.unificationHints do
    return false
  if t.isMVar then
    return false
  let hints := unificationHintExtension.getState (← getEnv)
  let candidates ← hints.discrTree.getMatch t UnificationHints.config
  for candidate in candidates do
    if (← tryCandidate candidate) then
      return true
  return false
where
  isDefEqPattern p e :=
    withReducible <| Meta.isExprDefEqAux p e

  tryCandidate candidate : MetaM Bool :=
    withTraceNode `Meta.isDefEq.hint
      (return m!"{exceptBoolEmoji ·} hint {candidate} at {t} =?= {s}") do
    checkpointDefEq do
      let cinfo ← getConstInfo candidate
      let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
      let val ← instantiateValueLevelParams cinfo us
      let (xs, bis, body) ← lambdaMetaTelescope val
      let hint? ← withConfig (fun cfg => { cfg with unificationHints := false }) do
        match decodeUnificationHint body with
        | Except.error _ => return none
        | Except.ok hint =>
          if (← isDefEqPattern hint.pattern.lhs t <&&> isDefEqPattern hint.pattern.rhs s) then
            return some hint
          else
            return none
      match hint? with
      | none      => return false
      | some hint =>
        trace[Meta.isDefEq.hint] "{candidate} succeeded, applying constraints"
        for c in hint.constraints do
          unless (← Meta.isExprDefEqAux c.lhs c.rhs) do
            return false
        for x in xs, bi in bis do
          if bi == BinderInfo.instImplicit then
            match (← trySynthInstance (← inferType x)) with
            | LOption.some val => unless (← isDefEq x val) do return false
            | _                => return false
        return true

builtin_initialize
  registerTraceClass `Meta.isDefEq.hint

end Lean.Meta
