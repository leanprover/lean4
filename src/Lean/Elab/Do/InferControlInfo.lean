/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Term
meta import Lean.Parser.Do
import Lean.Elab.Do.PatternVar

public section

namespace Lean.Elab.Do

open Lean Meta Parser.Term

structure ControlInfo where
  breaks : Bool := false
  continues : Bool := false
  returnsEarly : Bool := false
  exitsRegularly : Bool := true
  reassigns : NameSet := {}
  deriving Inhabited

def ControlInfo.pure : ControlInfo := {}

def ControlInfo.sequence (a b : ControlInfo) : ControlInfo :=
  if !a.exitsRegularly then a else {
    breaks := a.breaks || b.breaks,
    continues := a.continues || b.continues,
    returnsEarly := a.returnsEarly || b.returnsEarly,
    exitsRegularly := b.exitsRegularly,
    reassigns := a.reassigns ++ b.reassigns,
  }

def ControlInfo.alternative (a b : ControlInfo) : ControlInfo := {
    breaks := a.breaks || b.breaks,
    continues := a.continues || b.continues,
    returnsEarly := a.returnsEarly || b.returnsEarly,
    exitsRegularly := a.exitsRegularly || b.exitsRegularly,
    reassigns := a.reassigns ++ b.reassigns,
  }

instance : ToMessageData ControlInfo where
  toMessageData info := m!"breaks: {info.breaks}, continues: {info.continues},
    returnsEarly: {info.returnsEarly}, exitsRegularly: {info.exitsRegularly},
    reassigns: {info.reassigns.toList}"

/-- A handler for inferring `ControlInfo` from a `doElem` syntax. Register with `@[doElem_control_info parserName]`. -/
abbrev ControlInfoHandler := TSyntax `doElem → TermElabM ControlInfo

unsafe def mkControlInfoElemAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute ControlInfoHandler) :=
  mkElabAttribute ControlInfoHandler `builtin_doElem_control_info `doElem_control_info
    `Lean.Parser.Term.doElem ``Lean.Elab.Do.ControlInfoHandler "control info inference" ref

@[implemented_by mkControlInfoElemAttributeUnsafe]
opaque mkControlInfoElemAttribute (ref : Name) : IO (KeyedDeclsAttribute ControlInfoHandler)

/--
Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.

A handler should have type `ControlInfoHandler` (i.e. `TSyntax \`doElem → TermElabM ControlInfo`).
For pure handlers, use `fun stx => return ControlInfo.pure`.
-/
@[builtin_doc]
builtin_initialize controlInfoElemAttribute : KeyedDeclsAttribute ControlInfoHandler ←
  mkControlInfoElemAttribute decl_name%

namespace InferControlInfo

mutual

partial def ofElem (stx : TSyntax `doElem) : TermElabM ControlInfo := do
  let env ← getEnv
  if let some (_decl, stxNew?) ← liftMacroM (expandMacroImpl? env stx) then
    let stxNew ← liftMacroM <| liftExcept stxNew?
    return ← ofElem ⟨stxNew⟩

  match stx with
  | `(doElem| break) => return { breaks := true, exitsRegularly := false }
  | `(doElem| continue) => return { continues := true, exitsRegularly := false }
  | `(doElem| return $[$_]?) => return { returnsEarly := true, exitsRegularly := false }
  | `(doExpr| $_:term) => return { exitsRegularly := true }
  | `(doElem| do $doSeq) => ofSeq doSeq
  -- Let
  | `(doElem| let $[mut]? $_:letDecl) => return .pure
  | `(doElem| have $_:letDecl) => return .pure
  | `(doElem| let rec $_:letRecDecl) => return .pure
  | `(doElem| let $[mut]? $_ := $_ | $otherwise $(body?)?) =>
    ofLetOrReassign #[] none otherwise body?
  | `(doElem| let $[mut]? $decl) =>
    ofLetOrReassignArrow false decl
  | `(doElem| $decl:letIdDeclNoBinders) =>
    ofLetOrReassign (← getLetIdDeclVars ⟨decl⟩) none none none
  | `(doElem| $decl:letPatDecl) =>
    ofLetOrReassign (← getLetPatDeclVars ⟨decl⟩) none none none
  | `(doElem| $decl:doIdDecl) =>
    ofLetOrReassignArrow true decl
  | `(doElem| $decl:doPatDecl) =>
    ofLetOrReassignArrow true decl
  -- match
  | `(doElem| match $[(dependent := $_)]? $[(generalizing := $_)]? $(_)? $_,* with $alts:matchAlt*) =>
    let mut info := {}
    for alt in alts do
      let `(matchAltExpr| | $[$_,*]|* => $rhs) := alt | throwUnsupportedSyntax
      let rhsInfo ← ofSeq ⟨rhs⟩
      info := info.alternative rhsInfo
    return info
  -- If
  | `(doElem| if $_:doIfCond then $thenSeq $[else if $_:doIfCond then $thenSeqs]* $[else $elseSeq?]?) =>
    let mut info ← ofOptionSeq elseSeq?
    -- Since doIfLetBind does not allow `doElem`, `cond` always has default `ControlInfo`.
    for thenSeq in thenSeqs.reverse do
      let thenInfo ← ofSeq thenSeq
      info := thenInfo.alternative info
    let thenInfo ← ofSeq thenSeq
    return thenInfo.alternative info
  | `(doElem| unless $_ do $elseSeq) =>
    ControlInfo.alternative {} <$> ofSeq elseSeq
  | `(doElem| for $[$[$_ :]? $_ in $_],* do $bodySeq) =>
    let info ← ofSeq bodySeq
    return { info with  -- keep only reassigns and earlyReturn
      exitsRegularly := true,
      continues := false,
      breaks := false
    }
  -- Try
  | `(doElem| try $trySeq:doSeq $[$catches]* $[finally $finSeq?]?) =>
    let mut info ← ofSeq trySeq
    for catch_ in catches do
      match catch_ with
      | `(doCatch| catch $_ $[: $_]? => $catchSeq) =>
        let catchInfo ← ofSeq catchSeq
        info := catchInfo.alternative info
      | `(doCatchMatch| catch $matchAlts:matchAlt*) =>
        for alt in matchAlts do
          let `(matchAltExpr| | $[$_,*]|* => $rhs) := alt | throwUnsupportedSyntax
          let catchInfo ← ofSeq ⟨rhs⟩
          info := info.alternative catchInfo
      | _ => throwError "Not a catch or catch match: {toString catch_}"
    let finInfo ← ofOptionSeq finSeq?
    return info.sequence finInfo
  -- Misc
  | `(doElem| dbg_trace $_) => return .pure
  | `(doElem| assert! $_) => return .pure
  | `(doElem| debug_assert! $_) => return .pure
  -- match_expr and let_expr
  | `(doElem| match_expr $[(meta := false)]? $_ with $[| $_:matchExprPat => $rhsSeqs]* | _ => $elseSeq) =>
    let mut info ← ofSeq elseSeq
    for rhsSeq in rhsSeqs do
      let rhsInfo ← ofSeq rhsSeq
      info := rhsInfo.alternative info
    return info
  | `(doElem| let_expr $_ := $_ | $otherwise $(body?)?)
  | `(doElem| let_expr $_ ← $_ | $otherwise $(body?)?) =>
    -- rhs is always just a term
    let otherwiseInfo ← ofSeq ⟨otherwise⟩
    let bodyInfo ← match body? with | none => pure {} | some body => ofSeq ⟨body⟩
    return otherwiseInfo.alternative bodyInfo
  | _ =>
    let handlers := controlInfoElemAttribute.getEntries (← getEnv) stx.raw.getKind
    for handler in handlers do
      let res ← catchInternalId unsupportedSyntaxExceptionId
        (some <$> handler.value stx)
        (fun _ => pure none)
      if let some info := res then return info
    throwError
      "No `ControlInfo` inference handler found for `{stx.raw.getKind}` in syntax {indentD stx}\n\
       Register a handler with `@[doElem_control_info {stx.raw.getKind}]`."

partial def ofLetOrReassignArrow (reassignment : Bool) (decl : TSyntax [``doIdDecl, ``doPatDecl]) : TermElabM ControlInfo := do
  match decl with
  | `(doIdDecl| $x:ident $[: $_]? ← $rhs) =>
    let reassigns := if reassignment then #[x] else #[]
    ofLetOrReassign reassigns rhs none none
  | `(doPatDecl| $pattern ← $rhs $[| $otherwise? $[$body??]?]?) =>
    let reassigns ← if reassignment then getPatternVarsEx pattern else pure #[]
    ofLetOrReassign reassigns rhs otherwise? body??.join
  | _ => throwError "Not a let or reassignment declaration: {toString decl}"

partial def ofLetOrReassign (reassigned : Array Ident) (rhs? : Option (TSyntax `doElem))
    (otherwise? : Option (TSyntax ``doSeqIndent)) (body? : Option (TSyntax ``doSeqIndent))
    : TermElabM ControlInfo := do
  let rhs ← match rhs? with | none => pure { : ControlInfo } | some rhs => ofElem rhs
  let otherwise ← match otherwise? with | none => pure { : ControlInfo } | some otherwise => ofSeq ⟨otherwise⟩
  let body ← match body? with | none => pure { : ControlInfo } | some body => ofSeq ⟨body⟩
  let info := rhs.sequence (body.alternative otherwise)
  return { info with reassigns := (reassigned.map TSyntax.getId).foldl NameSet.insert info.reassigns }

partial def ofSeq (stx : TSyntax ``doSeq) : TermElabM ControlInfo := do
  let mut info : ControlInfo := {}
  for elem in getDoElems stx do
    if !info.exitsRegularly then
      break
    let elemInfo ← ofElem elem
    info := {
      info with
      breaks := info.breaks || elemInfo.breaks
      continues := info.continues || elemInfo.continues
      returnsEarly := info.returnsEarly || elemInfo.returnsEarly
      exitsRegularly := elemInfo.exitsRegularly
      reassigns := info.reassigns ++ elemInfo.reassigns
    }
  return info

partial def ofOptionSeq (stx? : Option (TSyntax ``doSeq)) : TermElabM ControlInfo := do
  match stx? with | none => pure { : ControlInfo } | some stx => ofSeq stx

end

end InferControlInfo

def inferControlInfoSeq (doSeq : TSyntax ``doSeq) : TermElabM ControlInfo :=
  InferControlInfo.ofSeq doSeq

def inferControlInfoElem (doElem : TSyntax `doElem) : TermElabM ControlInfo :=
  InferControlInfo.ofElem doElem
