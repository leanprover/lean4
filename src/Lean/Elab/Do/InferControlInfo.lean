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

/--
Represents information about what control effects a `do` block has.

The fields split by flavor:

* `breaks`, `continues`, `returnsEarly`, and `reassigns` are **syntactic**: `true`/non-empty iff
  the corresponding construct appears anywhere in the source text of the block, independent of
  whether it is semantically reachable. Downstream elaborators must assume every such syntactic
  effect may occur, because the elaborator visits every doElem (only top-level
  `return`/`break`/`continue` short-circuit via `elabAsSyntacticallyDeadCode`).
* `numRegularExits` is also **syntactic**: the number of times the block wires the enclosing
  continuation into its elaborated expression. `withDuplicableCont` reads it as a join-point
  duplication trigger (`> 1`).
* `noFallthrough = true` asserts that the next doElem in the enclosing sequence is semantically
  irrelevant (control never falls through to it). `noFallthrough = false` makes no such
  assertion. The dead-code warning fires on the next element when this is `true`.

Invariant: `numRegularExits = 0 → noFallthrough`. The converse does not hold.
-/
structure ControlInfo where
  /-- The `do` block syntactically contains a `break`. -/
  breaks : Bool := false
  /-- The `do` block syntactically contains a `continue`. -/
  continues : Bool := false
  /-- The `do` block syntactically contains an early `return`. -/
  returnsEarly : Bool := false
  /--
  The number of times the block wires the enclosing continuation into its elaborated expression.
  Consumed by `withDuplicableCont` to decide whether to introduce a join point (`> 1`).
  -/
  numRegularExits : Nat := 1
  /--
  When `true`, asserts that the next doElem in the enclosing sequence is semantically irrelevant
  (control never falls through to it). `false` asserts nothing.
  -/
  noFallthrough : Bool := false
  /-- The variables that are syntactically reassigned somewhere in the `do` block. -/
  reassigns : NameSet := {}
  deriving Inhabited

def ControlInfo.pure : ControlInfo := {}

/--
The identity of `ControlInfo.alternative`: a `ControlInfo` describing a block with no branches
at all (so no regular exits and the next element is trivially unreachable).
-/
def ControlInfo.empty : ControlInfo := { numRegularExits := 0, noFallthrough := true }

def ControlInfo.sequence (a b : ControlInfo) : ControlInfo := {
    -- Syntactic fields aggregate unconditionally; the elaborator keeps visiting `b` unless `a` is
    -- a syntactically-terminal element (only top-level `return`/`break`/`continue` are, via
    -- `elabAsSyntacticallyDeadCode`).
    breaks := a.breaks || b.breaks,
    continues := a.continues || b.continues,
    returnsEarly := a.returnsEarly || b.returnsEarly,
    reassigns := a.reassigns ++ b.reassigns,
    numRegularExits := b.numRegularExits,
    -- Semantic: the sequence is dead if either part is dead.
    noFallthrough := a.noFallthrough || b.noFallthrough,
  }

def ControlInfo.alternative (a b : ControlInfo) : ControlInfo := {
    breaks := a.breaks || b.breaks,
    continues := a.continues || b.continues,
    returnsEarly := a.returnsEarly || b.returnsEarly,
    reassigns := a.reassigns ++ b.reassigns,
    numRegularExits := a.numRegularExits + b.numRegularExits,
    -- Semantic: alternatives are dead only if all branches are dead.
    noFallthrough := a.noFallthrough && b.noFallthrough,
  }

instance : ToMessageData ControlInfo where
  toMessageData info := m!"breaks: {info.breaks}, continues: {info.continues},
    returnsEarly: {info.returnsEarly}, numRegularExits: {info.numRegularExits},
    noFallthrough: {info.noFallthrough}, reassigns: {info.reassigns.toList}"

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

open InternalSyntax in
mutual

partial def ofElem (stx : TSyntax `doElem) : TermElabM ControlInfo := do
  let env ← getEnv
  if let some (_decl, stxNew?) ← liftMacroM (expandMacroImpl? env stx) then
    let stxNew ← liftMacroM <| liftExcept stxNew?
    return ← ofElem ⟨stxNew⟩

  match stx with
  | `(doElem| break) => return { breaks := true, numRegularExits := 0, noFallthrough := true }
  | `(doElem| continue) => return { continues := true, numRegularExits := 0, noFallthrough := true }
  | `(doElem| return $[$_]?) => return { returnsEarly := true, numRegularExits := 0, noFallthrough := true }
  | `(doExpr| $_:term) => return { numRegularExits := 1 }
  | `(doElem| do $doSeq) => ofSeq doSeq
  -- Let
  | `(doElem| let $[mut]? $_:letConfig $_:letDecl) => return .pure
  | `(doElem| have $_:letConfig $_:letDecl) => return .pure
  | `(doElem| let rec $_:letRecDecl) => return .pure
  | `(doElem| let $[mut]? $_:letConfig $_ := $_ | $otherwise $(body?)?) =>
    ofLetOrReassign #[] none otherwise body?
  | `(doElem| let $[mut]? $_:letConfig $decl) =>
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
    let mut info := ControlInfo.empty
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
  -- For/Repeat
  | `(doElem| for $[$[$_ :]? $_ in $_],* do $bodySeq) =>
    let info ← ofSeq bodySeq
    return { info with  -- keep only reassigns and earlyReturn
      numRegularExits := 1,
      continues := false,
      breaks := false,
      noFallthrough := false,
    }
  | `(doRepeat| repeat $bodySeq) =>
    -- A break-less `repeat` never falls through; the elaborator injects an `unreachable!` so the
    -- surrounding continuation still has a polymorphic value to hand back, and any dead-code
    -- warning on subsequent elements is actionable.
    let info ← ofSeq bodySeq
    return { info with  -- keep only reassigns and earlyReturn
      numRegularExits := if info.breaks then 1 else 0,
      continues := false,
      breaks := false,
      noFallthrough := !info.breaks,
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
  | `(doElem| skip) => return .pure
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
    let kind := stx.raw.getKind
    let handlers := controlInfoElemAttribute.getEntries (← getEnv) kind
    for handler in handlers do
      let res ← catchInternalId unsupportedSyntaxExceptionId
        (some <$> handler.value stx)
        (fun _ => pure none)
      if let some info := res then return info
    throwError
      "No `ControlInfo` inference handler found for `{kind}` in syntax {indentD stx}\n\
       Register a handler with `@[doElem_control_info {kind}]`."

partial def ofLetOrReassignArrow (reassignment : Bool) (decl : TSyntax [``doIdDecl, ``doPatDecl]) : TermElabM ControlInfo := do
  match decl with
  | `(doIdDecl| $x:ident $[: $_]? ← $rhs) =>
    let reassigns := if reassignment then #[x] else #[]
    ofLetOrReassign reassigns rhs none none
  | `(doPatDecl| $pattern $[: $_]? ← $rhs $[| $otherwise? $[$body??]?]?) =>
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
    info := info.sequence (← ofElem elem)
  return info

partial def ofOptionSeq (stx? : Option (TSyntax ``doSeq)) : TermElabM ControlInfo := do
  match stx? with | none => pure { : ControlInfo } | some stx => ofSeq stx

end

end InferControlInfo

def inferControlInfoSeq (doSeq : TSyntax ``doSeq) : TermElabM ControlInfo :=
  InferControlInfo.ofSeq doSeq

def inferControlInfoElem (doElem : TSyntax `doElem) : TermElabM ControlInfo :=
  InferControlInfo.ofElem doElem
