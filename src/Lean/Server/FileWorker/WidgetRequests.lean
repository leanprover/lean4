/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
module

prelude

public import Lean.Server.Rpc.RequestHandling
public import Lean.Server.FileWorker.RequestHandling
import Lean.PrettyPrinter.Delaborator.Builtins
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

public section

/-! Registers all widget-related RPC procedures. -/

namespace Lean.Widget
open Server Lean.Elab

structure MsgToInteractive where
  msg : WithRpcRef MessageData
  indent : Nat
  deriving Inhabited, RpcEncodable

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.InteractiveDiagnostics.msgToInteractive
    MsgToInteractive
    InteractiveMessage
    fun ⟨m, i⟩ => RequestM.pureTask do msgToInteractive m.val i (hasWidgets := true)

/-- The information that the infoview uses to render a popup
for when the user hovers over an expression.
-/
structure InfoPopup where
  type : Option CodeWithInfos
  /-- Show the term with the implicit arguments. -/
  exprExplicit : Option CodeWithInfos
  /-- Docstring. In markdown. -/
  doc : Option String
  deriving Inhabited, RpcEncodable

open PrettyPrinter.Delaborator in
/-- Given elaborator info for a particular subexpression. Produce the `InfoPopup`.

The intended usage of this is for the infoview to pass the `InfoWithCtx` which
was stored for a particular `SubexprInfo` tag in a `TaggedText` generated with `ppExprTagged`.
 -/
def makePopup : WithRpcRef InfoWithCtx → RequestM (RequestTask InfoPopup)
  | i => RequestM.pureTask do
    let i := i.val
    i.ctx.runMetaM i.info.lctx do
      let type? ← match (← i.info.type?) with
        | some type => some <$> ppExprTagged type
        | none => pure none
      let exprExplicit? ← match i.info with
        | Elab.Info.ofTermInfo ti =>
          some <$> ppExprForPopup ti.expr (explicit := true)
        | Elab.Info.ofDelabTermInfo { toTermInfo := ti, explicit, ..} =>
          some <$> ppExprForPopup ti.expr (explicit := explicit)
        | Elab.Info.ofFieldInfo fi => pure <| some <| TaggedText.text fi.fieldName.toString
        | _ => pure none
      return {
        type := type?
        exprExplicit := exprExplicit?
        doc := ← i.info.docString? : InfoPopup
      }
where
  maybeWithoutTopLevelHighlight : Bool → CodeWithInfos → CodeWithInfos
    | true, .tag _ tt => tt
    | _,    tt        => tt
  ppExprForPopup (e : Expr) (explicit : Bool := false) : MetaM CodeWithInfos := do
    let mut e := e
    -- When hovering over a metavariable, we want to see its value, even if `pp.instantiateMVars` is false.
    if explicit && e.isMVar then
      if let some e' ← getExprMVarAssignment? e.mvarId! then
        e := e'
    -- When `explicit` is false, keep the top-level tag so that users can also see the explicit version of the term on an additional hover.
    maybeWithoutTopLevelHighlight explicit <$> ppExprTagged e do
      if explicit then
        withOptionAtCurrPos pp.tagAppFns.name true do
        withOptionAtCurrPos pp.explicit.name true do
        withOptionAtCurrPos pp.mvars.anonymous.name true do
          delabApp
      else
        withOptionAtCurrPos pp.proofs.name true do
        withOptionAtCurrPos pp.sorrySource.name true do
          delab

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.InteractiveDiagnostics.infoToInteractive
    (WithRpcRef InfoWithCtx)
    InfoPopup
    makePopup

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getInteractiveGoals
    Lsp.PlainGoalParams
    (Option InteractiveGoals)
    FileWorker.getInteractiveGoals

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getInteractiveTermGoal
    Lsp.PlainTermGoalParams
    (Option InteractiveTermGoal)
    FileWorker.getInteractiveTermGoal

structure GetInteractiveDiagnosticsParams where
  /-- Return diagnostics for these lines only if present,
  otherwise return all diagnostics. -/
  lineRange? : Option Lsp.LineRange
  deriving Inhabited, FromJson, ToJson

structure GetGoToLocationParams where
  kind : GoToKind
  info : WithRpcRef InfoWithCtx
  deriving RpcEncodable

builtin_initialize
  registerBuiltinRpcProcedure
    `Lean.Widget.getGoToLocation
    GetGoToLocationParams
    (Array Lsp.LocationLink)
    fun ⟨kind, i⟩ => RequestM.pureTask do
      let i := i.val
      let rc ← read
      let ls ← locationLinksOfInfo rc.doc.meta kind i
      let ls := ls.map (·.toLocationLink)
      if !ls.isEmpty then return ls
      -- TODO(WN): unify handling of delab'd (infoview) and elab'd (editor) applications
      let .ofTermInfo ti := i.info | return #[]
      let .app _ _ := ti.expr | return #[]
      let some nm := ti.expr.getAppFn.constName? | return #[]
      let ctx : GoToContext := {
        doc := rc.doc.meta
        kind
        infoTree? := none
        originInfo? := none
        children := PersistentArray.empty
      }
      GoToM.run ctx i.ctx ti.lctx do
        let ls ← locationLinksFromDecl nm
        return ls.map (·.toLocationLink)

def lazyTraceChildrenToInteractive (children : WithRpcRef LazyTraceChildren) :
    RequestM (RequestTask (Array InteractiveMessage)) :=
  RequestM.pureTask do
    let ⟨indent, children⟩ := children.val
    children.mapM fun child => do
      msgToInteractive child.val (hasWidgets := true) (indent := indent)

builtin_initialize registerBuiltinRpcProcedure ``lazyTraceChildrenToInteractive _ _ lazyTraceChildrenToInteractive

private def kmpSearch (query text : String) : Array String.Pos.Raw := Id.run do
  if query.isEmpty then
    return #[]
  let query := query.toUTF8
  let text := text.toUTF8
  let table := buildKMPTable query
  let mut r := #[]
  let mut qi : Int := 0
  for h:ti in *...text.size do
    while qi >= 0 && text[ti] != query[qi.toNat]! do
      qi := table[qi.toNat]!
    qi := qi + 1
    if qi == query.size then
      r := r.push <| (ti + 1) - query.size
      qi := table[qi.toNat]!
  return r.map (⟨·⟩)
where
  buildKMPTable (w : ByteArray) : Array Int := Id.run do
    let mut t := Array.emptyWithCapacity w.size
    let mut n := -1
    t := t.push n
    for h:i in *...w.size do
      while n >= 0 && w[n.toNat]! != w[i] do
        n := t[n.toNat]!
      n := n + 1
      t := t.push n
    return t

private def contains (query text : String) : Bool :=
  ! (kmpSearch query text).isEmpty

private def matchEndPos (query : String) (startPos : String.Pos.Raw) : String.Pos.Raw :=
  startPos + query

@[specialize]
private def hightlightStringMatches? (query text : String) (matchPositions : Array String.Pos.Raw)
    (highlight : α) (offset : String.Pos.Raw := ⟨0⟩) (mapIdx : Nat → Nat := id) :
    Option (TaggedText α) := Id.run do
  if query.isEmpty || text.isEmpty || matchPositions.isEmpty then
    return none
  let mut anyMatch : Bool := false
  let mut r : Array (TaggedText α) := #[]
  let mut p : String.Pos.Raw := ⟨0⟩
  for i in 0...matchPositions.size do
    if p >= text.rawEndPos then
      break
    let i := mapIdx i
    let globalMatchPos := matchPositions[i]!
    let matchPos := globalMatchPos.unoffsetBy offset
    if matchPos >= text.rawEndPos then
      break
    if let some nonMatch := nonMatch? p matchPos then
      r := r.push nonMatch
    let globalMatchEndPos := matchEndPos query globalMatchPos
    let matchEndPos := globalMatchEndPos.unoffsetBy offset
    let «match» := String.Pos.Raw.extract text matchPos matchEndPos
    r := r.push <| .tag highlight (.text «match»)
    p := matchEndPos
    anyMatch := true
  if let some nonMatch := nonMatch? p text.rawEndPos then
    r := r.push nonMatch
  if ! anyMatch then
    return none
  if h : r.size = 1 then
    return some r[0]
  return some (.append r)
where
  nonMatch? (p matchPosition : String.Pos.Raw) : Option (TaggedText α) := do
    guard <| p < matchPosition
    let nonMatch := String.Pos.Raw.extract text p matchPosition
    return .text nonMatch

private def findTaggedTextMatches (query : String) (tt : TaggedText α) (toText : α → String) :
    Array String.Pos.Raw :=
  let tt : TaggedText Empty := tt.rewrite fun t _ => .text (toText t)
  kmpSearch query tt.stripTags

private structure TaggedTextHighlightState where
  query        : String
  ms           : Array String.Pos.Raw
  p            : String.Pos.Raw
  anyHighlight : Bool

private def advanceTaggedTextHighlightState (text : String) (highlighted : α) :
    StateM TaggedTextHighlightState (TaggedText α) := do
  let query := (← get).query
  let p := (← get).p
  let ms := (← get).ms
  let highlighted? := hightlightStringMatches? query text ms highlighted (offset := p)
    (mapIdx := fun i => ms.size - i - 1)
  updateState text highlighted?.isSome
  return highlighted?.getD (.text text)
where
  updateState (text : String) (isHighlighted : Bool) : StateM TaggedTextHighlightState Unit :=
    modify fun s =>
      let p : String.Pos.Raw := s.p.increaseBy text.utf8ByteSize
      let ms := updateMatches s.query s.ms p
      let anyHighlight := s.anyHighlight || isHighlighted
      { s with p, ms, anyHighlight }
  updateMatches (query : String) (ms : Array String.Pos.Raw) (p : String.Pos.Raw) : Array String.Pos.Raw := Id.run do
    let n := ms.size
    let mut ms := ms
    for i in 0...n do
      if p >= matchEndPos query ms[n - i - 1]! then
        ms := ms.pop
    return ms

@[specialize]
private partial def highlightTaggedText (query : String) (tt : TaggedText α) (highlighted : β)
    (toText : (t : α) → String)
    (highlightTag :
      (t : α) →
      (highlightTaggedText :
        TaggedText α →
        StateM TaggedTextHighlightState (TaggedText β)) →
      StateM TaggedTextHighlightState β) :
    TaggedText β × Bool :=
  let ms := findTaggedTextMatches query tt toText
  let (tt, s) := go tt |>.run { query, p := ⟨0⟩, ms := ms.reverse, anyHighlight := false }
  (tt, s.anyHighlight)
where
  go (tt : TaggedText α) : StateM TaggedTextHighlightState (TaggedText β) := do
    match tt with
    | .text s =>
      advanceTaggedTextHighlightState s highlighted
    | .append a =>
      return .append (← a.mapM go)
    | .tag t a =>
      let t ← highlightTag t go
      let a ← go a
      return .tag t a

inductive HighlightedSubexprInfo where
  | subexpr (info : SubexprInfo)
  | highlighted

instance : RpcEncodable HighlightedSubexprInfo where
  rpcEncode
    | .subexpr info => rpcEncode info
    | .highlighted => pure "highlighted"
  rpcDecode
    | .str "highlighted" => pure .highlighted
    | j => do
      return .subexpr (← rpcDecode j)

abbrev HighlightedCodeWithInfos := TaggedText HighlightedSubexprInfo

private def HighlightedCodeWithInfos.ofCodeWithInfos (c : CodeWithInfos) :
    HighlightedCodeWithInfos :=
  c.map .subexpr

private partial def highlightCodeWithInfos (query : String) (c : CodeWithInfos) :
    HighlightedCodeWithInfos × Bool :=
  highlightTaggedText query c .highlighted (fun _ => "") fun i _ => pure <| .subexpr i

inductive HighlightedMsgEmbed where
  | expr : HighlightedCodeWithInfos → HighlightedMsgEmbed
  | goal : InteractiveGoal → HighlightedMsgEmbed
  | widget (wi : Widget.WidgetInstance) (alt : TaggedText HighlightedMsgEmbed)
  | trace (indent : Nat) (cls : Name) (msg : TaggedText HighlightedMsgEmbed) (collapsed : Bool)
      (children : StrictOrLazy
        (Array (TaggedText HighlightedMsgEmbed))
        (WithRpcRef LazyTraceChildren))
  | highlighted
  deriving Inhabited, RpcEncodable

mutual

private partial def HighlightedMsgEmbed.traceChildrenOfMsgEmbed :
    StrictOrLazy
      (Array (TaggedText MsgEmbed))
      (WithRpcRef LazyTraceChildren) →
    StrictOrLazy
      (Array (TaggedText HighlightedMsgEmbed))
      (WithRpcRef LazyTraceChildren)
  | .strict cs => .strict <| cs.map fun c => c.map (.ofMsgEmbed ·)
  | .lazy cs => .lazy cs

private partial def HighlightedMsgEmbed.ofMsgEmbed : MsgEmbed → HighlightedMsgEmbed
  | .expr c => .expr (.ofCodeWithInfos c)
  | .goal g => .goal g
  | .widget wi alt => .widget wi <| alt.map (.ofMsgEmbed ·)
  | .trace indent cls msg collapsed children =>
    let msg := msg.map (.ofMsgEmbed ·)
    let children := traceChildrenOfMsgEmbed children
    .trace indent cls msg collapsed children

end

abbrev HighlightedInteractiveMessage := TaggedText HighlightedMsgEmbed

private def HighlightedInteractiveMessage.ofInteractiveMessage (msg : InteractiveMessage) :
    HighlightedInteractiveMessage :=
  msg.map (.ofMsgEmbed ·)

private def highlightInteractiveMessageWithExprs (query : String) (msg : InteractiveMessage) :
    HighlightedInteractiveMessage × Bool :=
  highlightTaggedText query msg .highlighted toText go
where
  toText : MsgEmbed → String
    | .expr tt => tt.stripTags
    | _        => ""
  go e _ := do
    match e with
    | .expr tt =>
      let tt ← highlightTaggedText.go (tt := tt) .highlighted fun i _ => pure <| .subexpr i
      return .expr tt
    | e =>
      pure <| .ofMsgEmbed e

variable (query : String) (indent : Nat) in
private partial def unfoldMessageDataTracesContaining (msg : MessageData) (nctx : NamingContext) (ctx? : Option MessageDataContext) : BaseIO (MessageData × Bool) := do
  -- We currently only support `.trace` trees.
  match msg with
  | .trace data traceMsg children =>
    let unfolded ← children.mapM (unfoldMessageDataTracesContaining · nctx ctx?)
    let children := unfolded.map (·.1)
    let anyUnfolded := unfolded.any (·.2)
    if anyUnfolded then
      return (.trace { data with collapsed := false } traceMsg children, true)
    let fmt ← traceMsg.formatAux nctx ctx?
    let s := fmt.pretty (indent := indent)
    if contains query s then
      return (.trace { data with collapsed := false } traceMsg children, true)
    return (.trace data traceMsg children, false)
  | .withContext ctx msg =>
    let (msg, unfolded) ← unfoldMessageDataTracesContaining msg nctx ctx
    return (.withContext ctx msg, unfolded)
  | .withNamingContext nctx msg =>
    let (msg, unfolded) ← unfoldMessageDataTracesContaining msg nctx ctx?
    return (.withNamingContext nctx msg, unfolded)
  | .tagged tag msg =>
    let (msg, unfolded) ← unfoldMessageDataTracesContaining msg nctx ctx?
    return (.tagged tag msg, unfolded)
  | _ =>
    return (msg, false)

private structure Highlighted where
  msg : HighlightedInteractiveMessage
  isHighlighted : Bool
  isTrace : Bool

variable (query : String) in
private partial def highlightMatchesAux (msg : InteractiveMessage) :
    IO Highlighted := do
  match msg with
  | .tag (.trace indent cls msg collapsed children) a => do
    let a : HighlightedInteractiveMessage := .ofInteractiveMessage a
    let (msg, isMsgHighlighted) := highlightInteractiveMessageWithExprs query msg
    let unchangedChildren := Thunk.mk fun _ =>
      let children := HighlightedMsgEmbed.traceChildrenOfMsgEmbed children
      let trace := .trace indent cls msg collapsed children
      { msg := .tag trace a, isHighlighted := isMsgHighlighted, isTrace := true }
    let expandedChildren children :=
      let trace := .trace indent cls msg false (.strict children)
      { msg := .tag trace a, isHighlighted := true, isTrace := true }
    match children with
    | .strict children =>
      let highlighted ← children.mapM (highlightMatchesAux ·)
      let anyHighlighted := highlighted.any (·.2)
      let children := highlighted.map (·.1)
      if ! anyHighlighted then
        return unchangedChildren.get
      return expandedChildren children
    | .lazy c => do
      let indent := c.val.indent
      let unfolded ← c.val.children.mapM fun childRef =>
        let child := childRef.val
        let nctx := { currNamespace := Name.anonymous, openDecls := [] }
        unfoldMessageDataTracesContaining query indent child nctx none
      let anyUnfolded := unfolded.any (·.2)
      let children := unfolded.map (·.1)
      if ! anyUnfolded then
        return unchangedChildren.get
      let children ← children.mapM (msgToInteractive · true indent)
      let highlighted ← children.mapM highlightMatchesAux
      let children := highlighted.map (·.1)
      return expandedChildren children
  | .append as =>
    let highlighted ← as.mapM highlightMatchesAux
    let anyHighlighted := highlighted.any (·.isHighlighted)
    let anyTrace := highlighted.any (·.isTrace)
    let as := highlighted.map (·.msg)
    if ! anyTrace then
      let (msg, isHighlighted) := highlightInteractiveMessageWithExprs query msg
      return { msg, isHighlighted, isTrace := false }
    return { msg := .append as, isHighlighted := anyHighlighted, isTrace := true }
  | msg =>
    let (msg, isHighlighted) := highlightInteractiveMessageWithExprs query msg
    return { msg, isHighlighted, isTrace := false }

structure HighlightMatchesParams where
  query : String
  msg : InteractiveMessage
  deriving RpcEncodable

def highlightMatches (params : HighlightMatchesParams) : RequestM (RequestTask HighlightedInteractiveMessage) :=
  RequestM.pureTask do
    let r ← highlightMatchesAux params.query params.msg
    return r.msg

builtin_initialize registerBuiltinRpcProcedure ``highlightMatches _ _ highlightMatches

end Lean.Widget
