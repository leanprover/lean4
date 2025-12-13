/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich, Wojciech Nawrocki
-/
module

prelude
public import Lean.Widget
import Lean.Server.FileWorker.WidgetRequests
public import Lean.Server.GoTo

public section
open Lean
open Lean.Lsp
open Lean.JsonRpc

/-!
Runner for `tests/lean/interactive` server tests. Put here to avoid repeated elaboration overhead
per test.
-/

namespace Lean.Server.Test.Runner

namespace Client

/- Client-side types for showing interactive goals. -/

structure NormalizeState where
  freshPtr  : USize := 0
  knownPtrs : Std.TreeMap USize USize := {}

abbrev NormalizeM α := StateM NormalizeState α

def NormalizeM.run (x : NormalizeM α) (s : NormalizeState) : α := StateT.run' x s

def normalizedRef (ref : RpcRef) : NormalizeM RpcRef := do
  let ptr ← modifyGet fun s =>
    if let some ptr := s.knownPtrs.get? ref.p then
      (ptr, s)
    else
      (s.freshPtr, { s with
        freshPtr := s.freshPtr + 1
        knownPtrs := s.knownPtrs.insert ref.p s.freshPtr
      })
  return ⟨ptr⟩

structure SubexprInfo where
  info : RpcRef
  subexprPos : String
  diffStatus? : Option String
  deriving FromJson, ToJson

def SubexprInfo.normalize (i : SubexprInfo) : NormalizeM SubexprInfo := do
  return { i with
    info := ← normalizedRef i.info
  }

structure Hyp where
  type : Widget.TaggedText SubexprInfo
  names : Array String
  fvarIds : Array FVarId
  val? : Option (Widget.TaggedText SubexprInfo)
  isInstance? : Option Bool := none
  isType? : Option Bool := none
  isInserted? : Option Bool
  isRemoved? : Option Bool
  deriving FromJson, ToJson

def Hyp.normalize (h : Hyp) : NormalizeM Hyp := do
  return { h with
    type := ← h.type.mapM (·.normalize)
    fvarIds := #[]
    val? := ← h.val?.mapM (fun val => val.mapM (·.normalize))
  }

structure InteractiveGoalCore where
  hyps : Array Hyp
  type : Widget.TaggedText SubexprInfo
  ctx  : Lsp.RpcRef
  deriving FromJson, ToJson

def InteractiveGoalCore.normalize (g : InteractiveGoalCore) : NormalizeM InteractiveGoalCore := do
  return { g with
    hyps := ← g.hyps.mapM (·.normalize)
    type := ← g.type.mapM (·.normalize)
    ctx := ← normalizedRef g.ctx
  }

structure InteractiveGoal extends InteractiveGoalCore where
  userName? : Option String
  goalPrefix : String
  mvarId : MVarId
  isInserted?: Option Bool := none
  isRemoved?: Option Bool := none
  deriving FromJson, ToJson

def InteractiveGoal.normalize (goal : InteractiveGoal) : NormalizeM InteractiveGoal := do
  return { goal with
    mvarId := { name := .anonymous }
    toInteractiveGoalCore := ← goal.toInteractiveGoalCore.normalize
  }

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving FromJson, ToJson

def InteractiveGoals.normalize (gs : InteractiveGoals) : NormalizeM InteractiveGoals := do
  return {
    goals := ← gs.goals.mapM (·.normalize)
  }

structure InteractiveTermGoal extends InteractiveGoalCore where
  range : Lsp.Range
  term : Lsp.RpcRef
  deriving FromJson, ToJson

def InteractiveTermGoal.normalize (g : InteractiveTermGoal) : NormalizeM InteractiveTermGoal := do
  return { g with
    term := ← normalizedRef g.term
    toInteractiveGoalCore := ← g.toInteractiveGoalCore.normalize
  }

structure WidgetInstance where
  id : Name
  javascriptHash : UInt64
  props : Json
  deriving FromJson, ToJson

inductive StrictOrLazy (α β : Type) : Type
  | strict : α → StrictOrLazy α β
  | lazy : β → StrictOrLazy α β
  deriving FromJson, ToJson

inductive MsgEmbed where
  | expr : Widget.TaggedText SubexprInfo → MsgEmbed
  | goal : InteractiveGoal → MsgEmbed
  | widget (wi : WidgetInstance) (alt : Widget.TaggedText MsgEmbed)
  | trace (indent : Nat) (cls : Name) (msg : Widget.TaggedText MsgEmbed) (collapsed : Bool)
    (children : StrictOrLazy (Array (Widget.TaggedText MsgEmbed)) Lsp.RpcRef)
  deriving FromJson, ToJson

partial def MsgEmbed.normalize (m : MsgEmbed) : NormalizeM MsgEmbed := do
  match m with
  | .expr e => return .expr <| ← e.mapM (·.normalize)
  | .goal g => return .goal <| ← g.normalize
  | .widget wi alt => return .widget wi <| ← alt.mapM (·.normalize)
  | .trace ident cls msg collapsed children =>
    let msg ← msg.mapM (·.normalize)
    let children ← do
      match children with
      | .lazy childrenRef => pure <| .lazy childrenRef
      | .strict children => pure <| .strict <| ← children.mapM fun child => child.mapM (·.normalize)
    return .trace ident cls msg collapsed children

abbrev InteractiveDiagnostic := Lsp.DiagnosticWith (Widget.TaggedText MsgEmbed)

def InteractiveDiagnostic.normalize (d : InteractiveDiagnostic) : InteractiveDiagnostic :=
  { d with
    message := d.message.mapM MsgEmbed.normalize |>.run {}
  }

def normalizeInteractiveDiagnostics (diags : Array InteractiveDiagnostic) :
    Array InteractiveDiagnostic :=
  -- Sort diagnostics by range and message to erase non-determinism in the order of diagnostics
  -- induced by parallelism. This isn't complete, but it will hopefully be plenty for all tests.
  let sorted := diags.map (·.normalize) |>.toList.mergeSort fun d1 d2 =>
    compare d1.fullRange d2.fullRange |>.then (compare d1.message.stripTags d2.message.stripTags) |>.isLE
  sorted.toArray

structure InfoPopup where
  type : Option (Widget.TaggedText SubexprInfo)
  exprExplicit : Option (Widget.TaggedText SubexprInfo)
  doc : Option String
  deriving FromJson, ToJson

def InfoPopup.normalize (p : InfoPopup) : InfoPopup :=
  NormalizeM.run (s := {}) do
    return { p with
      type := ← p.type.mapM (fun type => type.mapM (·.normalize))
      exprExplicit := ← p.exprExplicit.mapM (fun exprExplicit => exprExplicit.mapM (·.normalize))
    }

structure GetGoToLocationParams where
  kind : GoToKind
  info : RpcRef
  deriving FromJson, ToJson

structure HighlightMatchesParams where
  query : String
  msg : Widget.TaggedText MsgEmbed
  deriving FromJson, ToJson

inductive HighlightedSubexprInfo where
  | subexpr (info : SubexprInfo)
  | highlighted
  deriving FromJson, ToJson

def HighlightedSubexprInfo.normalize : HighlightedSubexprInfo → NormalizeM HighlightedSubexprInfo
  | .highlighted => pure .highlighted
  | .subexpr i => return .subexpr <| ← i.normalize

inductive HighlightedMsgEmbed where
  | expr : Widget.TaggedText HighlightedSubexprInfo → HighlightedMsgEmbed
  | goal : Client.InteractiveGoal → HighlightedMsgEmbed
  | widget (wi : Client.WidgetInstance) (alt : Widget.TaggedText HighlightedMsgEmbed)
  | trace (indent : Nat) (cls : Name) (msg : Widget.TaggedText HighlightedMsgEmbed) (collapsed : Bool)
      (children : StrictOrLazy
        (Array (Widget.TaggedText HighlightedMsgEmbed))
        Lsp.RpcRef)
  | highlighted
  deriving FromJson, ToJson

partial def HighlightedMsgEmbed.normalize (m : HighlightedMsgEmbed) : NormalizeM HighlightedMsgEmbed := do
  match m with
  | .expr e => return .expr <| ← e.mapM (·.normalize)
  | .goal g => return .goal <| ← g.normalize
  | .widget wi alt => return .widget wi <| ← alt.mapM (·.normalize)
  | .trace ident cls msg collapsed children =>
    let msg ← msg.mapM (·.normalize)
    let children ← do
      match children with
      | .lazy childrenRef => pure <| .lazy childrenRef
      | .strict children => pure <| .strict <| ← children.mapM fun child => child.mapM (·.normalize)
    return .trace ident cls msg collapsed children
  | .highlighted => return .highlighted

end Client

/-! Test-only instances -/

instance : FromJson Widget.PanelWidgetInstance where
  fromJson? j := do
    let id ← j.getObjValAs? Name "id"
    let javascriptHash ← j.getObjValAs? UInt64 "javascriptHash"
    let props ← j.getObjVal? "props"
    let range? ← j.getObjValAs? (Option Lsp.Range) "range"
    return { id, javascriptHash, props := pure props, range? }

deriving instance FromJson for Widget.GetWidgetsResponse

def _root_.Lean.Widget.GetWidgetsResponse.debugJson (r : Widget.GetWidgetsResponse) : Json :=
  Json.mkObj [
    ("widgets", Json.arr (r.widgets.map fun w =>
      Json.mkObj [
        ("id", toJson w.id),
        ("javascriptHash", toJson w.javascriptHash),
        ("props", w.props.run' {}),
        ("range", toJson w.range?),
      ])
    )
  ]

open Std.Internal.Parsec in
open Std.Internal.Parsec.String in
def word : Parser String :=
  many1Chars <| digit <|> asciiLetter <|> pchar '_'

open Std.Internal.Parsec in
open Std.Internal.Parsec.String in
def ident : Parser Name := do
  let head ← word
  let xs ← many1 (pchar '.' *> word)
  return xs.foldl .str $ .mkSimple head

def patchUri (s : String) : IO String := do
  let some path := System.Uri.fileUriToPath? s
    | return s
  let path ←
    try
      IO.FS.realPath path
    catch _ =>
      return s
  let c := path.components.toArray
  if let some srcIdx := c.findIdx? (· == "src") then
    if ! c[srcIdx + 1]?.any (fun dir => dir == "Init" || dir == "Lean" || dir == "Std") then
      return s
    let c := c.drop <| srcIdx
    let path := System.mkFilePath c.toList
    return System.Uri.pathToUri path
  if let some testIdx := c.findIdx? (· == "tests") then
    let c := c.drop <| testIdx
    let path := System.mkFilePath c.toList
    return System.Uri.pathToUri path
  else
    return s

partial def patchUris : Json → IO Json
  | .null =>
    return .null
  | .bool b =>
    return .bool b
  | .num n =>
    return .num n
  | .arr elems =>
    return .arr <| ← elems.mapM patchUris
  | .obj kvPairs =>
    return .obj <| ← kvPairs.foldlM (init := ∅) fun acc k v =>
      return acc.insert k (← patchUris v)
  | .str s =>
    patchUri s

def printOutputLn (j : Json) : IO Unit := do
  IO.eprintln (← patchUris j)

structure RunnerState where
  uri : DocumentUri
  -- Whether we have waited for the server via `sync/collectDiagnostics/waitFor` since the last
  -- change; we should only send out further changes when we are in such a deterministic state.
  synced : Bool
  rpcSessionId : Option UInt64
  lineNo : Nat
  lastActualLineNo : Nat
  pos : Lsp.Position
  method : String
  params : String
  versionNo : Nat
  requestNo : Nat

abbrev RunnerM := StateT RunnerState Ipc.IpcM

def RunnerM.run (act : RunnerM α) (init : RunnerState) : Ipc.IpcM Unit :=
  discard <| StateT.run act init

def advanceRequestNo : RunnerM Unit :=
  modify fun s => { s with
    requestNo := s.requestNo + 1
  }

def advanceVersionNo : RunnerM Unit :=
  modify fun s => { s with
    versionNo := s.versionNo + 1
  }

def setSynced : RunnerM Unit :=
  modify fun s => { s with
    synced := true
  }

def setDesynced : RunnerM Unit :=
  modify fun s => { s with
    synced := false
  }

def request (method : String) [ToJson α] (p : α) (β : Type) [FromJson β] : RunnerM β := do
  let s ← get
  Ipc.writeRequest ⟨s.requestNo, method, p⟩
  advanceRequestNo
  let r ← Ipc.readResponseAs s.requestNo β
  return r.result

def requestWithLoggedResponse (method : String) [ToJson α] (p : α)
    (β : Type) [FromJson β] [ToJson β] (logParam := true) : RunnerM β := do
  if logParam then
    printOutputLn (toJson p)
  let r ← request method p β
  printOutputLn (toJson r)
  return r

def logResponse (method : String) [ToJson α] (p : α)
  (β : Type := Json) [FromJson β] [ToJson β] (logParam := true) : RunnerM Unit := do
  discard <| requestWithLoggedResponse method p β logParam

def rpcRequest (method : Name) [ToJson α] (p : α) (β : Type) [FromJson β] : RunnerM β := do
  if (← get).rpcSessionId.isNone then
    let connectParams := RpcConnectParams.mk (← get).uri
    let r ← request "$/lean/rpc/connect" connectParams RpcConnected
    modify fun s => { s with
      rpcSessionId := r.sessionId
    }
  let callParams : RpcCallParams := {
    params := toJson p
    textDocument := { uri := (← get).uri }
    position := (← get).pos,
    sessionId := (← get).rpcSessionId.get!,
    method := method
  }
  request "$/lean/rpc/call" callParams β

def rpcRequestWithLoggedResponse (method : Name) [ToJson α] (p : α)
    (β : Type) [FromJson β] [ToJson β] (logParam := true) (normalize : β → Client.NormalizeM β := pure) : RunnerM β := do
  if logParam then
    printOutputLn (toJson p)
  let r ← rpcRequest method p β
  let r := normalize r |>.run {}
  printOutputLn (toJson r)
  return r

def logRpcResponse (method : Name) [ToJson α] (p : α)
  (β : Type := Json) [FromJson β] [ToJson β] (logParam := true) (normalize : β → Client.NormalizeM β := pure) : RunnerM Unit := do
  discard <| rpcRequestWithLoggedResponse method p β logParam normalize

def reset : RunnerM Unit := modify fun s => { s with
  synced := true
  lineNo := 0
  lastActualLineNo := 0
  versionNo := 2
  rpcSessionId := none
}

def skipLineWithDirective : RunnerM Unit := modify fun s => { s with
  lineNo := s.lineNo + 1
}

def skipLineWithoutDirective : RunnerM Unit := modify fun s => { s with
  lastActualLineNo := s.lineNo
  lineNo := s.lineNo + 1
}

partial def expandTraces (msg : Client.MsgEmbed) : RunnerM Client.MsgEmbed := do
  match msg with
  | .trace indent cls msg _ children =>
    let children ←
      match children with
      | .lazy childrenRef =>
        rpcRequest `Lean.Widget.lazyTraceChildrenToInteractive childrenRef (Array (Widget.TaggedText Client.MsgEmbed))
      | .strict children =>
        pure children
    let children ← children.mapM fun child =>
      child.mapM expandTraces
    return .trace indent cls msg false (.strict children)
  | _ =>
    return msg

def processEdit : RunnerM Unit := do
  let s ← get
  if ! s.synced then
    throw <| IO.userError s!"cannot use '{s.method}' without syncing first"
  let (delete, insert) ←
    match s.method with
    | "delete" => pure (s.params, "\"\"")
    | "insert" => pure ("\"\"", s.params)
    | "change" =>
      -- TODO: allow spaces in strings
      let [delete, insert] := s.params.split ' ' |>.toStringList
        | throw <| IO.userError s!"expected two arguments in {s.params}"
      pure (delete, insert)
    | _ => unreachable!
  let some delete := Syntax.decodeStrLit delete
    | throw <| IO.userError s!"failed to parse {delete}"
  let some insert := Syntax.decodeStrLit insert
    | throw <| IO.userError s!"failed to parse {insert}"
  let params : DidChangeTextDocumentParams := {
    textDocument := {
      uri      := s.uri
      version? := s.versionNo
    }
    contentChanges := #[
      TextDocumentContentChangeEvent.rangeChange {
        start := s.pos
        «end» := { s.pos with character := s.pos.character + delete.length }
      } insert
    ]
  }
  let params := toJson params
  Ipc.writeNotification ⟨"textDocument/didChange", params⟩
  advanceVersionNo
  setDesynced

def processCollectDiagnostics : RunnerM Unit := do
  let s ← get
  if let some diags ← Ipc.collectDiagnostics s.requestNo s.uri (s.versionNo - 1) then
    printOutputLn (toJson diags.param)
  advanceRequestNo
  setSynced

def processWaitForILeans : RunnerM Unit := do
  let s ← get
  let _ ← Ipc.waitForILeans s.requestNo s.uri (s.versionNo - 1)
  advanceRequestNo

def processSync : RunnerM Unit := do
  let s ← get
  let _ ← Ipc.collectDiagnostics s.requestNo s.uri (s.versionNo - 1)
  advanceRequestNo
  setSynced

def processWaitFor : RunnerM Unit := do
  let s ← get
  let _ ← Ipc.waitForMessage s.params
  setSynced

def processCodeAction : RunnerM Unit := do
  let s ← get
  let params : CodeActionParams := {
    textDocument := { uri := s.uri },
    range := ⟨s.pos, s.pos⟩
  }
  let r ← requestWithLoggedResponse "textDocument/codeAction" params (Array CodeAction)
  for x in r do
    if x.data?.isNone then
      continue
    IO.eprintln s!"Resolution of {x.title}:"
    logResponse "codeAction/resolve" x (logParam := false)

def processInteractiveDiagnostics : RunnerM Unit := do
  let isExpandTraces := (← get).params == "expandTraces"
  let highlightMatchesQuery? := (← get).params.dropPrefix? "highlightMatches:"
  let params : Widget.GetInteractiveDiagnosticsParams := {
    lineRange? := some ⟨0, (← get).pos.line + 1⟩
  }
  printOutputLn (toJson params)
  let r ← rpcRequest `Lean.Widget.getInteractiveDiagnostics params (Array Client.InteractiveDiagnostic)
  let r := Client.normalizeInteractiveDiagnostics r
  if isExpandTraces then
    let r : Array Client.InteractiveDiagnostic ← r.mapM fun diag => do
      return { diag with
        message := ← diag.message.mapM expandTraces
      }
    let r := r.map (·.normalize)
    printOutputLn (toJson r)
  else if let some highlightMatchesQuery := highlightMatchesQuery? then
    for diag in r do
      let params := {
        query := highlightMatchesQuery.toString
        msg := diag.message
        : Client.HighlightMatchesParams
      }
      logRpcResponse `Lean.Widget.highlightMatches params (β := Widget.TaggedText Client.HighlightedMsgEmbed)
        (normalize := fun msg => msg.mapM (·.normalize))
  else
    printOutputLn (toJson (r.map (·.normalize)))


def processGoals : RunnerM Unit := do
  let withPopups := (← get).params == "withPopups"
  let withGoToLoc := (← get).params == "withGoToLoc"
  let params : Lsp.PlainGoalParams := {
    textDocument := { uri := (← get).uri }
    position := (← get).pos,
  }
  let r ← rpcRequestWithLoggedResponse `Lean.Widget.getInteractiveGoals params Client.InteractiveGoals
    (normalize := Client.InteractiveGoals.normalize)
  if withPopups then
    let interactiveTerms := r.goals.flatMap fun goal =>
      goal.hyps.map (fun h => (" ".intercalate h.names.toList, h.type)) |>.push ("goal", goal.type)
    for (termName, interactiveTerm) in interactiveTerms do
      IO.eprintln s!"Popups for type of {termName}:"
      interactiveTerm.forM fun i subtree => do
        IO.eprintln s!"Popup for {subtree.stripTags}:"
        logRpcResponse `Lean.Widget.InteractiveDiagnostics.infoToInteractive i.info (β := Client.InfoPopup)
          (normalize := fun p => pure p.normalize)
  if withGoToLoc then
    let interactiveTerms := r.goals.flatMap fun goal =>
      goal.hyps.map (fun h => (" ".intercalate h.names.toList, h.type)) |>.push ("goal", goal.type)
    for (termName, interactiveTerm) in interactiveTerms do
      IO.eprintln s!"GoToLoc responses for type of {termName}:"
      interactiveTerm.forM fun i subtree => do
        IO.eprintln s!"GoToLoc response for {subtree.stripTags}:"
        let params : Client.GetGoToLocationParams := {
          kind := .definition
          info := i.info
        }
        logRpcResponse `Lean.Widget.getGoToLocation params

def processTermGoal : RunnerM Unit := do
  let params : Lsp.PlainTermGoalParams := {
    textDocument := { uri := (← get).uri }
    position := (← get).pos,
  }
  logRpcResponse `Lean.Widget.getInteractiveTermGoal params (β := Option Client.InteractiveTermGoal)
    (normalize := fun g? => g?.mapM (·.normalize))

def processWidgets : RunnerM Unit := do
  let r ← rpcRequest `Lean.Widget.getWidgets (← get).pos Lean.Widget.GetWidgetsResponse
  printOutputLn r.debugJson
  for w in r.widgets do
    let params : Lean.Widget.GetWidgetSourceParams := { pos := (← get).pos, hash := w.javascriptHash }
    logRpcResponse `Lean.Widget.getWidgetSource params

def processCompletion : RunnerM Unit := do
  let p : CompletionParams := {
    textDocument := { uri := (← get).uri }
    position := (← get).pos
  }
  let r ← requestWithLoggedResponse "textDocument/completion" p CompletionList
  for i in r.items do
    if i.data?.isNone then
      continue
    IO.eprintln s!"Resolution of {i.label}:"
    logResponse "completionItem/resolve" i (logParam := false)

def processIncomingCallHierarchy : RunnerM Unit := do
  let s ← get
  let (callHierarchy?, callHierarchyRequestNo) ← Ipc.expandIncomingCallHierarchy s.requestNo s.uri s.pos
  printOutputLn (toJson callHierarchy?)
  set <| { s with requestNo := callHierarchyRequestNo }

def processOutgoingCallHierarchy : RunnerM Unit := do
  let s ← get
  let (callHierarchy?, callHierarchyRequestNo) ← Ipc.expandOutgoingCallHierarchy s.requestNo s.uri s.pos
  printOutputLn (toJson callHierarchy?)
  set <| { s with requestNo := callHierarchyRequestNo }

def processReferences : RunnerM Unit := do
  let p : ReferenceParams := {
    textDocument := { uri := (← get).uri }
    position := (← get).pos
    context := { includeDeclaration := true }
  }
  logResponse "textDocument/references" p

def processSymbols : RunnerM Unit := do
  let p : WorkspaceSymbolParams := {
    query := (← get).params
  }
  logResponse "workspace/symbol" p

def processModuleHierarchyImports : RunnerM Unit := do
  let s ← get
  let (moduleHierarchy?, moduleHierarchyRequestNo) ← Ipc.expandModuleHierarchyImports s.requestNo s.uri
  printOutputLn (toJson moduleHierarchy?)
  set <| { s with requestNo := moduleHierarchyRequestNo }

def processModuleHierarchyImportedBy : RunnerM Unit := do
  let s ← get
  let (moduleHierarchy?, moduleHierarchyRequestNo) ← Ipc.expandModuleHierarchyImportedBy s.requestNo s.uri
  printOutputLn (toJson moduleHierarchy?)
  set <| { s with requestNo := moduleHierarchyRequestNo }

def processInlayHints : RunnerM Unit := do
  let p : InlayHintParams := {
    textDocument := { uri := (← get).uri }
    range := { start := ⟨0, 0⟩, «end» := (← get).pos }
  }
  logResponse "textDocument/inlayHint" p

def processGenericRequest : RunnerM Unit := do
  let s ← get
  let Except.ok params := Json.parse s.params
    | throw <| IO.userError s!"failed to parse {s.params}"
  let params := params.setObjVal! "textDocument" (toJson { uri := s.uri : TextDocumentIdentifier })
  -- TODO: correctly compute in presence of Unicode
  let params := params.setObjVal! "position" (toJson s.pos)
  logResponse s.method params

def processDirective (ws directive : String) (directiveTargetLineNo : Nat) : RunnerM Unit := do
  let directive := directive.drop 1
  let colon := directive.find ':'
  let method := directive.sliceTo colon |>.trimAscii |>.copy
  -- TODO: correctly compute in presence of Unicode
  let directiveTargetColumn := ws.rawEndPos + "--"
  let pos : Lsp.Position := { line := directiveTargetLineNo, character := directiveTargetColumn.byteIdx }
  let params :=
    if h : ¬colon.IsAtEnd then
      directive.sliceFrom (colon.next h) |>.trimAscii.copy
    else "{}"
  modify fun s => { s with pos, method, params }
  match method with
  -- `delete: "foo"` deletes the given string's number of characters at the given position.
  -- We do NOT check currently that the text at this position is indeed that string.
  -- `insert: "foo"` inserts the given string at the given position.
  -- `change: "foo" "bar"` is like `delete: "foo"` followed by `insert: "bar"` in one atomic step.
  | "delete" | "insert" | "change" => processEdit
  | "collectDiagnostics" => processCollectDiagnostics
  | "waitForILeans" => processWaitForILeans
  | "sync" => processSync
  | "waitFor" => processWaitFor
  | "codeAction" => processCodeAction
  | "interactiveDiagnostics" => processInteractiveDiagnostics
  | "goals" => processGoals
  | "termGoal" => processTermGoal
  | "widgets" => processWidgets
  | "completion" => processCompletion
  | "incomingCallHierarchy" => processIncomingCallHierarchy
  | "outgoingCallHierarchy" => processOutgoingCallHierarchy
  | "references" => processReferences
  | "symbols" => processSymbols
  | "moduleHierarchyImports" => processModuleHierarchyImports
  | "moduleHierarchyImportedBy" => processModuleHierarchyImportedBy
  | "inlayHints" => processInlayHints
  | _ => processGenericRequest

def processLine (line : String) : RunnerM Unit := do
  let [ws, directive] := line.split "--" |>.toStringList
    | skipLineWithoutDirective
      return
  let directiveTargetLineNo ←
    match directive.front with
    | 'v' => pure <| (← get).lineNo + 1  -- TODO: support subsequent 'v'... or not
    | '^' => pure <| (← get).lastActualLineNo
    | _ =>
      skipLineWithoutDirective
      return
  processDirective ws directive directiveTargetLineNo
  skipLineWithDirective


partial def main (args : List String) : IO Unit := do
  let args := args.toArray
  let isProject := args[0]?.any (· == "-p")
  let (ipcCmd, ipcArgs) :=
    if isProject then
      ("lake", #["serve", "--", "-DstderrAsMessages=false", "-Dexperimental.module=true"])
    else
      ("lean", #["--server", "-DstderrAsMessages=false", "-Dexperimental.module=true"])
  let path := if args.size == 1 then args[0]! else args[1]!
  let uri := s!"file:///{path}"
  -- We want `dbg_trace` tactics to write directly to stderr instead of being caught in reuse
  Ipc.runWith ipcCmd ipcArgs do
    let initializationOptions? := some {
      hasWidgets? := some true
      logCfg? := none
    }
    let capabilities := {
      textDocument? := some {
        completion? := some {
          completionItem? := some {
            insertReplaceSupport? := true
          }
        }
      }
      lean? := some {
        silentDiagnosticSupport? := some true
      }
    }
    Ipc.writeRequest ⟨0, "initialize", { initializationOptions?, capabilities : InitializeParams }⟩
    let _ ← Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    let text ← IO.FS.readFile path
    let init : RunnerState := {
      uri
      synced := true
      versionNo := 2
      rpcSessionId := none
      lineNo := 0
      lastActualLineNo := 0
      pos := ⟨0, 0⟩
      method := ""
      params := ""
      requestNo := 1
    }
    RunnerM.run (init := init) do
      for text in text.split "-- RESET" do
        Ipc.writeNotification ⟨"textDocument/didOpen", {
          textDocument := { uri := uri, languageId := "lean", version := 1, text := text.copy } : DidOpenTextDocumentParams }⟩
        reset
        for line in text.split '\n' do
          processLine line.copy
        let _ ← Ipc.collectDiagnostics (← get).requestNo uri ((← get).versionNo - 1)
        advanceRequestNo
        Ipc.writeNotification ⟨"textDocument/didClose", {
          textDocument := { uri } : DidCloseTextDocumentParams }⟩

      Ipc.shutdown (← get).requestNo
      discard <| Ipc.waitForExit
