/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich, Wojciech Nawrocki
-/
module

prelude
public import Lean.Data.Lsp
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

structure SubexprInfo where
  info : RpcRef
  subexprPos : String
  diffStatus? : Option String
  deriving FromJson, ToJson

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

def Hyp.normalize (h : Hyp) : Hyp := { h with
  fvarIds := #[]
}

structure InteractiveGoalCore where
  hyps : Array Hyp
  type : Widget.TaggedText SubexprInfo
  ctx  : Lsp.RpcRef
  deriving FromJson, ToJson

def InteractiveGoalCore.normalize (g : InteractiveGoalCore) : InteractiveGoalCore := { g with
  hyps := g.hyps.map (·.normalize)
}

structure InteractiveGoal extends InteractiveGoalCore where
  userName? : Option String
  goalPrefix : String
  mvarId : MVarId
  isInserted?: Option Bool := none
  isRemoved?: Option Bool := none
  deriving FromJson, ToJson

def InteractiveGoal.normalize (goal : InteractiveGoal) : InteractiveGoal := { goal with
  mvarId := { name := .anonymous }
  toInteractiveGoalCore := goal.toInteractiveGoalCore.normalize
}

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving FromJson, ToJson

def InteractiveGoals.normalize (gs : InteractiveGoals) : InteractiveGoals := {
  goals := gs.goals.map (·.normalize)
}

structure InteractiveTermGoal extends InteractiveGoalCore where
  range : Lsp.Range
  term : Lsp.RpcRef
  deriving FromJson, ToJson

def InteractiveTermGoal.normalize (g : InteractiveTermGoal) : InteractiveTermGoal := { g with
  toInteractiveGoalCore := g.toInteractiveGoalCore.normalize
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

partial def MsgEmbed.normalize : MsgEmbed → MsgEmbed
  | .expr e => .expr e
  | .goal g => .goal g.normalize
  | .widget wi alt => .widget wi <| alt.map (·.normalize)
  | .trace ident cls msg collapsed children =>
    let msg := msg.map (·.normalize)
    let children :=
      match children with
      | .lazy childrenRef => .lazy childrenRef
      | .strict children => .strict <| children.map fun child => child.map (·.normalize)
    .trace ident cls msg collapsed children

abbrev InteractiveDiagnostic := Lsp.DiagnosticWith (Widget.TaggedText MsgEmbed)

def InteractiveDiagnostic.normalize (d : InteractiveDiagnostic) : InteractiveDiagnostic := { d with
  message := d.message.map (·.normalize)
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

partial def HighlightedMsgEmbed.normalize : HighlightedMsgEmbed → HighlightedMsgEmbed
  | .expr e => .expr e
  | .goal g => .goal g.normalize
  | .widget wi alt => .widget wi <| alt.map (·.normalize)
  | .trace ident cls msg collapsed children =>
    let msg := msg.map (·.normalize)
    let children :=
      match children with
      | .lazy childrenRef => .lazy childrenRef
      | .strict children => .strict <| children.map fun child => child.map (·.normalize)
    .trace ident cls msg collapsed children
  | .highlighted => .highlighted

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

def patchUri (s : String) : String := Id.run do
  let some path := System.Uri.fileUriToPath? s
    | return s
  let c := path.components.toArray
  let some srcIdx := c.findIdx? (· == "src")
    | return s
  if ! c[srcIdx + 1]?.any (fun dir => dir == "Init" || dir == "Lean" || dir == "Std") then
    return s
  let c := c.drop <| srcIdx
  let path := System.mkFilePath c.toList
  return System.Uri.pathToUri path

partial def patchUris : Json → Json
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .arr elems => .arr <| elems.map patchUris
  | .obj kvPairs => .obj <| kvPairs.foldl (init := ∅) fun acc k v => acc.insert k (patchUris v)
  | .str s => patchUri s

def printOutputLn (j : Json) : IO Unit :=
  IO.eprintln (patchUris j)

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
    (β : Type) [FromJson β] [ToJson β] (logParam := true) (normalize : β → β := id) : RunnerM β := do
  if logParam then
    printOutputLn (toJson p)
  let r ← rpcRequest method p β
  printOutputLn (toJson (normalize r))
  return r

def logRpcResponse (method : Name) [ToJson α] (p : α)
  (β : Type := Json) [FromJson β] [ToJson β] (logParam := true) (normalize : β → β := id) : RunnerM Unit := do
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
      let [delete, insert] := s.params.splitOn " "
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
    let r ← r.mapM fun diag => do
      return { diag with
        message := ← diag.message.mapM expandTraces
      }
    let r := r.map (fun d => { d with message := d.message.map Client.MsgEmbed.normalize })
    printOutputLn (toJson r)
  else if let some highlightMatchesQuery := highlightMatchesQuery? then
    for diag in r do
      let params := {
        query := highlightMatchesQuery.toString
        msg := diag.message
        : Client.HighlightMatchesParams
      }
      logRpcResponse `Lean.Widget.highlightMatches params (β := Widget.TaggedText Client.HighlightedMsgEmbed)
        (normalize := fun msg => msg.map (·.normalize))
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
    (normalize := fun g? => g?.map (·.normalize))

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
  let colon := directive.posOf ':'
  let method := directive.extract 0 colon |>.trim
  -- TODO: correctly compute in presence of Unicode
  let directiveTargetColumn := ws.endPos + "--"
  let pos : Lsp.Position := { line := directiveTargetLineNo, character := directiveTargetColumn.byteIdx }
  let params := if colon < directive.endPos then directive.extract (colon + ':') directive.endPos |>.trim else "{}"
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
  | "inlayHints" => processInlayHints
  | _ => processGenericRequest

def processLine (line : String) : RunnerM Unit := do
  let [ws, directive] := line.splitOn "--"
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
  let uri := s!"file:///{args.head!}"
  -- We want `dbg_trace` tactics to write directly to stderr instead of being caught in reuse
  Ipc.runWith (←IO.appPath) #["--server", "-DstderrAsMessages=false"] do
    let initializationOptions? := some {
      editDelay? := none
      hasWidgets? := some true
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

    let text ← IO.FS.readFile args.head!
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
      for text in text.splitOn "-- RESET" do
        Ipc.writeNotification ⟨"textDocument/didOpen", {
          textDocument := { uri := uri, languageId := "lean", version := 1, text := text } : DidOpenTextDocumentParams }⟩
        reset
        for line in text.splitOn "\n" do
          processLine line
        let _ ← Ipc.collectDiagnostics (← get).requestNo uri ((← get).versionNo - 1)
        advanceRequestNo
        Ipc.writeNotification ⟨"textDocument/didClose", {
          textDocument := { uri } : DidCloseTextDocumentParams }⟩

      Ipc.shutdown (← get).requestNo
      discard <| Ipc.waitForExit
