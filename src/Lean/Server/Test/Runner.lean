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
  isInserted?: Option Bool
  isRemoved?: Option Bool
  deriving FromJson, ToJson

structure InteractiveGoalCore where
  hyps : Array Hyp
  type : Widget.TaggedText SubexprInfo
  deriving FromJson, ToJson

structure InteractiveGoal extends InteractiveGoalCore where
  isInserted?: Option Bool := none
  isRemoved?: Option Bool := none
  deriving FromJson, ToJson

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving FromJson, ToJson

structure InteractiveTermGoal extends InteractiveGoalCore where
  range : Lsp.Range
  deriving FromJson, ToJson

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
    (children : StrictOrLazy (Array (Widget.TaggedText MsgEmbed)) Json)
  deriving FromJson, ToJson

abbrev InteractiveDiagnostic := Lsp.DiagnosticWith (Widget.TaggedText MsgEmbed)

def normalizeInteractiveDiagnostics (diags : Array InteractiveDiagnostic) :
    Array InteractiveDiagnostic :=
  -- Sort diagnostics by range and message to erase non-determinism in the order of diagnostics
  -- induced by parallelism. This isn't complete, but it will hopefully be plenty for all tests.
  let sorted := diags.toList.mergeSort fun d1 d2 =>
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
    let mut requestNo : Nat := 1
    for text in text.splitOn "-- RESET" do
      Ipc.writeNotification ⟨"textDocument/didOpen", {
        textDocument := { uri := uri, languageId := "lean", version := 1, text := text } : DidOpenTextDocumentParams }⟩
      -- Whether we have waited for the server via `sync/collectDiagnostics/waitFor` since the last
      -- change; we should only send out further changes when we are in such a deterministic state.
      let mut synced := true
      let mut lineNo := 0
      let mut lastActualLineNo := 0
      let mut versionNo : Nat := 2
      let mut rpcSessionId : Option UInt64 := none
      for line in text.splitOn "\n" do
        match line.splitOn "--" with
        | [ws, directive] =>
          let line ← match directive.front with
            | 'v' => pure <| lineNo + 1  -- TODO: support subsequent 'v'... or not
            | '^' => pure <| lastActualLineNo
            | _ =>
              lastActualLineNo := lineNo
              lineNo := lineNo + 1
              continue
          let directive := directive.drop 1
          let colon := directive.posOf ':'
          let method := directive.extract 0 colon |>.trim
          -- TODO: correctly compute in presence of Unicode
          let column := ws.endPos + "--"
          let pos : Lsp.Position := { line := line, character := column.byteIdx }
          let params := if colon < directive.endPos then directive.extract (colon + ':') directive.endPos |>.trim else "{}"
          match method with
          -- `delete: "foo"` deletes the given string's number of characters at the given position.
          -- We do NOT check currently that the text at this position is indeed that string.
          | "delete"
          -- `insert: "foo"` inserts the given string at the given position.
          | "insert"
          -- `change: "foo" "bar"` is like `delete: "foo"` followed by `insert: "bar"` in one atomic step.
          | "change" =>
            if !synced then
              throw <| IO.userError s!"cannot use '{method}' without syncing first"
            let (delete, insert) ← match method with
              | "delete" => pure (params, "\"\"")
              | "insert" => pure ("\"\"", params)
              | "change" =>
                -- TODO: allow spaces in strings
                let [delete, insert] := params.splitOn " "
                  | throw <| IO.userError s!"expected two arguments in {params}"
                pure (delete, insert)
              | _ => unreachable!
            let some delete := Syntax.decodeStrLit delete
              | throw <| IO.userError s!"failed to parse {delete}"
            let some insert := Syntax.decodeStrLit insert
              | throw <| IO.userError s!"failed to parse {insert}"
            let params : DidChangeTextDocumentParams := {
              textDocument := {
                uri      := uri
                version? := versionNo
              }
              contentChanges := #[TextDocumentContentChangeEvent.rangeChange {
                start := pos
                «end» := { pos with character := pos.character + delete.length }
              } insert]
            }
            let params := toJson params
            Ipc.writeNotification ⟨"textDocument/didChange", params⟩
            synced := false
            -- We don't want to wait for changes to be processed so we can test concurrency
            --let _ ← Ipc.collectDiagnostics requestNo uri versionNo
            requestNo := requestNo + 1
            versionNo := versionNo + 1
          | "collectDiagnostics" =>
            if let some diags ← Ipc.collectDiagnostics requestNo uri (versionNo - 1) then
              printOutputLn (toJson diags.param)
            synced := true
            requestNo := requestNo + 1
          | "waitForILeans" =>
            let _ ← Ipc.waitForILeans requestNo uri (versionNo - 1)
            requestNo := requestNo + 1
          | "sync" =>  -- wait for processing but do not print diagnostics
            let _ ← Ipc.collectDiagnostics requestNo uri (versionNo - 1)
            synced := true
            requestNo := requestNo + 1
          | "waitFor" =>  -- wait specific message text but do not print diagnostics
            let _ ← Ipc.waitForMessage params
            synced := true
          | "codeAction" =>
            let params : CodeActionParams := {
              textDocument := {uri := uri},
              range := ⟨pos, pos⟩
            }
            Ipc.writeRequest ⟨requestNo, "textDocument/codeAction", params⟩
            let r ← Ipc.readResponseAs requestNo (Array CodeAction)
            for x in r.result do
              printOutputLn (toJson x)
            requestNo := requestNo + 1
            for x in r.result do
              if x.data?.isNone then
                continue
              IO.eprintln s!"resolve: {x.title}"
              Ipc.writeRequest ⟨requestNo, "codeAction/resolve", x⟩
              let r ← Ipc.readResponseAs requestNo CodeAction
              printOutputLn (toJson r.result)
              requestNo := requestNo + 1
          | "interactiveDiagnostics" =>
            if rpcSessionId.isNone then
              Ipc.writeRequest ⟨requestNo, "$/lean/rpc/connect",  RpcConnectParams.mk uri⟩
              let r ← Ipc.readResponseAs requestNo RpcConnected
              rpcSessionId := some r.result.sessionId
              requestNo := requestNo + 1
            let params : Widget.GetInteractiveDiagnosticsParams := {
              lineRange? := some ⟨0, pos.line + 1⟩
            }
            let ps : RpcCallParams := {
              params := toJson params
              textDocument := { uri }
              position := pos,
              sessionId := rpcSessionId.get!,
              method := `Lean.Widget.getInteractiveDiagnostics
            }
            Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
            let response ← Ipc.readResponseAs requestNo (Array Client.InteractiveDiagnostic)
            requestNo := requestNo + 1
            printOutputLn (toJson (Client.normalizeInteractiveDiagnostics response.result))
          | "goals" =>
            let withPopups := params == "withPopups"
            let withGoToLoc := params == "withGoToLoc"
            if rpcSessionId.isNone then
              Ipc.writeRequest ⟨requestNo, "$/lean/rpc/connect",  RpcConnectParams.mk uri⟩
              let r ← Ipc.readResponseAs requestNo RpcConnected
              rpcSessionId := some r.result.sessionId
              requestNo := requestNo + 1
            let params : Lsp.PlainGoalParams := {
              textDocument := { uri }
              position := pos,
            }
            let ps : RpcCallParams := {
              params := toJson params
              textDocument := { uri }
              position := pos,
              sessionId := rpcSessionId.get!,
              method := `Lean.Widget.getInteractiveGoals
            }
            Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
            let response ← Ipc.readResponseAs requestNo Client.InteractiveGoals
            requestNo := requestNo + 1
            printOutputLn (toJson response.result)
            if withPopups then
              let interactiveTerms := response.result.goals.flatMap fun goal =>
                goal.hyps.map (fun h => (" ".intercalate h.names.toList, h.type)) |>.push ("goal", goal.type)
              for (termName, interactiveTerm) in interactiveTerms do
                IO.eprintln s!"Popups for type of {termName}:"
                let (_, requestNo') ← StateT.run (s := requestNo) do
                  interactiveTerm.forM fun i subtree => do
                    IO.eprintln s!"Popup for {subtree.stripTags}:"
                    let requestNo : Nat ← get
                    let ps : RpcCallParams := {
                      params := toJson i.info
                      textDocument := { uri }
                      position := pos,
                      sessionId := rpcSessionId.get!,
                      method := `Lean.Widget.InteractiveDiagnostics.infoToInteractive
                    }
                    Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
                    let response ← Ipc.readResponseAs requestNo Client.InfoPopup
                    set <| requestNo + 1
                    printOutputLn (toJson response.result)
                requestNo := requestNo'
            if withGoToLoc then
              let interactiveTerms := response.result.goals.flatMap fun goal =>
                goal.hyps.map (fun h => (" ".intercalate h.names.toList, h.type)) |>.push ("goal", goal.type)
              for (termName, interactiveTerm) in interactiveTerms do
                IO.eprintln s!"GoToLoc responses for type of {termName}:"
                let (_, requestNo') ← StateT.run (s := requestNo) do
                  interactiveTerm.forM fun i subtree => do
                    IO.eprintln s!"GoToLoc response for {subtree.stripTags}:"
                    let requestNo : Nat ← get
                    let params : Client.GetGoToLocationParams := {
                      kind := .definition
                      info := i.info
                    }
                    let ps : RpcCallParams := {
                      params := toJson params
                      textDocument := { uri }
                      position := pos,
                      sessionId := rpcSessionId.get!,
                      method := `Lean.Widget.getGoToLocation
                    }
                    Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
                    let response ← Ipc.readResponseAs requestNo (Array Lsp.LocationLink)
                    set <| requestNo + 1
                    printOutputLn (toJson response.result)
                requestNo := requestNo'
          | "termGoal" =>
            if rpcSessionId.isNone then
              Ipc.writeRequest ⟨requestNo, "$/lean/rpc/connect",  RpcConnectParams.mk uri⟩
              let r ← Ipc.readResponseAs requestNo RpcConnected
              rpcSessionId := some r.result.sessionId
              requestNo := requestNo + 1
            let params : Lsp.PlainTermGoalParams := {
              textDocument := { uri }
              position := pos,
            }
            let ps : RpcCallParams := {
              params := toJson params
              textDocument := { uri }
              position := pos,
              sessionId := rpcSessionId.get!,
              method := `Lean.Widget.getInteractiveTermGoal
            }
            Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
            let response ← Ipc.readResponseAs requestNo Client.InteractiveTermGoal
            requestNo := requestNo + 1
            printOutputLn (toJson response.result)
          | "widgets" =>
            if rpcSessionId.isNone then
              Ipc.writeRequest ⟨requestNo, "$/lean/rpc/connect",  RpcConnectParams.mk uri⟩
              let r ← Ipc.readResponseAs requestNo RpcConnected
              rpcSessionId := some r.result.sessionId
              requestNo := requestNo + 1
            let ps : RpcCallParams := {
              textDocument := {uri := uri},
              position := pos,
              sessionId := rpcSessionId.get!,
              method := `Lean.Widget.getWidgets,
              params := toJson pos,
            }
            Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
            let response ← Ipc.readResponseAs requestNo Lean.Widget.GetWidgetsResponse
            requestNo := requestNo + 1
            printOutputLn response.result.debugJson
            for w in response.result.widgets do
              let params : Lean.Widget.GetWidgetSourceParams := { pos, hash := w.javascriptHash }
              let ps : RpcCallParams := {
                ps with
                method := `Lean.Widget.getWidgetSource,
                params := toJson params,
              }
              Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
              let resp ← Ipc.readResponseAs requestNo Lean.Widget.WidgetSource
              printOutputLn (toJson resp.result)
              requestNo := requestNo + 1
          | "completion" =>
            let p : CompletionParams := {
              textDocument := { uri }
              position := pos
            }
            printOutputLn (toJson p)
            Ipc.writeRequest ⟨requestNo, "textDocument/completion", p⟩
            let r ← Ipc.readResponseAs requestNo CompletionList
            printOutputLn (toJson r.result)
            requestNo := requestNo + 1
            for i in r.result.items do
              if i.data?.isNone then
                continue
              IO.eprintln s!"resolve: {i.label}"
              Ipc.writeRequest ⟨requestNo, "completionItem/resolve", i⟩
              let r ← Ipc.readResponseAs requestNo CompletionItem
              printOutputLn (toJson r.result)
              requestNo := requestNo + 1
          | "incomingCallHierarchy" =>
            let (callHierarchy?, callHierarchyRequestNo) ← Ipc.expandIncomingCallHierarchy requestNo uri pos
            printOutputLn (toJson callHierarchy?)
            requestNo := callHierarchyRequestNo
          | "outgoingCallHierarchy" =>
            let (callHierarchy?, callHierarchyRequestNo) ← Ipc.expandOutgoingCallHierarchy requestNo uri pos
            printOutputLn (toJson callHierarchy?)
            requestNo := callHierarchyRequestNo
          | "references" =>
            let p : ReferenceParams := {
              textDocument := { uri }
              position := pos
              context := { includeDeclaration := true }
            }
            printOutputLn (toJson p)
            Ipc.writeRequest ⟨requestNo, "textDocument/references", p⟩
            let r ← Ipc.readResponseAs requestNo (Option (Array Location))
            printOutputLn (toJson r.result)
            requestNo := requestNo + 1
          | "moduleHierarchyImports" =>
            let (moduleHierarchy?, moduleHierarchyRequestNo) ← Ipc.expandModuleHierarchyImports requestNo uri
            printOutputLn (toJson moduleHierarchy?)
            requestNo := moduleHierarchyRequestNo
          | "inlayHints" =>
            let p : InlayHintParams := {
              textDocument := { uri }
              range := { start := ⟨0, 0⟩, «end» := pos }
            }
            printOutputLn (toJson p)
            Ipc.writeRequest ⟨requestNo, "textDocument/inlayHint", p⟩
            let r ← Ipc.readResponseAs requestNo (Option (Array InlayHint))
            printOutputLn (toJson r.result)
            requestNo := requestNo + 1
          | _ =>
            let Except.ok params ← pure <| Json.parse params
              | throw <| IO.userError s!"failed to parse {params}"
            let params := params.setObjVal! "textDocument" (toJson { uri := uri : TextDocumentIdentifier })
            -- TODO: correctly compute in presence of Unicode
            let params := params.setObjVal! "position" (toJson pos)
            printOutputLn params
            Ipc.writeRequest ⟨requestNo, method, params⟩
            let rec readFirstResponse := do
              match ← Ipc.readMessage with
              | Message.response id r =>
                assert! id == requestNo
                return r
              | Message.notification .. => readFirstResponse
              | Message.request .. => readFirstResponse
              | msg => throw <| IO.userError s!"unexpected message {toJson msg}"
            let resp ← readFirstResponse
            printOutputLn resp
            requestNo := requestNo + 1
        | _ =>
          lastActualLineNo := lineNo
        lineNo := lineNo + 1

      let _ ← Ipc.collectDiagnostics requestNo uri (versionNo - 1)
      Ipc.writeNotification ⟨"textDocument/didClose", {
        textDocument := { uri } : DidCloseTextDocumentParams }⟩

    Ipc.shutdown requestNo
    discard <| Ipc.waitForExit
