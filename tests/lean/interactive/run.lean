import Lean.Data.Lsp
import Lean.Widget
open Lean
open Lean.Lsp
open Lean.JsonRpc

namespace Client

/- Client-side types for showing interactive goals. -/

structure SubexprInfo where
  subexprPos : String
  diffStatus? : Option String
  deriving FromJson, Repr

structure Hyp where
  type : Widget.TaggedText SubexprInfo
  names : Array String
  isInserted?: Option Bool
  isRemoved?: Option Bool
  deriving FromJson, Repr

structure InteractiveGoal where
  type : Widget.TaggedText SubexprInfo
  isInserted?: Option Bool := none
  isRemoved?: Option Bool := none
  hyps : Array Hyp
  deriving FromJson, Repr

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving FromJson, Repr

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

def Lean.Widget.GetWidgetsResponse.debugJson (r : Widget.GetWidgetsResponse) : Json :=
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

def word : Parsec String :=
  Parsec.many1Chars <| Parsec.digit <|> Parsec.asciiLetter <|> Parsec.pchar '_'

def ident : Parsec Name := do
  let head ← word
  let xs ← Parsec.many1 (Parsec.pchar '.' *> word)
  return xs.foldl Name.mkStr $ head

partial def main (args : List String) : IO Unit := do
  let uri := s!"file:///{args.head!}"
  Ipc.runWith (←IO.appPath) #["--server"] do
    let capabilities := {
      textDocument? := some {
        completion? := some {
          completionItem? := some {
            insertReplaceSupport? := true
          }
        }
      }
    }
    Ipc.writeRequest ⟨0, "initialize", { capabilities : InitializeParams }⟩
    let _ ← Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    let text ← IO.FS.readFile args.head!
    Ipc.writeNotification ⟨"textDocument/didOpen", {
      textDocument := { uri := uri, languageId := "lean", version := 1, text := text } : DidOpenTextDocumentParams }⟩
    let _ ← Ipc.collectDiagnostics 1 uri 1
    let mut lineNo := 0
    let mut lastActualLineNo := 0
    let mut versionNo : Nat := 2
    let mut requestNo : Nat := 2
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
        | "insert" =>
          let params : DidChangeTextDocumentParams := {
            textDocument := {
              uri      := uri
              version? := versionNo
            }
            contentChanges := #[TextDocumentContentChangeEvent.rangeChange {
              start := pos
              «end» := { pos with character := pos.character + params.endPos.byteIdx }
            } params]
          }
          let params := toJson params
          IO.eprintln params
          Ipc.writeNotification ⟨"textDocument/didChange", params⟩
          -- We don't want to wait for changes to be processed so we can test concurrency
          --let _ ← Ipc.collectDiagnostics requestNo uri versionNo
          requestNo := requestNo + 1
          versionNo := versionNo + 1
        | "collectDiagnostics" =>
          let diags ← Ipc.collectDiagnostics requestNo uri (versionNo - 1)
          for diag in diags do
            IO.eprintln (toJson diag.param)
          requestNo := requestNo + 1
        | "codeAction" =>
          let params : CodeActionParams := {
            textDocument := {uri := uri},
            range := ⟨pos, pos⟩
          }
          Ipc.writeRequest ⟨requestNo, "textDocument/codeAction", params⟩
          let r ← Ipc.readResponseAs requestNo (Array Json)
          for x in r.result do
            IO.eprintln x
          requestNo := requestNo + 1
        | "goals" =>
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
          IO.eprintln (repr response.result)
          IO.eprintln ""
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
          IO.eprintln response.result.debugJson
          for w in response.result.widgets do
            let params : Lean.Widget.GetWidgetSourceParams := { pos, hash := w.javascriptHash }
            let ps : RpcCallParams := {
              ps with
              method := `Lean.Widget.getWidgetSource,
              params := toJson params,
            }
            Ipc.writeRequest ⟨requestNo, "$/lean/rpc/call", ps⟩
            let resp ← Ipc.readResponseAs requestNo Lean.Widget.WidgetSource
            IO.eprintln (toJson resp.result)
            requestNo := requestNo + 1
        | _ =>
          let Except.ok params ← pure <| Json.parse params
            | throw <| IO.userError s!"failed to parse {params}"
          let params := params.setObjVal! "textDocument" (toJson { uri := uri : TextDocumentIdentifier })
          -- TODO: correctly compute in presence of Unicode
          let params := params.setObjVal! "position" (toJson pos)
          IO.eprintln params
          Ipc.writeRequest ⟨requestNo, method, params⟩
          let rec readFirstResponse := do
            match ← Ipc.readMessage with
            | Message.response id r =>
              assert! id == requestNo
              return r
            | Message.notification .. => readFirstResponse
            | msg => throw <| IO.userError s!"unexpected message {toJson msg}"
          let resp ← readFirstResponse
          IO.eprintln resp
          requestNo := requestNo + 1
      | _ =>
        lastActualLineNo := lineNo
      lineNo := lineNo + 1

    Ipc.shutdown requestNo
    discard <| Ipc.waitForExit
