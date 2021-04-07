import Lean.Data.Lsp
open IO Lean Lsp

def main (args : List String) : IO Unit := do
  let uri := s!"file://{args.head!}"
  Ipc.runWith (←IO.appPath) #["--server"] do
    let hIn ← Ipc.stdin
    Ipc.writeRequest ⟨0, "initialize", { capabilities := ⟨⟩ : InitializeParams }⟩
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
    for line in text.splitOn "\n" do
      match line.splitOn "--^" with
      | [ws, directive] =>
        let colon := directive.posOf ':'
        let method := directive.extract 0 colon |>.trim
        -- TODO: correctly compute in presence of Unicode
        let column := ws.bsize + "--".length
        let pos : Lsp.Position := { line := lastActualLineNo, character := column }
        let params := if colon < directive.bsize then directive.extract (colon + 1) directive.bsize |>.trim else "{}"
        match method with
        | "insert" =>
          let params : DidChangeTextDocumentParams := {
            textDocument := {
              uri      := uri
              version? := versionNo
            }
            contentChanges := #[TextDocumentContentChangeEvent.rangeChange {
              start := pos
              «end» := { pos with character := pos.character + params.bsize }
            } params]
          }
          let params := toJson params
          IO.eprintln params
          Ipc.writeNotification ⟨"textDocument/didChange", params⟩
          let diags ← Ipc.collectDiagnostics requestNo uri versionNo
          --for diag in diags do
          --  IO.eprintln (toJson diag.param)
          requestNo := requestNo + 1
          versionNo := versionNo + 1
        | _ =>
          let Except.ok params ← pure <| Json.parse params
            | throw <| IO.userError s!"failed to parse {params}"
          let params := params.setObjVal! "textDocument" (toJson { uri := uri : TextDocumentIdentifier })
          -- TODO: correctly compute in presence of Unicode
          let column := ws.bsize + "--".length
          let params := params.setObjVal! "position" (toJson pos)
          IO.eprintln params
          Ipc.writeRequest ⟨requestNo, method, params⟩
          let resp ← Ipc.readResponseAs requestNo Json
          IO.eprintln resp.result
          requestNo := requestNo + 1
      | _ =>
        lastActualLineNo := lineNo
      lineNo := lineNo + 1
    Ipc.writeRequest ⟨requestNo, "shutdown", Json.null⟩
    let shutResp ← Ipc.readResponseAs requestNo Json
    assert! shutResp.result.isNull
    Ipc.writeNotification ⟨"exit", Json.null⟩
    discard <| Ipc.waitForExit
