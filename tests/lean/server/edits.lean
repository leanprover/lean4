import Lean.Data.Lsp
open IO Lean Lsp

#exit
#eval (do
  Ipc.runWith (←IO.appPath) #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard $ Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    hIn.write (←FS.readBinFile "open_content.log")
    hIn.flush
    discard <| Ipc.collectDiagnostics 1 "file:///test.lean" 1

    hIn.write (←FS.readBinFile "content_changes.log")
    hIn.flush

    let diags ← Ipc.collectDiagnostics 2 "file:///test.lean" 7
    if diags.isEmpty then
      throw $ userError "Test failed, no diagnostics received."
    else
      let diag := diags.getLast!
      FS.writeFile "edits_diag.json.produced" (toString <| toJson (diag : JsonRpc.Message))

      if let some (refDiag : JsonRpc.Notification PublishDiagnosticsParams) :=
        (Json.parse $ ←FS.readFile "edits_diag.json").toOption >>= fromJson?
      then
        assert! (diag == refDiag)
      else
        throw $ userError "Failed parsing test file."

      Ipc.writeRequest ⟨3, "shutdown", Json.null⟩
      let shutResp ← Ipc.readResponseAs 3 Json
      assert! shutResp.result.isNull
      Ipc.writeNotification ⟨"exit", Json.null⟩
      discard $ Ipc.waitForExit
: IO Unit)
