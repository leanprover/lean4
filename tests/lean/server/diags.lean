import Lean.Data.Lsp
open IO Lean Lsp

#eval (do
  Ipc.runWith (←IO.appPath) #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard $ Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    hIn.write (←FS.readBinFile "open_content.log")
    hIn.flush
    let diags ← Ipc.collectDiagnostics 1 "file:///test.lean"
    if h: diags.isEmpty then
      throw $ userError "Test failed, no diagnostics received."
    else
      let diag := diags.getLast (by
        intro hEq
        rw hEq at h
        exact h rfl)

      if let some (refDiag : JsonRpc.Notification PublishDiagnosticsParams) :=
        (Json.parse $ ←FS.readFile "content_diag.json").toOption >>= fromJson?
      then
        assert! (diag == refDiag)
      else
        throw $ userError "Failed parsing test file."

      Ipc.writeRequest ⟨2, "shutdown", Json.null⟩
      let shutResp ← Ipc.readResponseAs 2 Json
      assert! shutResp.result.isNull
      Ipc.writeNotification ⟨"exit", Json.null⟩
      discard $ Ipc.waitForExit
: IO Unit)