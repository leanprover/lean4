import Lean.Data.Lsp
open IO Lean Lsp

def main : IO Unit := do
  Ipc.runWith (←IO.appPath) #["--server", "-Dlinter.all=false"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard $ Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    hIn.write (←FS.readBinFile "open_content.log")
    hIn.flush
    let some diag ← Ipc.collectDiagnostics 1 "file:///test.lean" 1
      | throw $ userError "Test failed, no diagnostics received."
    FS.writeFile "content_diag.json.produced" (toString <| toJson (diag : JsonRpc.Message))

    if let Except.ok (refDiag : JsonRpc.Notification PublishDiagnosticsParams) :=
      (Json.parse $ ←FS.readFile "content_diag.json") >>= fromJson?
    then
      assert! (diag == refDiag)
    else
      throw $ userError "Failed parsing test file."

    Ipc.shutdown 2
    discard $ Ipc.waitForExit
