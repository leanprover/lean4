import Lean.Data.Lsp
open IO Lean Lsp

/-
#eval (do
  Ipc.runWith (←IO.appPath) #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    let initResp ← Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩ 
    hIn.write (←FS.readBinFile "open_empty.log")
    hIn.flush
    Ipc.writeRequest ⟨1, "shutdown", Json.null⟩
    let shutdownResp ← Ipc.readResponseAs 1 Json
    assert! shutdownResp.result.isNull
    Ipc.writeNotification ⟨"exit", Json.null⟩
  : IO Unit)
-/
