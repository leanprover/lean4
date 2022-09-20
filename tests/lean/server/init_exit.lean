import Lean.Data.Lsp
open IO Lean Lsp

def main : IO Unit := do
  Ipc.runWith (←IO.appPath) #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    let initResp ← Ipc.readResponseAs 0 InitializeResult
    let regWatchReq ← Ipc.readRequestAs "client/registerCapability" Json
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    Ipc.shutdown 1
    discard Ipc.waitForExit
