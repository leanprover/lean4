import Lean.Data.Lsp
open IO Lean Lsp

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_zed_0_150_4.log")
    hIn.flush
    let initResp ← Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    Ipc.shutdown 1
    discard Ipc.waitForExit
