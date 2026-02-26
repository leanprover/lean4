import Lean.Data.Lsp
open IO Lean Lsp

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "server_startup.lean.log")
    hIn.flush
    let _ ← Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    Ipc.shutdown 1
