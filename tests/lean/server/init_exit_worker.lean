import Lean.Data.Lsp
open IO Lean Lsp

#eval (do
  Ipc.runWith (←IO.appPath) #["--worker"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    hIn.write (←FS.readBinFile "open_empty.log")
    hIn.flush
    Ipc.writeNotification ⟨"exit", Json.null⟩
  : IO Unit)