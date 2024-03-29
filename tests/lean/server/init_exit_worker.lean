import Lean.Data.Lsp
open IO Lean Lsp

def main : IO Unit := do
  Ipc.runWith (←IO.appPath) #["--worker"] do
    let hIn ← Ipc.stdin
    hIn.write (←FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush

    hIn.write (←FS.readBinFile "open_empty.log")
    hIn.flush
    let diags? ← Ipc.collectDiagnostics 1 "file:///empty" 1
    assert! diags?.isSome

    Ipc.writeNotification ⟨"exit", Json.null⟩
    discard Ipc.waitForExit
