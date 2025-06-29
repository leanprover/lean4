import Lean.Data.Lsp
open IO Lean Lsp

def mkCompletionRequest (id : Nat) : JsonRpc.Request Json :=
  let param := Json.parse r#"{"textDocument":{"uri":"file:///home/mhuisi/Lean/lean4/tests/bench/identifier_completion.lean"},"position":{"line":25,"character":40},"context":{"triggerKind":1}}"#
  let param := param.toOption.get!
  { id, method := "textDocument/completion", param }

def main : IO Unit := do
  Ipc.runWith (←IO.appPath) #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (← FS.readBinFile "identifier_completion_initialization.log")
    hIn.flush
    let _ ← Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification {
      method := "initialized"
      param := InitializedParams.mk
    }
    hIn.write (← FS.readBinFile "identifier_completion_didOpen.log")
    -- Let file progress proceed to the point of the completion that we want to benchmark
    Ipc.writeRequest <| mkCompletionRequest 1
    let _ ← Ipc.readResponseAs 1 CompletionList
    let startTime ← IO.monoMsNow
    for i in [2:5] do
      Ipc.writeRequest <| mkCompletionRequest i
      let _ ← Ipc.readResponseAs i CompletionList
    let endTime ← IO.monoMsNow
    IO.println s!"completion: {(endTime - startTime).toFloat / 1000.0}"
    Ipc.shutdown 5
