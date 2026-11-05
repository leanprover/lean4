import Lean.Data.Lsp

/-!
Tests that the watchdog can shut down when a file worker has closed its stdout but keeps running and
ignores the `exit` notification. The fake worker is `closed_stdout_worker.sh`.
-/

open IO Lean Lsp

partial def readResponse (id : Nat) : Ipc.IpcM JsonRpc.Message := do
  let msg ← Ipc.readMessage
  match msg with
  | .response id' _ | .responseError id' .. =>
    if id' == (id : JsonRpc.RequestID) then
      return msg
    readResponse id
  | _ => readResponse id

def test : Ipc.IpcM Unit := do
  let hIn ← Ipc.stdin
  hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
  hIn.flush
  discard <| Ipc.readResponseAs 0 InitializeResult
  Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri := "file:///closedStdout.lean", languageId := "lean", version := 1,
                      text := "def x := 1\n" }
    : DidOpenTextDocumentParams }⟩
  -- Gives the watchdog time to notice that the output of the worker has ended.
  IO.sleep 1000
  Ipc.writeRequest ⟨1, "shutdown", Json.null⟩
  -- Waits at most 10 s, so that the test fails instead of hanging when the shutdown is blocked.
  let proc ← read
  let resp ← IO.asTask (readResponse 1 |>.run proc)
  let mut waitedMs := 0
  while !(← IO.hasFinished resp) && waitedMs < 10000 do
    IO.sleep 100
    waitedMs := waitedMs + 100
  unless ← IO.hasFinished resp do
    IO.println "shutdown: no response within 10 s"
    proc.kill
    return
  IO.println "shutdown: answered"
  Ipc.writeNotification ⟨"exit", Json.null⟩
  IO.println s!"watchdog exit code: {← Ipc.waitForExit}"

def main : IO Unit := do
  let proc ← Process.spawn {
    toStdioConfig := Ipc.ipcStdioConfig
    cmd  := "lean"
    args := #["--server"]
    env  := #[("LEAN_WORKER_PATH", some ((← IO.currentDir) / "closed_stdout_worker.sh").toString)]
  }
  test.run proc
