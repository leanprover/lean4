import Lean.Data.Lsp

/-!
Tests that the watchdog keeps running when a file worker exits before it reads the `initialize`
request and the `didOpen` notification. The fake worker is the `true` program. The document is
larger than a pipe buffer, so the watchdog cannot write the `didOpen` notification.
-/

open IO Lean Lsp

def findTrue : IO System.FilePath := do
  let name := if System.Platform.isWindows then "true.exe" else "true"
  for dir in System.SearchPath.parse ((← IO.getEnv "PATH").getD "") do
    let path := dir / name
    if ← path.pathExists then
      return path
  throw <| userError "Cannot find `true` in `PATH`"

def uri : DocumentUri := "file:///big.lean"

def bigText : String :=
  "def x := 1\n" ++ String.join (List.replicate 16000 s!"-- {String.ofList (List.replicate 60 'x')}\n")

/-- Reads the next response for any request, skipping notifications and server requests. -/
partial def readNextResponse : Ipc.IpcM JsonRpc.Message := do
  let msg ← Ipc.readMessage
  match msg with
  | .response .. | .responseError .. => return msg
  | _ => readNextResponse

def describe (msg : JsonRpc.Message) : String :=
  match msg with
  | .responseError id code message _ => s!"{(toJson id).compress}: error {(toJson code).compress}: {message}"
  | .response id .. => s!"{(toJson id).compress}: result"
  | _ => s!"unexpected message {(toJson msg).compress}"

def test : Ipc.IpcM Unit := do
  let hIn ← Ipc.stdin
  hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
  hIn.flush
  discard <| Ipc.readResponseAs 0 InitializeResult
  Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri, languageId := "lean", version := 1, text := bigText }
    : DidOpenTextDocumentParams }⟩
  Ipc.writeRequest ⟨1, "textDocument/hover",
    { textDocument := { uri }, position := ⟨0, 4⟩ : HoverParams }⟩
  IO.println s!"request to the file: {describe (← readNextResponse)}"
  Ipc.shutdown 2
  IO.println s!"watchdog exit code: {← Ipc.waitForExit}"

def main : IO Unit := do
  let proc ← Process.spawn {
    toStdioConfig := Ipc.ipcStdioConfig
    cmd  := "lean"
    args := #["--server"]
    env  := #[("LEAN_WORKER_PATH", some (← findTrue).toString)]
  }
  test.run proc
