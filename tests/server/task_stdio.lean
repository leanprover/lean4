import Lean.Data.Lsp

/-!
Tests that user code in a task cannot read the LSP messages of a file worker from stdin or write
to its LSP output on stdout (#738). In the worker, such a task reads end of file from stdin, and its
output to stdout goes to stderr.
-/

open IO Lean Lsp

def uri : DocumentUri := "file:///taskStdio.lean"

def text : String := "#eval show IO String from do
  let t ← IO.asTask do (← IO.getStdin).getLine
  IO.ofExcept (← IO.wait t)

#eval show IO Unit from do
  let t ← IO.asTask (IO.println \"output from a task\")
  discard <| IO.wait t

def x := 1
"

partial def readResponse (id : Nat) : Ipc.IpcM JsonRpc.Message := do
  let msg ← Ipc.readMessage
  match msg with
  | .response id' _ | .responseError id' .. =>
    if id' == (id : JsonRpc.RequestID) then
      return msg
    readResponse id
  | _ => readResponse id

def describe : JsonRpc.Message → String
  | .response .. => "result"
  | .responseError _ code message _ => s!"error {(toJson code).compress}: {message}"
  | msg => s!"unexpected message {(toJson msg).compress}"

def test : Ipc.IpcM Unit := do
  let hIn ← Ipc.stdin
  hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
  hIn.flush
  discard <| Ipc.readResponseAs 0 InitializeResult
  Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri, languageId := "lean", version := 1, text }
    : DidOpenTextDocumentParams }⟩
  let some diags ← Ipc.collectDiagnostics 1 uri 1
    | throw <| userError "no diagnostics"
  for d in diags.param.diagnostics do
    IO.println s!"diagnostic on line {d.range.start.line}: {d.message}"
  Ipc.writeRequest ⟨2, "textDocument/hover",
    { textDocument := { uri }, position := ⟨8, 4⟩ : HoverParams }⟩
  IO.println s!"hover on `x`: {describe (← readResponse 2)}"
  Ipc.shutdown 3
  IO.println s!"watchdog exit code: {← Ipc.waitForExit}"

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let proc ← read
    -- Waits at most 30 s, so that the test fails instead of hanging.
    let t ← IO.asTask (test.run proc)
    let mut waitedMs := 0
    while !(← IO.hasFinished t) && waitedMs < 30000 do
      IO.sleep 100
      waitedMs := waitedMs + 100
    unless ← IO.hasFinished t do
      IO.println "no result within 30 s"
      proc.kill
      return
    IO.ofExcept (← IO.wait t)
