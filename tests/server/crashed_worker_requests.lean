import Lean.Data.Lsp

/-!
Tests that the watchdog answers requests to a crashed file worker with `workerCrashed`, both for
requests that are pending when the worker crashes and for requests that arrive before the next
`didChange` restarts the worker. A worker that exits with code 0 without an `exit` notification
counts as crashed. Other files keep working.
-/

open IO Lean Lsp

-- The sleep makes sure that the first hover request is pending when the worker exits.
def crashingText (exitCode : Nat) : String :=
  s!"def x := 1\n#eval show IO Unit from do IO.sleep 1000; IO.Process.forceExit {exitCode}\ndef y := 2\n"

def fixedText : String :=
  "def x := 1\ndef y := 2\n"

def hover (id : Nat) (uri : DocumentUri) (line : Nat) : Ipc.IpcM Unit :=
  Ipc.writeRequest ⟨id, "textDocument/hover",
    { textDocument := { uri }, position := ⟨line, 4⟩ : HoverParams }⟩

def describe (msg : JsonRpc.Message) : String :=
  match msg with
  | .responseError _ code message _ => s!"error {(toJson code).compress}: {message}"
  | .response .. => "result"
  | _ => s!"unexpected message {(toJson msg).compress}"

def isFatalErrorProgress (uri : DocumentUri) (msg : JsonRpc.Message) : Bool :=
  match msg with
  | .notification "$/lean/fileProgress" (some params) =>
    match fromJson? (α := LeanFileProgressParams) (toJson params) with
    | .ok p => p.textDocument.uri == uri && p.processing.any (·.kind == .fatalError)
    | .error _ => false
  | _ => false

/-- Reads the next response for any request, skipping notifications and server requests. -/
partial def readNextResponse : Ipc.IpcM JsonRpc.Message := do
  let msg ← Ipc.readMessage
  match msg with
  | .response .. | .responseError .. => return msg
  | _ => readNextResponse

def responseId? : JsonRpc.Message → Option JsonRpc.RequestID
  | .response id _ | .responseError id .. => some id
  | _ => none

/-- Reads the next response and fails if it is not the response for `id`. -/
def readResponse (id : Nat) : Ipc.IpcM JsonRpc.Message := do
  let resp ← readNextResponse
  if responseId? resp != some (id : JsonRpc.RequestID) then
    throw <| userError s!"Expected a response for request {id}, got: {(toJson resp).compress}"
  return resp

/--
Reads messages until both the response for `id` and the `fatalError` progress notification for
`uri` have arrived. They can arrive in either order.
-/
partial def readResponseAndCrash (uri : DocumentUri) (id : JsonRpc.RequestID)
    (resp? : Option JsonRpc.Message := none) (crashed := false) : Ipc.IpcM JsonRpc.Message := do
  if let some resp := resp? then
    if crashed then
      return resp
  let msg ← Ipc.readMessage
  if responseId? msg == some id then
    readResponseAndCrash uri id (some msg) crashed
  else
    readResponseAndCrash uri id resp? (crashed || isFatalErrorProgress uri msg)

/-- Crashes the worker for `uri` with `exitCode` and restarts it. Request IDs start at `base`. -/
def scenario (exitCode : Nat) (uri : DocumentUri) (base : Nat) : Ipc.IpcM Unit := do
  let log (s : String) := IO.println s!"exit code {exitCode}, {s}"
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri, languageId := "lean", version := 1, text := crashingText exitCode }
    : DidOpenTextDocumentParams }⟩
  hover base uri 2
  let resp ← readResponseAndCrash uri base
  log s!"request pending during the crash: {describe resp}"

  hover (base + 1) uri 0
  -- The watchdog answers requests to files without a worker at once, so if it does not answer
  -- the previous request before this one, the previous request is left pending.
  hover (base + 2) "file:///notOpen.lean" 0
  log s!"request after the crash: {describe (← readResponse (base + 1))}"
  discard <| readResponse (base + 2)

  Ipc.writeNotification ⟨"textDocument/didChange", {
    textDocument := { uri, version? := some 2 }
    contentChanges := #[.fullChange fixedText]
    : DidChangeTextDocumentParams }⟩
  hover (base + 3) uri 0
  log s!"request after the restart: {describe (← readResponse (base + 3))}"

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard <| Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    let healthyUri := "file:///healthy.lean"
    Ipc.writeNotification ⟨"textDocument/didOpen", {
      textDocument := { uri := healthyUri, languageId := "lean", version := 1, text := fixedText }
      : DidOpenTextDocumentParams }⟩

    scenario 1 "file:///crash1.lean" 10
    scenario 0 "file:///crash0.lean" 20

    hover 30 healthyUri 0
    IO.println s!"request to another file: {describe (← readResponse 30)}"

    Ipc.shutdown 31
    discard Ipc.waitForExit
