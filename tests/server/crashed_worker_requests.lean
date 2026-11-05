import Lean.Data.Lsp

/-!
Tests that the watchdog answers requests to a crashed file worker with `workerCrashed`, both for
requests that are pending when the worker crashes and for requests that arrive before the next
`didChange` restarts the worker.
-/

open IO Lean Lsp

def uri : DocumentUri := "file:///crash.lean"

-- The sleep makes sure that the first hover request is pending when the worker exits.
def crashingText : String :=
  "def x := 1\n#eval show IO Unit from do IO.sleep 1000; IO.Process.forceExit 1\ndef y := 2\n"

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

def isFatalErrorProgress (msg : JsonRpc.Message) : Bool :=
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

/--
Reads messages until both the response for `id` and the `fatalError` progress notification for
`uri` have arrived. They can arrive in either order.
-/
partial def readResponseAndCrash (id : JsonRpc.RequestID) (resp? : Option JsonRpc.Message := none)
    (crashed := false) : Ipc.IpcM JsonRpc.Message := do
  if let some resp := resp? then
    if crashed then
      return resp
  let msg ← Ipc.readMessage
  if responseId? msg == some id then
    readResponseAndCrash id (some msg) crashed
  else
    readResponseAndCrash id resp? (crashed || isFatalErrorProgress msg)

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard <| Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩

    Ipc.writeNotification ⟨"textDocument/didOpen", {
      textDocument := { uri, languageId := "lean", version := 1, text := crashingText }
      : DidOpenTextDocumentParams }⟩
    hover 1 uri 2
    let resp ← readResponseAndCrash 1
    IO.println s!"request pending during the crash: {describe resp}"

    hover 2 uri 0
    -- The watchdog answers requests to files without a worker at once, so if it does not answer
    -- request 2 before request 3, request 2 is left pending.
    hover 3 "file:///notOpen.lean" 0
    let resp ← readNextResponse
    if responseId? resp != some (2 : JsonRpc.RequestID) then
      throw <| userError s!"Expected a response for request 2, got: {(toJson resp).compress}"
    IO.println s!"request after the crash: {describe resp}"
    discard readNextResponse

    Ipc.writeNotification ⟨"textDocument/didChange", {
      textDocument := { uri, version? := some 2 }
      contentChanges := #[.fullChange fixedText]
      : DidChangeTextDocumentParams }⟩
    hover 4 uri 0
    let resp ← readNextResponse
    if responseId? resp != some (4 : JsonRpc.RequestID) then
      throw <| userError s!"Expected a response for request 4, got: {(toJson resp).compress}"
    IO.println s!"request after the restart: {describe resp}"

    Ipc.shutdown 5
    discard Ipc.waitForExit
