import Lean.Data.Lsp

/-!
Tests that a client reply to a request from a file worker only reaches the worker that sent the
request. A new worker for the same file reuses the request IDs of the old worker, so a late reply
to the old worker must not reach the new one. The test replaces the worker by close/reopen, by a
crash and a restart, and by an import restart.
-/

open IO Lean Lsp

/--
Body of the test document. `sendPings n` sends `n` requests to the client, `ping` sends one
request and returns the reply of the client, and `crash` exits the worker.
-/
def body : String := r#"
open Lean Server

@[server_rpc_method]
def sendPings (n : Nat) : RequestM (RequestTask Unit) := do
  for _ in [0:n] do
    discard <| RequestM.sendServerRequest Json Json "test/ping" Json.null
  return .pure ()

@[server_rpc_method]
def ping (_ : Nat) : RequestM (RequestTask String) := do
  let t ← RequestM.sendServerRequest Json String "test/ping" Json.null
  RequestM.mapTaskCheap t fun
    | .success s => return s
    | .failure _ msg => return s!"failure: {msg}"

@[server_rpc_method]
def crash (_ : Nat) : RequestM (RequestTask Unit) :=
  IO.Process.forceExit 1
"#

def text : String := "import Lean\n" ++ body

def textWithNewImport : String := "import Lean\nimport Lean.Data.Json\n" ++ body

structure TestState where
  nextId : Nat := 1
  /-- IDs of the requests from the server since the last reset. -/
  serverRequests : Array JsonRpc.RequestID := #[]

abbrev TestM := StateT TestState Ipc.IpcM

def request [ToJson α] (method : String) (params : α) : TestM Nat := do
  let id := (← get).nextId
  modify ({ · with nextId := id + 1 })
  Ipc.writeRequest ⟨id, method, params⟩
  return id

def respond (id : JsonRpc.RequestID) (result : String) : TestM Unit := do
  (← Ipc.stdin).writeLspResponse { id, result : JsonRpc.Response String }

/-- Reads messages until `stop` holds, and records the requests from the server. -/
partial def readUntil (stop : JsonRpc.Message → Bool) : TestM JsonRpc.Message := do
  let msg ← Ipc.readMessage
  if let .request id .. := msg then
    modify fun s => { s with serverRequests := s.serverRequests.push id }
  if stop msg then
    return msg
  readUntil stop

def isResponse (id : Nat) : JsonRpc.Message → Bool
  | .response id' _ | .responseError id' .. => id' == (id : JsonRpc.RequestID)
  | _ => false

def describe : JsonRpc.Message → String
  | .response _ result => result.compress
  | .responseError _ code message _ => s!"error {(toJson code).compress}: {message}"
  | msg => s!"unexpected message {(toJson msg).compress}"

def openFile (uri : DocumentUri) (text : String) : TestM Unit :=
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri, languageId := "lean", version := 1, text }
    : DidOpenTextDocumentParams }⟩

def changeFile (uri : DocumentUri) (version : Nat) (text : String) : TestM Unit :=
  Ipc.writeNotification ⟨"textDocument/didChange", {
    textDocument := { uri, version? := some version }
    contentChanges := #[.fullChange text]
    : DidChangeTextDocumentParams }⟩

def closeFile (uri : DocumentUri) : TestM Unit :=
  Ipc.writeNotification ⟨"textDocument/didClose", {
    textDocument := { uri } : DidCloseTextDocumentParams }⟩

def connect (uri : DocumentUri) : TestM UInt64 := do
  let id ← request "$/lean/rpc/connect" { uri : RpcConnectParams }
  let msg ← readUntil (isResponse id)
  let .response _ result := msg
    | throw <| userError s!"rpc/connect failed: {describe msg}"
  let .ok (r : RpcConnected) := fromJson? result
    | throw <| userError s!"unexpected rpc/connect result: {result.compress}"
  return r.sessionId

/-- Calls `method` at the end of `text`, after all RPC methods are defined. -/
def call (uri : DocumentUri) (text : String) (sessionId : UInt64) (method : Name) (param : Nat) :
    TestM Nat := do
  let position := ⟨(text.splitOn "\n").length - 1, 0⟩
  request "$/lean/rpc/call"
    { textDocument := { uri }, position, sessionId, method, params := toJson param : RpcCallParams }

/--
Waits until the worker for `uri` has finished `version`. Only then does the test connect, so that
the session belongs to the worker for `version`.
-/
def waitForILeans (uri : DocumentUri) (version : Nat) : TestM Unit := do
  let id ← request "$/lean/waitForILeans" { uri? := some uri, version? := some version : WaitForILeansParams }
  let msg ← readUntil (isResponse id)
  unless msg matches .response .. do
    throw <| userError s!"waitForILeans failed: {describe msg}"

/--
Lets worker #1 send many requests to the client, replaces the worker with `replace`, and lets
worker #2 send one request. The reply to worker #2 is visible as the result of `ping`. Worker #1
used every request ID that worker #2 can use for its request, so all replies to worker #1 are
answered with `"stale"` before the reply to worker #2. `replace` returns the new text and version.
-/
def scenario (name : String) (uri : DocumentUri)
    (replace : UInt64 → TestM (String × Nat)) : TestM Unit := do
  modify ({ · with serverRequests := #[] })
  openFile uri text
  waitForILeans uri 1
  let session ← connect uri
  let id ← call uri text session `sendPings 50
  discard <| readUntil (isResponse id)
  let oldRequests := (← get).serverRequests
  let (newText, newVersion) ← replace session
  waitForILeans uri newVersion
  let session ← connect uri
  let id ← call uri newText session `ping 0
  let .request pingId .. ← readUntil (· matches .request _ "test/ping" _)
    | throw <| userError "expected a `test/ping` request"
  for oldId in oldRequests do
    respond oldId "stale"
  respond pingId "fresh"
  IO.println s!"{name}: {describe (← readUntil (isResponse id))}"
  closeFile uri

def test : TestM Unit := do
  scenario "close-reopen" "file:///lateRepliesA.lean" fun _ => do
    closeFile "file:///lateRepliesA.lean"
    openFile "file:///lateRepliesA.lean" text
    return (text, 1)
  scenario "crash-restart" "file:///lateRepliesB.lean" fun session => do
    let id ← call "file:///lateRepliesB.lean" text session `crash 0
    discard <| readUntil (isResponse id)
    changeFile "file:///lateRepliesB.lean" 2 (text ++ "\n")
    return (text ++ "\n", 2)
  scenario "import-restart" "file:///lateRepliesC.lean" fun _ => do
    changeFile "file:///lateRepliesC.lean" 2 textWithNewImport
    return (textWithNewImport, 2)
  Ipc.shutdown (← get).nextId
  discard Ipc.waitForExit

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard <| Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
    discard <| test.run {}
