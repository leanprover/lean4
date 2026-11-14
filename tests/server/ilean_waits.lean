import Lean.Data.Lsp

/-!
Tests when the watchdog answers `$/lean/waitForILeans` requests:
* A wait for a newer version stays pending when an older version is finalized.
* A wait that is pending when the worker crashes gets `workerCrashed`.
* After the crash, a wait for a finalized version gets a result, and a wait for any other version
  gets `workerCrashed`.
* A wait that is pending when the file is closed gets `contentModified`.
-/

open IO Lean Lsp

def describe : Option JsonRpc.Message → String
  | some (.responseError _ code message _) => s!"error {(toJson code).compress}: {message}"
  | some (.response ..) => "result"
  | some msg => s!"unexpected message {(toJson msg).compress}"
  | none => "no response"

def responseId? : JsonRpc.Message → Option JsonRpc.RequestID
  | .response id _ | .responseError id .. => some id
  | _ => none

def isFatalErrorProgress (uri : DocumentUri) (msg : JsonRpc.Message) : Bool :=
  match msg with
  | .notification "$/lean/fileProgress" (some params) =>
    match fromJson? (α := LeanFileProgressParams) (toJson params) with
    | .ok p => p.textDocument.uri == uri && p.processing.any (·.kind == .fatalError)
    | .error _ => false
  | _ => false

/-- Reads messages until `stop` holds and returns the responses that arrived before. -/
partial def collectResponsesUntil (stop : JsonRpc.Message → Bool)
    (acc : Array JsonRpc.Message := #[]) : Ipc.IpcM (Array JsonRpc.Message) := do
  let msg ← Ipc.readMessage
  if stop msg then
    return acc
  collectResponsesUntil stop (if (responseId? msg).isSome then acc.push msg else acc)

/-- Reads messages until the response for `id` and returns it with all responses before it. -/
def collectResponsesThrough (id : Nat) : Ipc.IpcM (Array JsonRpc.Message) := do
  let mut acc := #[]
  repeat
    let msg ← Ipc.readMessage
    if (responseId? msg).isSome then
      acc := acc.push msg
    if responseId? msg == some (id : JsonRpc.RequestID) then
      break
  return acc

def findResponse (resps : Array JsonRpc.Message) (id : Nat) : Option JsonRpc.Message :=
  resps.find? (responseId? · == some (id : JsonRpc.RequestID))

def waitForILeans (id : Nat) (uri : DocumentUri) (version : Nat) : Ipc.IpcM Unit :=
  Ipc.writeRequest ⟨id, "$/lean/waitForILeans",
    { uri? := some uri, version? := some version : WaitForILeansParams }⟩

/--
The watchdog answers requests to files without a worker at once. All requests sent before it are
answered before it, unless they are pending.
-/
def sentinel (id : Nat) : Ipc.IpcM Unit :=
  Ipc.writeRequest ⟨id, "textDocument/hover",
    { textDocument := { uri := "file:///notOpen.lean" }, position := ⟨0, 0⟩ : HoverParams }⟩

def openFile (uri : DocumentUri) (text : String) : Ipc.IpcM Unit :=
  Ipc.writeNotification ⟨"textDocument/didOpen", {
    textDocument := { uri, languageId := "lean", version := 1, text }
    : DidOpenTextDocumentParams }⟩

def changeFile (uri : DocumentUri) (version : Nat) (text : String) : Ipc.IpcM Unit :=
  Ipc.writeNotification ⟨"textDocument/didChange", {
    textDocument := { uri, version? := some version }
    contentChanges := #[.fullChange text]
    : DidChangeTextDocumentParams }⟩

def finalizationOrder : Ipc.IpcM Unit := do
  let uri := "file:///waits.lean"
  openFile uri "def a := 1\n"
  waitForILeans 1 uri 1
  discard <| collectResponsesThrough 1
  changeFile uri 2 "def a := 1\n#eval IO.sleep 1000\n"
  waitForILeans 2 uri 3
  waitForILeans 3 uri 2
  discard <| collectResponsesThrough 3
  changeFile uri 3 "def a := 1\ndef b := 2\n"
  waitForILeans 4 uri 3
  let resps ← collectResponsesThrough 4
  IO.println s!"wait for v3 sent before v2 was finalized: {describe (findResponse resps 2)}"

def crash : Ipc.IpcM Unit := do
  let uri := "file:///waitsCrash.lean"
  openFile uri "def a := 1\n"
  waitForILeans 10 uri 1
  discard <| collectResponsesThrough 10
  -- The sleep makes sure that the wait is pending when the worker exits.
  changeFile uri 2 "def a := 1\n#eval show IO Unit from do IO.sleep 1000; IO.Process.forceExit 1\n"
  waitForILeans 11 uri 2
  let mut resps ← collectResponsesUntil (isFatalErrorProgress uri)
  sentinel 12
  resps := resps ++ (← collectResponsesThrough 12)
  IO.println s!"wait pending during the crash: {describe (findResponse resps 11)}"
  waitForILeans 13 uri 2
  waitForILeans 14 uri 1
  sentinel 15
  let laterResps ← collectResponsesThrough 15
  IO.println s!"new wait for v2 after the crash: {describe (findResponse laterResps 13)}"
  IO.println s!"new wait for v1 after the crash: {describe (findResponse laterResps 14)}"

def close : Ipc.IpcM Unit := do
  let uri := "file:///waitsClose.lean"
  openFile uri "def a := 1\n#eval IO.sleep 3000\n"
  waitForILeans 20 uri 1
  Ipc.writeNotification ⟨"textDocument/didClose", {
    textDocument := { uri } : DidCloseTextDocumentParams }⟩
  sentinel 21
  let resps ← collectResponsesThrough 21
  IO.println s!"wait pending during didClose: {describe (findResponse resps 20)}"

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard <| Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
    finalizationOrder
    crash
    close
    Ipc.shutdown 30
    discard Ipc.waitForExit
