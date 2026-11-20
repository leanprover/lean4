import Lean.Data.Lsp

/-!
Tests that `$/lean/rpc/call` requests for user RPC methods that arrive while the file is still being
elaborated do not block in a `sync` task, which makes the runtime print a panic. The proof of
`slow` is elaborated asynchronously and still runs when the requests arrive.
-/

open IO Lean Lsp

def uri : DocumentUri := "file:///rpcDuringElab.lean"

def text : String := "import Lean
open Lean Server

theorem slow : True := by
  sleep 1500
  trivial

@[server_rpc_method]
def answer (_ : Nat) : RequestM (RequestTask Nat) :=
  return .pure 42
"

def responseId? : JsonRpc.Message → Option JsonRpc.RequestID
  | .response id _ | .responseError id .. => some id
  | _ => none

/-- Reads messages until the responses for all of `ids` have arrived, and returns them. -/
partial def readResponses (ids : List Nat) (acc : Array JsonRpc.Message := #[]) :
    Ipc.IpcM (Array JsonRpc.Message) := do
  if ids.all fun id => acc.any (responseId? · == some (id : JsonRpc.RequestID)) then
    return acc
  let msg ← Ipc.readMessage
  readResponses ids (if (responseId? msg).isSome then acc.push msg else acc)

def describe : Option JsonRpc.Message → String
  | some (.response _ result) => result.compress
  | some (.responseError _ code message _) => s!"error {(toJson code).compress}: {message}"
  | some msg => s!"unexpected message {(toJson msg).compress}"
  | none => "no response"

def call (id : Nat) (sessionId : UInt64) (method : Name) : Ipc.IpcM Unit :=
  Ipc.writeRequest ⟨id, "$/lean/rpc/call", {
    textDocument := { uri }, position := ⟨10, 0⟩, sessionId, method, params := toJson 0
    : RpcCallParams }⟩

def main : IO Unit := do
  Ipc.runWith "lean" #["--server"] do
    let hIn ← Ipc.stdin
    hIn.write (← FS.readBinFile "init_vscode_1_47_2.log")
    hIn.flush
    discard <| Ipc.readResponseAs 0 InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
    Ipc.writeNotification ⟨"textDocument/didOpen", {
      textDocument := { uri, languageId := "lean", version := 1, text }
      : DidOpenTextDocumentParams }⟩
    Ipc.writeRequest ⟨1, "$/lean/rpc/connect", { uri : RpcConnectParams }⟩
    let session ← Ipc.readResponseAs 1 RpcConnected
    call 2 session.result.sessionId `answer
    call 3 session.result.sessionId `doesNotExist
    let resps ← readResponses [2, 3]
    let find (id : Nat) := resps.find? (responseId? · == some (id : JsonRpc.RequestID))
    IO.println s!"answer: {describe (find 2)}"
    IO.println s!"doesNotExist: {describe (find 3)}"
    Ipc.shutdown 4
    IO.println s!"watchdog exit code: {← Ipc.waitForExit}"
