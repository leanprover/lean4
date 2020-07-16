import Init.System.IO
import Lean.Data.JsonRpc

namespace Lean
namespace Lsp

open IO
open JsonRpc

private def parseHeaderField (s : String) : Option (String × String) :=
if s = "" ∨ s.takeRight 2 ≠ "\r\n" then
  none
else
  let xs := (s.dropRight 2).splitOn ": ";
  match xs with
  | []  => none
  | [_] => none
  | name :: value :: rest =>
    let value := ": ".intercalate (value :: rest);
    some ⟨name, value⟩

private partial def readHeaderFields : FS.Handle → IO (List (String × String))
| h => do
  l ← h.getLine;
  if l = "\r\n" then
    pure []
  else
    match parseHeaderField l with
    | some hf => do
      tail ← readHeaderFields h;
      pure (hf :: tail)
    | none => throw (userError $ "invalid header field" ++ l)

-- Returns the Content-Length.
private def readLspHeader (h : FS.Handle) : IO Nat := do
fields ← readHeaderFields h;
match fields.lookup "Content-Length" with
| some length => match length.toNat? with
  | some n => pure n
  | none   => throw (userError ("Content-Length header value '" ++ length ++ "' is not a Nat"))
| none => throw (userError ("no Content-Length header in header fields " ++ toString fields))

def readLspMessage (h : FS.Handle) : IO Message := do
nBytes ← readLspHeader h;
h.readMessage nBytes

def readLspRequestAs (h : FS.Handle) (expectedMethod : String) (α : Type*) [HasFromJson α] : IO (Request α) := do
nBytes ← readLspHeader h;
h.readRequestAs nBytes expectedMethod α

def readLspRequestNotificationAs (h : FS.Handle) (expectedMethod : String) (α : Type*) [HasFromJson α] : IO α := do
nBytes ← readLspHeader h;
h.readRequestNotificationAs nBytes expectedMethod α

def writeLspMessage (h : FS.Handle) (m : Message) : IO Unit := do
-- inlined implementation instead of using jsonrpc's writeMessage
-- to maintain the atomicity of putStr
let j := (toJson m).compress;
let header := "Content-Length: " ++ toString j.utf8ByteSize ++ "\r\n\r\n";
h.putStr (header ++ j);
h.flush

def writeLspResponse {α : Type*} [HasToJson α] (h : FS.Handle) (id : RequestID) (r : α) : IO Unit :=
writeLspMessage h (Message.response id (toJson r))

def writeLspNotification {α : Type*} [HasToJson α] (h : FS.Handle) (method : String) (r : α) : IO Unit :=
match toJson r with
| Json.obj o => writeLspMessage h (Message.requestNotification method o)
| Json.arr a => writeLspMessage h (Message.requestNotification method a)
| _          => throw (userError "internal server error in Lean.Lsp.writeLspNotification: tried to write lsp notification that is neither a json object nor a json array")

end Lsp
end Lean
