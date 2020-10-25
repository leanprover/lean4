/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Lean.Data.JsonRpc

/-! Reading/writing LSP messages from/to IO handles. -/

namespace Lean
namespace Lsp

open IO
open JsonRpc

private def parseHeaderField (s : String) : Option (String × String) :=
  if s = "" ∨ s.takeRight 2 ≠ "\r\n" then
    none
  else
    let xs := (s.dropRight 2).splitOn ": "
    match xs with
    | []  => none
    | [_] => none
    | name :: value :: rest =>
      let value := ": ".intercalate (value :: rest)
      some ⟨name, value⟩

variables {m : Type → Type} [Monad m] [MonadIO m]

private partial def readHeaderFields (h : FS.Stream) : m (List (String × String)) := do
  let l ← liftIO $ h.getLine
  if l = "\r\n" then
    pure []
  else
    match parseHeaderField l with
    | some hf =>
      let tail ← readHeaderFields h
      pure (hf :: tail)
    | none => liftIO $ throw (userError $ "Invalid header field: " ++ l)

/-- Returns the Content-Length. -/
private def readLspHeader (h : FS.Stream) : m Nat := do
  let fields ← readHeaderFields h
  match fields.lookup "Content-Length" with
  | some length => match length.toNat? with
    | some n => pure n
    | none   => liftIO $ throw (userError ("Content-Length header value '" ++ length ++ "' is not a Nat"))
  | none => liftIO $ throw (userError ("No Content-Length header in header fields: " ++ toString fields))

def readLspMessage (h : FS.Stream) : m Message := do
  let nBytes ← readLspHeader h
  liftIO $ h.readMessage nBytes

def readLspRequestAs (h : FS.Stream) (expectedMethod : String) (α : Type) [FromJson α] : m (Request α) := do
  let nBytes ← readLspHeader h
  liftIO $ h.readRequestAs nBytes expectedMethod α

def readLspNotificationAs (h : FS.Stream) (expectedMethod : String) (α : Type) [FromJson α] : m α := do
  let nBytes ← readLspHeader h
  liftIO $ h.readNotificationAs nBytes expectedMethod α

def writeLspMessage (h : FS.Stream) (msg : Message) : m Unit := do
  -- inlined implementation instead of using jsonrpc's writeMessage
  -- to maintain the atomicity of putStr
  let j := (toJson msg).compress
  let header := "Content-Length: " ++ toString j.utf8ByteSize ++ "\r\n\r\n"
  liftIO $ h.putStr (header ++ j)
  liftIO $ h.flush

def writeLspRequest {α : Type} [ToJson α] (h : FS.Stream) (id : RequestID) (method : String) (params : α) : m Unit :=
  writeLspMessage h (Message.request id method (fromJson? (toJson params)))

def writeLspNotification {α : Type} [ToJson α] (h : FS.Stream) (method : String) (r : α) : m Unit :=
  writeLspMessage h (Message.notification method (fromJson? (toJson r)))

def writeLspResponse {α : Type} [ToJson α] (h : FS.Stream) (id : RequestID) (r : α) : m Unit :=
  writeLspMessage h (Message.response id (toJson r))

def writeLspResponseError (h : FS.Stream) (id : RequestID) (code : ErrorCode) (message : String) : m Unit :=
  writeLspMessage h (Message.responseError id code message none)

def writeLspResponseErrorWithData {α : Type} [ToJson α] (h : FS.Stream) (id : RequestID) (code : ErrorCode) (message : String) (data : α) : m Unit :=
  writeLspMessage h (Message.responseError id code message (toJson data))

end Lsp
end Lean
