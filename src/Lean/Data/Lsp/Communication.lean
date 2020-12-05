/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Lean.Data.JsonRpc

/-! Reading/writing LSP messages from/to IO handles. -/

namespace IO.FS.Stream

open Lean
open Lean.JsonRpc

section
  variables (h : FS.Stream) (expectedMethod : String) (α) [FromJson α]

  private def parseHeaderField (s : String) : Option (String × String) := do
    guard $ s ≠ "" ∧ s.takeRight 2 = "\r\n"
    let xs := (s.dropRight 2).splitOn ": "
    match xs with
    | []  => none
    | [_] => none
    | name :: value :: rest =>
      let value := ": ".intercalate (value :: rest)
      some ⟨name, value⟩

  private partial def readHeaderFields : IO (List (String × String)) := do
    let l ← h.getLine
    if l = "\r\n" then
      pure []
    else
      match parseHeaderField l with
      | some hf =>
        let tail ← readHeaderFields
        pure (hf :: tail)
      | none => throw $ userError ("Invalid header field: " ++ l)

  /-- Returns the Content-Length. -/
  private def readLspHeader : IO Nat := do
    let fields ← readHeaderFields h
    match fields.lookup "Content-Length" with
    | some length => match length.toNat? with
      | some n => pure n
      | none   => throw $ userError ("Content-Length header value '" ++ length ++ "' is not a Nat")
    | none => throw $ userError ("No Content-Length header in header fields: " ++ toString fields)

  def readLspMessage : IO Message := do
    let nBytes ← readLspHeader h
    h.readMessage nBytes

  def readLspRequestAs : IO (Request α) := do
    let nBytes ← readLspHeader h
    h.readRequestAs nBytes expectedMethod α

  def readLspNotificationAs : IO (Notification α) := do
    let nBytes ← readLspHeader h
    h.readNotificationAs nBytes expectedMethod α
end

section
  variables [ToJson α] (h : FS.Stream)

  def writeLspMessage (h : FS.Stream) (msg : Message) : IO Unit := do
    -- inlined implementation instead of using jsonrpc's writeMessage
    -- to maintain the atomicity of putStr
    let j := (toJson msg).compress
    let header := "Content-Length: " ++ toString j.utf8ByteSize ++ "\r\n\r\n"
    h.putStr (header ++ j)
    h.flush

  def writeLspRequest (r : Request α): IO Unit :=
    h.writeLspMessage r

  def writeLspNotification (n : Notification α) : IO Unit :=
    h.writeLspMessage n

  def writeLspResponse (r : Response α) : IO Unit :=
    h.writeLspMessage r

  def writeLspResponseError (e : ResponseError Unit) : IO Unit :=
    h.writeLspMessage (Message.responseError e.id e.code e.message none)

  def writeLspResponseErrorWithData (e : ResponseError α) : IO Unit :=
    h.writeLspMessage e
end

end IO.FS.Stream
