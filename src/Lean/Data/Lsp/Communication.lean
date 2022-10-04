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
  private def parseHeaderField (s : String) : Option (String × String) := do
    guard $ s ≠ "" ∧ s.takeRight 2 = "\r\n"
    let xs := (s.dropRight 2).splitOn ": "
    match xs with
    | []  => none
    | [_] => none
    | name :: value :: rest =>
      let value := ": ".intercalate (value :: rest)
      some ⟨name, value⟩

  /-- Returns true when the string is a Lean 3 request.
  This means that the user is running a Lean 3 language client that
  is not aware of Lean 4. In this case we should give a friendlier message. -/
  private def isLean3Request (s : String) : Bool :=
    let e : Except String Unit := (do
      let j ← Json.parse s
      let _ ← j.getObjVal? "command"
      let _ ← j.getObjVal? "seq_num"
      return ()
    )
    e.isOk

  private partial def readHeaderFields (h : FS.Stream) : IO (List (String × String)) := do
    let l ← h.getLine
    if l.isEmpty then
      throw $ userError "Stream was closed"
    if l = "\r\n" then
      pure []
    else
      match parseHeaderField l with
      | some hf =>
        let tail ← readHeaderFields h
        pure (hf :: tail)
      | none =>
        if isLean3Request l then
          throw $ userError s!"A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 "
        else
          throw $ userError s!"Invalid header field: {repr l}"

  /-- Returns the Content-Length. -/
  private def readLspHeader (h : FS.Stream) : IO Nat := do
    let fields ← readHeaderFields h
    match fields.lookup "Content-Length" with
    | some length => match length.toNat? with
      | some n => pure n
      | none   => throw $ userError s!"Content-Length header field value '{length}' is not a Nat"
    | none => throw $ userError s!"No Content-Length field in header: {fields}"

  def readLspMessage (h : FS.Stream) : IO Message := do
    try
      let nBytes ← readLspHeader h
      h.readMessage nBytes
    catch e =>
      throw $ userError s!"Cannot read LSP message: {e}"

  def readLspRequestAs (h : FS.Stream) (expectedMethod : String) (α) [FromJson α] : IO (Request α) := do
    try
      let nBytes ← readLspHeader h
      h.readRequestAs nBytes expectedMethod α
    catch e =>
      throw $ userError s!"Cannot read LSP request: {e}"

  def readLspNotificationAs (h : FS.Stream) (expectedMethod : String) (α) [FromJson α] : IO (Notification α) := do
    try
      let nBytes ← readLspHeader h
      h.readNotificationAs nBytes expectedMethod α
    catch e =>
      throw $ userError s!"Cannot read LSP notification: {e}"

  def readLspResponseAs (h : FS.Stream) (expectedID : RequestID) (α) [FromJson α] : IO (Response α) := do
    try
      let nBytes ← readLspHeader h
      h.readResponseAs nBytes expectedID α
    catch e =>
      throw $ userError s!"Cannot read LSP response: {e}"
end

section
  variable [ToJson α]

  def writeLspMessage (h : FS.Stream) (msg : Message) : IO Unit := do
    -- inlined implementation instead of using jsonrpc's writeMessage
    -- to maintain the atomicity of putStr
    let j := (toJson msg).compress
    let header := s!"Content-Length: {toString j.utf8ByteSize}\r\n\r\n"
    h.putStr (header ++ j)
    h.flush

  def writeLspRequest (h : FS.Stream) (r : Request α) : IO Unit :=
    h.writeLspMessage r

  def writeLspNotification (h : FS.Stream) (n : Notification α) : IO Unit :=
    h.writeLspMessage n

  def writeLspResponse (h : FS.Stream) (r : Response α) : IO Unit :=
    h.writeLspMessage r

  def writeLspResponseError (h : FS.Stream) (e : ResponseError Unit) : IO Unit :=
    h.writeLspMessage (Message.responseError e.id e.code e.message none)

  def writeLspResponseErrorWithData (h : FS.Stream) (e : ResponseError α) : IO Unit :=
    h.writeLspMessage e
end

end IO.FS.Stream
