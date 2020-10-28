/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.Control
import Init.System.IO
import Std.Data.RBTree
import Lean.Data.Json

/-! Implementation of JSON-RPC 2.0 (https://www.jsonrpc.org/specification)
for use in the LSP server. -/

namespace Lean
namespace JsonRpc

open Json
open Std (RBNode)

inductive RequestID
  | str (s : String)
  | num (n : JsonNumber)
  | null

/-- Error codes defined by JSON-RPC and LSP. -/
inductive ErrorCode
  | parseError
  | invalidRequest
  | methodNotFound
  | invalidParams
  | internalError
  | serverErrorStart
  | serverErrorEnd
  | serverNotInitialized
  | unknownErrorCode
  -- LSP-specific codes below.
  | requestCancelled
  | contentModified

instance : FromJson ErrorCode := ⟨fun j =>
  match j with
  | num (-32700 : Int) => ErrorCode.parseError
  | num (-32600 : Int) => ErrorCode.invalidRequest
  | num (-32601 : Int) => ErrorCode.methodNotFound
  | num (-32602 : Int) => ErrorCode.invalidParams
  | num (-32603 : Int) => ErrorCode.internalError
  | num (-32099 : Int) => ErrorCode.serverErrorStart
  | num (-32000 : Int) => ErrorCode.serverErrorEnd
  | num (-32002 : Int) => ErrorCode.serverNotInitialized
  | num (-32001 : Int) => ErrorCode.unknownErrorCode
  | num (-32800 : Int) => ErrorCode.requestCancelled
  | num (-32801 : Int) => ErrorCode.contentModified
  | _  => none⟩

instance : ToJson ErrorCode := ⟨fun e =>
  match e with
  | ErrorCode.parseError           => (-32700 : Int)
  | ErrorCode.invalidRequest       => (-32600 : Int)
  | ErrorCode.methodNotFound       => (-32601 : Int)
  | ErrorCode.invalidParams        => (-32602 : Int)
  | ErrorCode.internalError        => (-32603 : Int)
  | ErrorCode.serverErrorStart     => (-32099 : Int)
  | ErrorCode.serverErrorEnd       => (-32000 : Int)
  | ErrorCode.serverNotInitialized => (-32002 : Int)
  | ErrorCode.unknownErrorCode     => (-32001 : Int)
  | ErrorCode.requestCancelled     => (-32800 : Int)
  | ErrorCode.contentModified      => (-32801 : Int)⟩

/- Uses separate constructors for notifications and errors because client and server
behavior is expected to be wildly different for both. -/
inductive Message
  | request (id : RequestID) (method : String) (params? : Option Structured)
  | notification (method : String) (params? : Option Structured)
  | response (id : RequestID) (result : Json)
  | responseError (id : RequestID) (code : ErrorCode) (message : String) (data? : Option Json)

def Batch := Array Message

-- data types for reading expected messages
structure Request (α : Type) := (id : RequestID) (param : α)
structure Response (α : Type) := (id : RequestID) (result : α)
structure Error := (id : RequestID) (code : JsonNumber) (message : String) (data? : Option Json)

instance : Coe String RequestID := ⟨RequestID.str⟩
instance : Coe JsonNumber RequestID := ⟨RequestID.num⟩

instance : FromJson RequestID := ⟨fun j =>
  match j with
  | str s => RequestID.str s
  | num n => RequestID.num n
  | _     => none⟩

instance : ToJson RequestID := ⟨fun rid =>
  match rid with
  | RequestID.str s => s
  | RequestID.num n => num n
  | RequestID.null  => null⟩

instance : ToJson Message := ⟨fun m =>
  mkObj $ ⟨"jsonrpc", "2.0"⟩ :: match m with
  | Message.request id method params? =>
    [ ⟨"id", toJson id⟩,
      ⟨"method", method⟩
    ] ++ opt "params" params?
  | Message.notification method params? =>
    ⟨"method", method⟩ ::
    opt "params" params?
  | Message.response id result =>
    [ ⟨"id", toJson id⟩,
      ⟨"result", result⟩]
  | Message.responseError id code message data? =>
    [ ⟨"id", toJson id⟩,
      ⟨"error", mkObj $ [
          ⟨"code", toJson code⟩,
          ⟨"message", message⟩
        ] ++ opt "data" data?⟩
    ]⟩

def aux1 (j : Json) : Option Message := do
  let id ← j.getObjValAs? RequestID "id"
  let method ← j.getObjValAs? String "method"
  let params? := j.getObjValAs? Structured "params"
  pure (Message.request id method params?)

def aux2 (j : Json) : Option Message := do
  let method ← j.getObjValAs? String "method"
  let params? := j.getObjValAs? Structured "params"
  pure (Message.notification method params?)

def aux3 (j : Json) : Option Message := do
  let id ← j.getObjValAs? RequestID "id"
  let result ← j.getObjVal? "result"
  pure (Message.response id result)

def aux4 (j : Json) : Option Message := do
  let id ← j.getObjValAs? RequestID "id"
  let err ← j.getObjVal? "error"
  let code ← err.getObjValAs? ErrorCode "code"
  let message ← err.getObjValAs? String "message"
  let data? := err.getObjVal? "data";
  pure (Message.responseError id code message data?)

-- HACK: The implementation must be made up of several `auxN`s instead
-- of one large block because of a bug in the compiler.
instance : FromJson Message := ⟨fun j => do
  let "2.0" ← j.getObjVal? "jsonrpc" | none
  aux1 j <|> aux2 j <|> aux3 j <|> aux4 j⟩

end JsonRpc
end Lean

namespace IO.FS.Stream

open Lean
open Lean.JsonRpc
open IO

def readMessage (h : FS.Stream) (nBytes : Nat) : IO Message := do
  let j ← h.readJson nBytes
  match fromJson? j with
  | some m => pure m
  | none   => throw (userError ("JSON '" ++ j.compress ++ "' did not have the format of a JSON-RPC message"))

def readRequestAs (h : FS.Stream) (nBytes : Nat) (expectedMethod : String) (α : Type) [FromJson α] : IO (Request α) := do
  let m ← h.readMessage nBytes
  match m with
  | Message.request id method params? =>
    if method = expectedMethod then
      match params? with
      | some params =>
        let j := toJson params
        match fromJson? j with
        | some v => pure ⟨id, v⟩
        | none   => throw (userError ("unexpected param '" ++ j.compress  ++ "' for method '" ++ expectedMethod ++ "'"))
      | none => throw (userError ("unexpected lack of param for method '" ++ expectedMethod ++ "'"))
    else
      throw (userError ("expected method '" ++ expectedMethod ++ "', got method '" ++ method ++ "'"))
  | _ => throw (userError "expected request, got other type of message")

def readNotificationAs (h : FS.Stream) (nBytes : Nat) (expectedMethod : String) (α : Type) [FromJson α] : IO α := do
  let m ← h.readMessage nBytes
  match m with
  | Message.notification method params? =>
    if method = expectedMethod then
      match params? with
      | some params =>
        let j := toJson params;
        match fromJson? j with
        | some v => pure v
        | none   => throw (userError ("unexpected param '" ++ j.compress  ++ "' for method '" ++ expectedMethod ++ "'"))
      | none => throw (userError ("unexpected lack of param for method '" ++ expectedMethod ++ "'"))
    else
      throw (userError ("expected method '" ++ expectedMethod ++ "', got method '" ++ method ++ "'"))
  | _ => throw (userError "expected notification, got other type of message")

def writeMessage (h : FS.Stream) (m : Message) : IO Unit :=
  h.writeJson (toJson m)

def writeResponse {α} [ToJson α] (h : FS.Stream) (id : RequestID) (r : α) : IO Unit :=
  h.writeMessage (Message.response id (toJson r))

end IO.FS.Stream
