import Init.Control
import Init.System.IO
import Lean.Data.Json

namespace Lean.JsonRpc

open Lean
open Lean.Json

inductive RequestID
| str (s : String)
| num (n : JsonNumber)
| null

inductive Structured
| arr (elems : Array Json)
| obj (kvPairs : RBNode String (fun _ => Json))

-- uses Option Structured because users will likely rarely distinguish between an empty
-- parameter array and an omitted params field.
-- uses seperate constructors for notifications and errors because client and server
-- behavior is expected to be wildly different for both.
inductive Message
| request (id : RequestID) (method : String) (params? : Option Structured)
| requestNotification (method : String) (params? : Option Structured)
| response (id : RequestID) (result : Json)
| responseError (id : RequestID) (code : JsonNumber) (message : String) (data? : Option Json)

def Batch := Array Message

-- data types for reading expected messages
structure Request (α : Type*) := (id : RequestID) (param : α)
structure Response (α : Type*) := (id : RequestID) (result : α)
structure Error := (id : RequestID) (code : JsonNumber) (message : String) (data? : Option Json)

instance stringToRequestID : HasCoe String RequestID := ⟨RequestID.str⟩
instance numToRequestID : HasCoe JsonNumber RequestID := ⟨RequestID.num⟩

instance arrayToStructured : HasCoe (Array Json) Structured := ⟨Structured.arr⟩
instance kvPairsToStructured : HasCoe (RBNode String (fun _ => Json)) Structured := ⟨Structured.obj⟩

instance requestIDToJson : HasToJson RequestID :=
⟨fun rid => match rid with
  | RequestID.str s => s
  | RequestID.num n => num n
  | RequestID.null  => null⟩
instance requestIDFromJson : HasFromJson RequestID :=
⟨fun j => match j with 
  | str s => RequestID.str s
  | num n => RequestID.num n
  | _     => none⟩

instance structuredToJson : HasToJson Structured :=
⟨fun s => match s with
  | Structured.arr a => arr a
  | Structured.obj o => obj o⟩
instance structuredFromJson : HasFromJson Structured :=
⟨fun j => match j with
  | arr a => Structured.arr a
  | obj o => Structured.obj o
  | _     => none⟩

instance messageToJson : HasToJson Message :=
⟨fun m =>   
  mkObj $ ⟨"jsonrpc", "2.0"⟩ :: match m with
  | Message.request id method params? =>
    [⟨"id", toJson id⟩, ⟨"method", method⟩] ++ opt "params" params?
  | Message.requestNotification method params? =>
    ⟨"method", method⟩ :: opt "params" params?
  | Message.response id result =>
    [⟨"id", toJson id⟩, ⟨"result", result⟩]
  | Message.responseError id code message data? =>
    [⟨"id", toJson id⟩, 
     ⟨"error", mkObj $ 
       [⟨"code", toJson code⟩, ⟨"message", message⟩] ++ opt "data" data?⟩]⟩

def aux1 (j : Json) : Option Message := do
id ← j.getObjValAs? RequestID "id";
method ← j.getObjValAs? String "method";
let params? := j.getObjValAs? Structured "params";
pure (Message.request id method params?)

def aux2 (j : Json) : Option Message := do
method ← j.getObjValAs? String "method";
let params? := j.getObjValAs? Structured "params";
pure (Message.requestNotification method params?)

def aux3 (j : Json) : Option Message := do
id ← j.getObjValAs? RequestID "id";
result ← j.getObjVal? "result";
pure (Message.response id result)

def aux4 (j : Json) : Option Message := do
id ← j.getObjValAs? RequestID "id";
err ← j.getObjVal? "error";
code ← err.getObjValAs? JsonNumber "code";
message ← err.getObjValAs? String "message";
let data? := err.getObjVal? "data";
pure (Message.responseError id code message data?)

instance messageFromJson : HasFromJson Message :=
⟨fun j => do
  "2.0" ← j.getObjVal? "jsonrpc" | none;
  aux1 j <|> aux2 j <|> aux3 j <|> aux4 j⟩

end Lean.JsonRpc

namespace IO.FS.Handle

open Lean
open Lean.JsonRpc
open IO

def readMessage (h : FS.Handle) (nBytes : Nat) : IO Message := do
j ← h.readJson nBytes;
match fromJson? j with
| some m => pure m
| none   => throw (userError ("json '" ++ j.compress ++ "' did not have the format of a jsonrpc message"))

def readRequestAs (h : FS.Handle) (nBytes : Nat) (expectedMethod : String) (α : Type*) [HasFromJson α] : IO (Request α) := do
m ← h.readMessage nBytes;
match m with
| Message.request id method params? =>
  if method = expectedMethod then
    match params? with
    | some params => 
      let j := toJson params;
      match fromJson? j with
      | some v => pure ⟨id, v⟩
      | none   => throw (userError ("unexpected param '" ++ j.compress  ++ "' for method '" ++ expectedMethod ++ "'"))
    | none => throw (userError ("unexpected lack of param for method '" ++ expectedMethod ++ "'"))
  else
    throw (userError ("expected method '" ++ expectedMethod ++ "', got method '" ++ method ++ "'"))
| _ => throw (userError "expected request, got other type of message")

def readRequestNotificationAs (h : FS.Handle) (nBytes : Nat) (expectedMethod : String) (α : Type*) [HasFromJson α] : IO α := do
m ← h.readMessage nBytes;
match m with
| Message.requestNotification method params? =>
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

def writeMessage (h : FS.Handle) (m : Message) : IO Unit :=
h.writeJson (toJson m)

def writeResponse {α : Type*} [HasToJson α] (h : FS.Handle) (id : RequestID) (r : α) : IO Unit :=
h.writeMessage (Message.response id (toJson r))

end IO.FS.Handle
