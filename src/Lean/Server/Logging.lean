/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
import Std.Time
public import Lean.Data.Lsp.InitShutdown

namespace Lean.Server.Logging

public structure LogConfig where
  isEnabled : Bool
  logFile : System.FilePath
  allowedMethods? : Option (Std.HashSet String)
  disallowedMethods? : Option (Std.HashSet String)

public def LogConfig.ofLspLogConfig (lspCfg? : Option Lsp.LogConfig) : IO LogConfig := do
  let time ← Std.Time.ZonedDateTime.now
  let time := time.format "yyyy-MM-dd-HH-mm-ss-SSSSXX"
  let logFileName := s!"LSP_{time}.log"
  let defaultLogFile : System.FilePath := System.FilePath.join "." logFileName
  let some lspCfg := lspCfg?
    | return {
      isEnabled := false
      logFile := defaultLogFile
      allowedMethods? := none
      disallowedMethods? := none
    }
  return {
    isEnabled := true
    logFile := lspCfg.logDir?.map (System.FilePath.join · logFileName) |>.getD defaultLogFile
    allowedMethods? := lspCfg.allowedMethods?
    disallowedMethods? := lspCfg.disallowedMethods?
  }

open Lean

public inductive MessageMethod where
  | request (method : String)
  | rpcRequest (method : String)
  | notification (method : String)
  deriving Inhabited

def MessageMethod.all : MessageMethod → Array String
  | .request method
  | .notification method =>
    #[method]
  | .rpcRequest method =>
    #["$/lean/rpc/call", method]

public def messageMethod? : JsonRpc.Message → Option MessageMethod
  | .request _ method params? => do
    if method == "$/lean/rpc/call" then
      let params := toJson params?
      if let .ok (callParams : Lsp.RpcCallParams) := fromJson? params then
        return .rpcRequest callParams.method.toString
    return .request method
  | .notification method _ =>
    some <| .notification method
  | _ =>
    none

def messageId? : JsonRpc.Message → Option JsonRpc.RequestID
  | .request id .. => some id
  | .response id .. => some id
  | .responseError id .. => some id
  | _ => none

def isMsgAllowed (cfg : LogConfig)
    (pending : Std.HashMap JsonRpc.RequestID MessageMethod)
    (msg : JsonRpc.Message) : Bool := Id.run do
  if ! cfg.isEnabled then
    return false
  let some method := method?
    | return false
  let allMethods := method.all
  if let some allowedMethods := cfg.allowedMethods? then
    if allMethods.any (! allowedMethods.contains ·) then
      return false
  if let some disallowedMethods := cfg.disallowedMethods? then
    if allMethods.any (disallowedMethods.contains ·) then
      return false
  return true
where
  method? : Option MessageMethod :=
    messageMethod? msg <|> (do pending.get? (← messageId? msg))

local instance : ToJson Std.Time.ZonedDateTime where
  toJson dt := dt.toISO8601String

local instance : FromJson Std.Time.ZonedDateTime where
  fromJson?
    | .str s => Std.Time.ZonedDateTime.fromISO8601String s
    | _ => throw "Expected string when converting JSON to Std.Time.ZonedDateTime"

structure LogEntry where
  time : Std.Time.ZonedDateTime
  direction : JsonRpc.MessageDirection
  kind : JsonRpc.MessageKind
  msg : JsonRpc.Message
  deriving FromJson, ToJson

public def writeLogEntry (cfg : LogConfig) (pending : Std.HashMap JsonRpc.RequestID MessageMethod)
    (log : IO.FS.Handle) (direction : JsonRpc.MessageDirection) (msg : JsonRpc.Message) : IO Unit := do
  if ! isMsgAllowed cfg pending msg then
    return
  let entry : LogEntry := {
    time := ← Std.Time.ZonedDateTime.now
    direction
    kind := .ofMessage msg
    msg
  }
  let entry := toJson entry |>.compress
  log.putStrLn entry
  log.flush
