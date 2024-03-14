/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Data.Json

open Lean

inductive MessageType where
  | error
  | warning
  | info
  | log

instance : FromJson MessageType where
  fromJson?
    | (1 : Nat) => .ok .error
    | (2 : Nat) => .ok .warning
    | (3 : Nat) => .ok .info
    | (4 : Nat) => .ok .log
    | _         => .error "Unknown MessageType ID"

instance : ToJson MessageType where
  toJson
    | .error   => 1
    | .warning => 2
    | .info    => 3
    | .log     => 4

structure ShowMessageParams where
  type    : MessageType
  message : String
  deriving FromJson, ToJson

structure MessageActionItem where
  title : String
  deriving FromJson, ToJson

structure ShowMessageRequestParams where
  type     : MessageType
  message  : String
  actions? : Option (Array MessageActionItem)
  deriving FromJson, ToJson

def ShowMessageResponse := Option MessageActionItem
  deriving FromJson, ToJson
