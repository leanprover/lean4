import Lean.Server.Rpc.Basic

open Lean Server

structure FooRef where
  a : Array Nat
  deriving RpcEncoding with { withRef := true }

structure FooJson where
  s : String
  deriving FromJson, ToJson

structure Bar where
  fooRef : WithRpcRef FooRef
  fooJson : FooJson
  deriving RpcEncoding

structure BarTrans where
  bar : Bar
  deriving RpcEncoding

structure Baz where
  arr : Array String -- non-constant field
  deriving RpcEncoding
