import Lean.Server.FileWorker.LspEncoding

open Lean Server

structure FooRef where
  a : Array Nat
  deriving LspEncoding with { withRef := true }

structure FooJson where
  s : String
  deriving FromJson, ToJson

structure Bar where
  fooRef : WithRpcRef FooRef
  fooJson : FooJson
  deriving LspEncoding

structure BarTrans where
  bar : Bar
  deriving LspEncoding

structure Baz where
  arr : Array String -- non-constant field
  deriving LspEncoding
