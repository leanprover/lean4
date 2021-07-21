import Lean.Server.FileWorker.LspEncoding

open Lean Server

structure Foo where
  a : Array Nat
  deriving LspEncoding with { withRef := true }

structure Bar where
  fooRef : WithRpcRef Foo
  deriving LspEncoding
