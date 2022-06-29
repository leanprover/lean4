import Lean.Server.Rpc.Basic

open Lean Server

@[reducible]
def rpcPacketFor (α : Type) {β : outParam Type} [RpcEncoding α β] := β

structure FooRef where
  a : Array Nat
  deriving RpcEncoding with { withRef := true }

#synth FromJson (rpcPacketFor (WithRpcRef FooRef))
#synth ToJson (rpcPacketFor (WithRpcRef FooRef))

structure FooJson where
  s : String
  deriving FromJson, ToJson

structure Bar where
  fooRef : WithRpcRef FooRef
  fooJson : FooJson
  deriving RpcEncoding

#synth FromJson (rpcPacketFor Bar)
#synth ToJson (rpcPacketFor Bar)

structure BarTrans where
  bar : Bar
  deriving RpcEncoding

#synth FromJson (rpcPacketFor BarTrans)
#synth ToJson (rpcPacketFor BarTrans)

structure Baz where
  arr : Array String -- non-constant field
  deriving RpcEncoding

#synth FromJson (rpcPacketFor Baz)
#synth ToJson (rpcPacketFor Baz)

structure FooGeneric (α : Type) where
  a : α
  b? : Option α
  deriving RpcEncoding

#synth FromJson (rpcPacketFor <| FooGeneric Nat)
#synth ToJson (rpcPacketFor <| FooGeneric Nat)

inductive FooInductive (α : Type) where
  | a : α → Bar → FooInductive α
  | b : (n : Nat) → (a : α) → Nat → FooInductive α
  deriving RpcEncoding

#synth FromJson (rpcPacketFor <| FooInductive Nat)
#synth ToJson (rpcPacketFor <| FooInductive Nat)
