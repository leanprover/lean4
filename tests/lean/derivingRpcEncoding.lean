import Lean.Server.Rpc.Basic

open Lean Server

abbrev M := StateM (Array (Name × NonScalar))

instance : MonadRpcSession M where
  rpcStoreRef typeName obj :=
    (return ⟨(← get).size.toUSize⟩) <* modify (·.push (typeName, obj))
  rpcGetRef r := return (← get)[r.p]?
  rpcReleaseRef _ := return false

def M.run (x : ExceptT String M α) : Except String α := x.run' #[]

def test (α : Type) [RpcEncoding α β] [FromJson β] [ToJson β] (a : α) := M.run do
  let json := toJson (← rpcEncode a)
  let packet ← ofExcept (fromJson? (α := β) json)
  let _ ← rpcDecode (α := α) packet
  return json

@[reducible]
def rpcPacketFor (α : Type) {β : outParam Type} [RpcEncoding α β] := β

structure FooRef where
  a : Array Nat
  deriving Inhabited, RpcEncoding with { withRef := true }

#check instRpcEncodingWithRpcRefFooRefRpcRef
#eval test (WithRpcRef FooRef) default

structure FooJson where
  s : String
  deriving FromJson, ToJson, Inhabited

structure Bar where
  fooRef : WithRpcRef FooRef
  fooJson : FooJson
  deriving RpcEncoding, Inhabited

#check instRpcEncodingBar
#eval test Bar default

structure BarTrans where
  bar : Bar
  deriving RpcEncoding, Inhabited

#check instRpcEncodingBarTrans
#eval test BarTrans default

structure Baz where
  arr : Array String -- non-constant field
  deriving RpcEncoding, Inhabited

#check instRpcEncodingBaz
#eval test Baz default

structure FooGeneric (α : Type) where
  a : α
  b? : Option α
  deriving RpcEncoding, Inhabited

#check instRpcEncodingFooGeneric
#eval test (FooGeneric Nat) default
#eval test (FooGeneric Nat) { a := 3, b? := some 42 }

inductive BazInductive
  | baz (arr : Array Bar)
  deriving RpcEncoding, Inhabited

#check instRpcEncodingBazInductive
#eval test BazInductive ⟨#[default, default]⟩

inductive FooInductive (α : Type) where
  | a : α → WithRpcRef FooRef → FooInductive α
  | b : (n : Nat) → (a : α) → (m : Nat) → FooInductive α
  deriving RpcEncoding, Inhabited

#check instRpcEncodingFooInductive
#eval test (FooInductive BazInductive) (.a default default)
#eval test (FooInductive BazInductive) (.b 42 default default)

inductive FooNested (α : Type) where
  | a : α → Array (FooNested α) → FooNested α
  deriving RpcEncoding, Inhabited

#eval test (FooNested BazInductive) (.a default #[default])

inductive FooParam (n : Nat) where
  | a : Nat → FooParam n
  deriving RpcEncoding, Inhabited

#check instRpcEncodingFooParam
#eval test (FooParam 10) (.a 42)

inductive Unused (α : Type) | a
  deriving RpcEncoding, Inhabited

#check instRpcEncodingUnused
structure NoRpcEncoding
#eval test (Unused NoRpcEncoding) default

structure UnusedStruct (α : Type)
  deriving RpcEncoding, Inhabited

#check instRpcEncodingUnusedStruct
#eval test (UnusedStruct NoRpcEncoding) default

deriving instance Repr, RpcEncoding for Empty
#eval M.run do rpcDecode (α := Empty) (← fromJson? .null)
