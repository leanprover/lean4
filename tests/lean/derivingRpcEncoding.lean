import Lean.Server.Rpc.Basic

open Lean Server

abbrev M := StateM RpcObjectStore

def M.run (x : ExceptT String M α) : Except String α :=
  x.run' {}

def test (α : Type) [RpcEncodable α] (a : α) := M.run do
  let json ← rpcEncode a
  let _a : α ← ofExcept (rpcDecode json (← get))
  return json

structure FooRef where
  a : Array Nat
  deriving Inhabited, TypeName

#eval do return test (WithRpcRef FooRef) (← WithRpcRef.mk default)

structure FooJson where
  s : String
  deriving FromJson, ToJson, Inhabited

structure Bar where
  fooRef : WithRpcRef FooRef
  fooJson : FooJson
  deriving RpcEncodable, Inhabited

def Bar.mkDefault : BaseIO Bar := do return {
  fooRef  := ← WithRpcRef.mk default
  fooJson := default
}

#eval do return test Bar (← Bar.mkDefault)

structure BarTrans where
  bar : Bar
  deriving RpcEncodable, Inhabited

#eval do return test BarTrans { bar := ← Bar.mkDefault }

structure Baz where
  arr : Array String -- non-constant field
  deriving RpcEncodable, Inhabited

#eval test Baz default

structure FooGeneric (α : Type) where
  a : α
  b? : Option α
  deriving RpcEncodable, Inhabited

#eval test (FooGeneric Nat) default
#eval test (FooGeneric Nat) { a := 3, b? := some 42 }

inductive BazInductive
  | baz (arr : Array Bar)
  deriving RpcEncodable, Inhabited

#eval do return test BazInductive ⟨#[← Bar.mkDefault, ← Bar.mkDefault]⟩

inductive FooInductive (α : Type) where
  | a : α → WithRpcRef FooRef → FooInductive α
  | b : (n : Nat) → (a : α) → (m : Nat) → FooInductive α
  deriving RpcEncodable, Inhabited

#eval do return test (FooInductive BazInductive) (.a default (← WithRpcRef.mk default))
#eval do return test (FooInductive BazInductive) (.b 42 default default)

inductive FooNested (α : Type) where
  | a : α → Array (FooNested α) → FooNested α
  deriving RpcEncodable, Inhabited

#eval test (FooNested BazInductive) (.a default #[default])

inductive FooParam (n : Nat) where
  | a : Nat → FooParam n
  deriving RpcEncodable, Inhabited

#eval test (FooParam 10) (.a 42)

inductive Unused (α : Type) | a
  deriving RpcEncodable, Inhabited

structure NoRpcEncodable
#eval test (Unused NoRpcEncodable) default

structure UnusedStruct (α : Type)
  deriving RpcEncodable, Inhabited

#eval test (UnusedStruct NoRpcEncodable) default

deriving instance Repr, RpcEncodable for Empty
#eval rpcDecode (α := Empty) .null {}
