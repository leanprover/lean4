/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Json

/-! Allows LSP clients to make Remote Procedure Calls to the server.

The single use case for these is to allow the infoview UI to refer to and manipulate heavy-weight
objects residing on the server. It would be inefficient to serialize these into JSON and send over.
For example, the client can format an `Expr` without transporting the whole `Environment`.

All RPC requests are relative to an open file and an RPC session for that file. The client must
first connect to the session using `$/lean/rpc/connect`. -/

namespace Lean.Lsp

/-- An object which RPC clients can refer to without marshalling. -/
structure RpcRef where
  /- NOTE(WN): It is important for this to be a single-field structure
  in order to deserialize as an `Object` on the JS side. -/
  p : USize
  deriving BEq, Hashable, FromJson, ToJson

instance : ToString RpcRef where
  toString r := toString r.p

end Lean.Lsp

namespace Lean.Server

structure RpcObjectStore : Type where
  /-- Objects that are being kept alive for the RPC client, together with their type names,
  mapped to by their RPC reference.

  Note that we may currently have multiple references to the same object. It is only disposed
  of once all of those are gone. This simplifies the client a bit as it can drop every reference
  received separately. -/
  aliveRefs : PersistentHashMap Lsp.RpcRef Dynamic := {}
  /-- Value to use for the next `RpcRef`. It is monotonically increasing to avoid any possible
  bugs resulting from its reuse. -/
  nextRef   : USize := 0

def rpcStoreRef (any : Dynamic) : StateM RpcObjectStore Lsp.RpcRef := do
  let st ← get
  set { st with
    aliveRefs := st.aliveRefs.insert ⟨st.nextRef⟩ any
    nextRef := st.nextRef + 1
  }
  return ⟨st.nextRef⟩

def rpcGetRef (r : Lsp.RpcRef) : ReaderT RpcObjectStore Id (Option Dynamic) :=
  return (← read).aliveRefs.find? r

def rpcReleaseRef (r : Lsp.RpcRef) : StateM RpcObjectStore Bool := do
  let st ← get
  if st.aliveRefs.contains r then
    set { st with aliveRefs := st.aliveRefs.erase r }
    return true
  else
    return false

/--
`RpcEncodable α` means that `α` can be serialized in the RPC system of the Lean server.
This is required when `α` contains fields which should be serialized as an RPC reference
instead of being sent in full.
The type wrapper `WithRpcRef` is used for these fields which should be sent as
a reference.

- Any type with `FromJson` and `ToJson` instance is automatically `RpcEncodable`.
- If a type has an `Dynamic` instance, then `WithRpcRef` can be used for its references.
- `deriving RpcEncodable` acts like `FromJson`/`ToJson` but marshalls any `WithRpcRef` fields
  as `Lsp.RpcRef`s.
-/
-- TODO(WN): for Lean.js, compile `WithRpcRef` to "opaque reference" on the client
class RpcEncodable (α : Type) where
  rpcEncode : α → StateM RpcObjectStore Json
  rpcDecode : Json → ExceptT String (ReaderT RpcObjectStore Id) α
export RpcEncodable (rpcEncode rpcDecode)

instance : Nonempty (RpcEncodable α) :=
  ⟨{ rpcEncode := default, rpcDecode := default }⟩

instance [FromJson α] [ToJson α] : RpcEncodable α where
  rpcEncode a := return toJson a
  rpcDecode j := ofExcept (fromJson? j)

instance [RpcEncodable α] : RpcEncodable (Option α) where
  rpcEncode v := toJson <$> v.mapM rpcEncode
  rpcDecode j := do Option.mapM rpcDecode (← fromJson? j)

-- TODO(WN): instance [RpcEncodable α β] [Traversable t] : RpcEncodable (t α) (t β)

instance [RpcEncodable α] : RpcEncodable (Array α) where
  rpcEncode a := toJson <$> a.mapM rpcEncode
  rpcDecode b := do Array.mapM rpcDecode (← fromJson? b)

instance [RpcEncodable α] [RpcEncodable β] : RpcEncodable (α × β) where
  rpcEncode := fun (a, b) => return toJson (← rpcEncode a, ← rpcEncode b)
  rpcDecode j := do
    let (a, b) ← fromJson? j
    return (← rpcDecode a, ← rpcDecode b)

/-- Marks fields to encode as opaque references in LSP packets. -/
structure WithRpcRef (α : Type u) where
  val : α
  deriving Inhabited

instance [TypeName α] : RpcEncodable (WithRpcRef α) :=
  { rpcEncode, rpcDecode }
where
  -- separate definitions to prevent inlining
  rpcEncode r := toJson <$> rpcStoreRef (.mk r.val)
  rpcDecode j := do
    let r ← fromJson? j
    match (← rpcGetRef r) with
      | none => throw s!"RPC reference '{r}' is not valid"
      | some any =>
        if let some obj := any.get? α then
          return ⟨obj⟩
        else
          throw s!"RPC call type mismatch in reference '{r}'\nexpected '{TypeName.typeName α}', got '{any.typeName}'"

end Lean.Server
