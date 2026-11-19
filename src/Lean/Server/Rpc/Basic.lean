/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
module

prelude
public import Init.Dynamic
public import Lean.Data.Json.FromToJson.Basic

public section

/-! Allows LSP clients to make Remote Procedure Calls to the server.

The single use case for these is to allow the infoview UI to refer to and manipulate heavy-weight
objects residing on the server. It would be inefficient to serialize these into JSON and send over.
For example, the client can format an `Expr` without transporting the whole `Environment`.

All RPC requests are relative to an open file and an RPC session for that file. The client must
first connect to the session using `$/lean/rpc/connect`. -/

namespace Lean.Lsp

/--
The address of an object in an `RpcObjectStore` that clients can refer to.
Its JSON encoding depends on the RPC wire format.

The language server may serve the same `RpcRef` multiple times.
It maintains a reference count to track how many times it has served the reference.
If clients want to release the object associated with an `RpcRef`,
they must release the reference as many times as they have received it from the server.
-/
structure RpcRef where
  p : USize
  deriving Inhabited, BEq, Hashable

instance : ToString RpcRef where
  toString r := toString r.p

/-- The *RPC wire format* specifies how user data is encoded in RPC requests. -/
inductive RpcWireFormat where
  /-- Version `0` uses JSON.
  Serialized RPC data is stored directly in `RpcCallParams.params` and in `JsonRpc.Response.result`
  (as opposed to being wrapped in additional metadata).
  General types (except RPC references) are (de)serialized via `ToJson/FromJson`.
  RPC references are serialized as `{"p": n}`. -/
  | v0
  /-- Version `1` is like `0`,
  except that RPC references are serialized as `{"__rpcref": n}`. -/
  | v1
  deriving FromJson, ToJson

@[inline]
def RpcWireFormat.refFieldName : RpcWireFormat → String
  | .v0 => "p"
  | .v1 => "__rpcref"

end Lean.Lsp

namespace Lean.Server

/--
`WithRpcRef α` marks values that RPC clients should see as opaque references.
This includes heavy objects such as `Lean.Environment`s
and non-serializable objects such as closures.

In the Lean server, `WithRpcRef α` is a structure containing a value of type `α`
and an associated `id`.
In an RPC client (e.g. the infoview), it is an opaque reference.
Thus, `WithRpcRef α` is cheap to transmit, but its data may only be accessed server-side.
In practice, this is used by client code to pass data
between various RPC methods provided by the server.

Two `WithRpcRef`s with the same `id` will yield the same client-side reference.

See also the docstring for `RpcEncodable`.
-/
structure WithRpcRef (α : Type u) where
  private mk' ::
    val : α
    private id : USize
  deriving Inhabited

builtin_initialize freshWithRpcRefId : IO.Ref USize ← IO.mkRef 1

/--
Creates an `WithRpcRef` instance with a unique `id`.
As long as the client holds at least one reference to this `WithRpcRef`,
serving it again will yield the same client-side reference.
Thus, when used as React deps,
client-side references can help preserve UI state across RPC requests.
-/
def WithRpcRef.mk (val : α) : BaseIO (WithRpcRef α) := do
  let id ← freshWithRpcRefId.modifyGet fun id => (id, id + 1)
  return { val, id }

structure ReferencedObject where
  obj : Dynamic
  id  : USize
  rc  : Nat

structure RpcObjectStore : Type where
  /--
  Objects that are being kept alive for the RPC client, together with their type names,
  mapped to by their RPC reference.
  -/
  aliveRefs : PersistentHashMap Lsp.RpcRef ReferencedObject := {}
  /--
  Unique `RpcRef` for the ID of an object that is being referenced through RPC.
  We store this mapping so that we can reuse `RpcRef`s for the same object.
  Reusing `RpcRef`s is helpful because it enables clients to reuse their UI state.
  -/
  refsById : PersistentHashMap USize Lsp.RpcRef := {}
  /--
  Value to use for the next fresh `RpcRef`, monotonically increasing.
  -/
  nextRef : USize := 0
  /-- The RPC wire format to follow. -/
  wireFormat : Lsp.RpcWireFormat := .v1

def rpcStoreRef [TypeName α] (obj : WithRpcRef α) : StateM RpcObjectStore Lsp.RpcRef := do
  let st ← get
  let reusableRef? : Option Lsp.RpcRef := st.refsById.find? obj.id
  match reusableRef? with
  | some ref =>
    -- Reuse `RpcRef` for this `obj` so that clients can reuse their UI state for it.
    -- We maintain a reference count so that we only free `obj` when the client has released
    -- all of its instances of the `RpcRef` for `obj`.
    let some referencedObj := st.aliveRefs.find? ref
      | return panic! "Found object ID in `refsById` but not in `aliveRefs`."
    let referencedObj := { referencedObj with rc := referencedObj.rc + 1 }
    set { st with aliveRefs := st.aliveRefs.insert ref referencedObj }
    return ref
  | none =>
    let ref : Lsp.RpcRef := ⟨st.nextRef⟩
    set { st with
      aliveRefs := st.aliveRefs.insert ref ⟨.mk obj.val, obj.id, 1⟩
      refsById := st.refsById.insert obj.id ref
      nextRef := st.nextRef + 1
    }
    return ref

def rpcGetRef (α) [TypeName α] (r : Lsp.RpcRef)
    : ReaderT RpcObjectStore (ExceptT String Id) (WithRpcRef α) := do
  let some referencedObj := (← read).aliveRefs.find? r
    | throw s!"RPC reference '{r}' is not valid"
  let some val := referencedObj.obj.get? α
    | throw <| s!"RPC call type mismatch in reference '{r}'\nexpected '{TypeName.typeName α}', " ++
        s!"got '{referencedObj.obj.typeName}'"
  return { val, id := referencedObj.id }

def rpcReleaseRef (r : Lsp.RpcRef) : StateM RpcObjectStore Bool := do
  let st ← get
  let some referencedObj := st.aliveRefs.find? r
    | return false
  let referencedObj := { referencedObj with rc := referencedObj.rc - 1 }
  if referencedObj.rc == 0 then
    set { st with
      aliveRefs := st.aliveRefs.erase r
      refsById := st.refsById.erase referencedObj.id
    }
  else
    set { st with aliveRefs := st.aliveRefs.insert r referencedObj }
  return true

/--
`RpcEncodable α` means `α` can be used as an argument or return value
in Remote Procedure Call (RPC) methods.

The following types are `RpcEncodable` by default:
- Any type with both `FromJson` and `ToJson` instances.
- Any type all of whose components
  (meaning the fields of a `structure`, or the arguments to `inductive` constructors)
  are `RpcEncodable`.
  Use `deriving RpcEncodable` to construct an instance in this case.
- Certain common containers, if containing `RpcEncodable` data (see instances below).
- Any `WithRpcRef α` where `[TypeName α]`.

Some names are reserved for internal use and must not appear
as the name of a field or constructor argument in any `RpcEncodable` type,
or as an object key in any nested JSON.
The following are currently reserved:
- `__rpcref`

It is also possible (but discouraged for non-experts)
to implement custom `RpcEncodable` instances.
These must respect the `RpcObjectStore.wireFormat`.
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

instance [RpcEncodable α] : RpcEncodable (StateM RpcObjectStore α) where
  rpcEncode fn := fn >>= rpcEncode
  rpcDecode j := do
    let a : α ← rpcDecode j
    return return a

instance [TypeName α] : RpcEncodable (WithRpcRef α) :=
  { rpcEncode, rpcDecode }
where
  -- separate definitions to prevent inlining
  rpcEncode r := do
    let ref ← rpcStoreRef r
    let fieldName := (← get).wireFormat.refFieldName
    return Json.mkObj [(fieldName, toJson ref.p)]
  rpcDecode j := do
    let fieldName := (← read).wireFormat.refFieldName
    let p ← j.getObjValAs? USize fieldName
    rpcGetRef α ⟨p⟩

end Lean.Server
