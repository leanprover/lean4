/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Lsp.Extra

/-! Allows LSP clients to make Remote Procedure Calls to the server.

The single use case for these is to allow the infoview UI to refer to and manipulate heavy-weight
objects residing on the server. It would be inefficient to serialize these into JSON and send over.
For example, the client can format an `Expr` without transporting the whole `Environment`.

All RPC requests are relative to an open file and an RPC session for that file. The client must
first connect to the session using `$/lean/rpc/connect`. -/

namespace Lean.Server

/-- Monads with an RPC session in their state. -/
class MonadRpcSession (m : Type → Type) where
  rpcStoreRef (typeName : Name) (obj : NonScalar) : m Lsp.RpcRef
  rpcGetRef (r : Lsp.RpcRef) : m (Option (Name × NonScalar))
  rpcReleaseRef (r : Lsp.RpcRef) : m Bool
export MonadRpcSession (rpcStoreRef rpcGetRef rpcReleaseRef)

instance {m n : Type → Type} [MonadLift m n] [MonadRpcSession m] : MonadRpcSession n where
  rpcStoreRef typeName obj := liftM (rpcStoreRef typeName obj : m _)
  rpcGetRef r              := liftM (rpcGetRef r : m _)
  rpcReleaseRef r          := liftM (rpcReleaseRef r : m _)

/-- `RpcEncoding α β` means that `α` may participate in RPC calls with its on-the-wire LSP encoding
being `β`. This is useful when `α` contains fields which must be marshalled in a special way. In
particular, we encode `WithRpcRef` fields as opaque references rather than send their content.

Structures with `From/ToJson` use JSON as their `RpcEncoding`. Structures containing
non-JSON-serializable fields can be auto-encoded in two ways:
- `deriving RpcEncoding` acts like `From/ToJson` but marshalls any `WithRpcRef` fields
  as `Lsp.RpcRef`s.
- `deriving RpcEncoding with { withRef := true }` generates an encoding for
  `WithRpcRef TheType`. -/
-- TODO(WN): for Lean.js, have third parameter defining the client-side structure;
-- or, compile `WithRpcRef` to "opaque reference" on the client
class RpcEncoding (α : Type) (β : outParam Type) where
  rpcEncode {m : Type → Type} [Monad m] [MonadRpcSession m] : α → m β
  rpcDecode {m : Type → Type} [Monad m] [MonadRpcSession m] : β → ExceptT String m α
export RpcEncoding (rpcEncode rpcDecode)

instance [FromJson α] [ToJson α] : RpcEncoding α α where
  rpcEncode := pure
  rpcDecode := pure

instance [RpcEncoding α β] : RpcEncoding (Option α) (Option β) where
  rpcEncode v := match v with
    | none => none
    | some v => some <$> rpcEncode v
  rpcDecode v := match v with
    | none => none
    | some v => some <$> rpcDecode v

-- TODO(WN): instance [RpcEncoding α β] [Traversable t] : RpcEncoding (t α) (t β)
instance [RpcEncoding α β] : RpcEncoding (Array α) (Array β) where
  rpcEncode a := a.mapM rpcEncode
  rpcDecode b := b.mapM rpcDecode

instance [RpcEncoding α α'] [RpcEncoding β β'] : RpcEncoding (α × β) (α' × β') where
  rpcEncode := fun (a, b) => do
    let a' ← rpcEncode a
    let b' ← rpcEncode b
    return (a', b')
  rpcDecode := fun (a', b') => do
    let a ← rpcDecode a'
    let b ← rpcDecode b'
    return (a, b)

structure RpcEncoding.DerivingParams where
  withRef : Bool := false

/-- Marks fields to encode as opaque references in LSP packets. -/
structure WithRpcRef (α : Type u) where
  val : α
  deriving Inhabited

namespace WithRpcRef

variable {m : Type → Type} [Monad m] [MonadRpcSession m]

/-- This is unsafe because we must ensure that:
- the stored `NonScalar` is never used to access the value as a type other than `α`
- the type `α` is not a scalar -/
protected unsafe def encodeUnsafe [Monad m] (typeName : Name) (r : WithRpcRef α) : m Lsp.RpcRef := do
  let obj := @unsafeCast α NonScalar r.val
  rpcStoreRef typeName obj

protected unsafe def decodeUnsafeAs (α) (typeName : Name) (r : Lsp.RpcRef) : ExceptT String m (WithRpcRef α) := do
  match (← rpcGetRef r) with
    | none => throw s!"RPC reference '{r}' is not valid"
    | some (nm, obj) =>
      if nm != typeName then
        throw s!"RPC call type mismatch in reference '{r}'\nexpected '{typeName}', got '{nm}'"
      WithRpcRef.mk <| @unsafeCast NonScalar α obj

end WithRpcRef
end Lean.Server
