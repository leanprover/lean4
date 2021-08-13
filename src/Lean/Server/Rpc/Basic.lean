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
  rpcSessionId : m UInt64
  rpcStoreRef (typeName : Name) (obj : NonScalar) : m Lsp.RpcRef
  rpcGetRef (r : Lsp.RpcRef) : m (Option (Name × NonScalar))
  rpcReleaseRef (r : Lsp.RpcRef) : m Bool
export MonadRpcSession (rpcSessionId rpcStoreRef rpcGetRef rpcReleaseRef)

instance {m n : Type → Type} [MonadLift m n] [MonadRpcSession m] : MonadRpcSession n where
  rpcSessionId             := liftM (rpcSessionId : m _)
  rpcStoreRef typeName obj := liftM (rpcStoreRef typeName obj : m _)
  rpcGetRef r              := liftM (rpcGetRef r : m _)
  rpcReleaseRef r          := liftM (rpcReleaseRef r : m _)

/-- Concurrently modifiable part of an RPC session. -/
structure RpcSessionState where
  /-- Objects that are being kept alive for the RPC client, together with their type names,
  mapped to by their RPC reference.

  Note that we may currently have multiple references to the same object. It is only disposed
  of once all of those are gone. This simplifies the client a bit as it can drop every reference
  received separately. -/
  aliveRefs : Std.PersistentHashMap Lsp.RpcRef (Name × NonScalar)
  /-- Value to use for the next `RpcRef`. It is monotonically increasing to avoid any possible
  bugs resulting from its reuse. -/
  nextRef   : USize

namespace RpcSessionState

def store (st : RpcSessionState) (typeName : Name) (obj : NonScalar) : Lsp.RpcRef × RpcSessionState :=
  let ref := ⟨st.nextRef⟩
  let st' := { st with aliveRefs := st.aliveRefs.insert ref (typeName, obj)
                       nextRef := st.nextRef + 1 }
  (ref, st')

def release (st : RpcSessionState) (ref : Lsp.RpcRef) : Bool × RpcSessionState :=
  let released := st.aliveRefs.contains ref
  (released, { st with aliveRefs := st.aliveRefs.erase ref })

end RpcSessionState

structure RpcSession where
  sessionId       : UInt64
  clientConnected : Bool
  /-- The `IO.monoMsNow` time when the session expires. See `$/lean/rpc/keepAlive`.
  Note we only *actually* reset the connection if `clientConnected` is set. -/
  expireTime      : Nat
  /-- We allow asynchronous elab tasks and request handlers to modify parts of the state.
  A single `Ref` ensures atomic transactions. -/
  state           : IO.Ref RpcSessionState

namespace RpcSession

def keepAliveTimeMs : Nat :=
  30000

def new (clientConnected := false) : IO RpcSession := do
  /- We generate a random ID to ensure that session IDs do not repeat across re-initializations
  and worker restarts. Otherwise, the client may attempt to use outdated references. -/
  let newId ← ByteArray.toUInt64LE! <$> IO.getRandomBytes 8
  let newState ← IO.mkRef {
    aliveRefs := Std.PersistentHashMap.empty
    nextRef := 0
  }
  return {
    sessionId := newId
    expireTime := (← IO.monoMsNow) + keepAliveTimeMs
    clientConnected
    state := newState
  }

def keptAlive (s : RpcSession) : IO RpcSession := do
  return { s with expireTime := (← IO.monoMsNow) + keepAliveTimeMs }

def hasExpired (s : RpcSession) : IO Bool :=
  return s.clientConnected ∧ s.expireTime ≤ (← IO.monoMsNow)

end RpcSession

instance [Monad m] [MonadLiftT IO m] [MonadReaderOf RpcSession m] : MonadRpcSession m where
  rpcSessionId := do
    (←read).sessionId
  rpcStoreRef typeName obj := do
    liftM (m := IO) <| (←read).state.modifyGet fun st => st.store typeName obj
  rpcGetRef r := do
    let rs ← liftM (m := IO) <| (←read).state.get
    rs.aliveRefs.find? r
  rpcReleaseRef r := do
    liftM (m := IO) <| (←read).state.modifyGet fun st => st.release r

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
  -- TODO(WN): ExceptT String or RpcError where | InvalidSession | InvalidParams (msg : String) | ..
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
