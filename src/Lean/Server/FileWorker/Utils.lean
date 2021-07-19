/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.Server.Utils
import Lean.Server.Snapshots
import Lean.Server.AsyncList

namespace Lean.Server.FileWorker
open Snapshots
open IO

def logSnapContent (s : Snapshot) (text : FileMap) : IO Unit :=
  IO.eprintln s!"[{s.beginPos}, {s.endPos}]: ```\n{text.source.extract s.beginPos (s.endPos-1)}\n```"

inductive ElabTaskError where
  | aborted
  | eof
  | ioError (e : IO.Error)

instance : Coe IO.Error ElabTaskError := ⟨ElabTaskError.ioError⟩

structure CancelToken where
  ref : IO.Ref Bool
  deriving Inhabited

namespace CancelToken

def new : IO CancelToken :=
  CancelToken.mk <$> IO.mkRef false

def check [MonadExceptOf ElabTaskError m] [MonadLiftT (ST RealWorld) m] [Monad m] (tk : CancelToken) : m Unit := do
  let c ← tk.ref.get
  if c then
    throw ElabTaskError.aborted

def set (tk : CancelToken) : IO Unit :=
  tk.ref.set true

end CancelToken

/-- A document editable in the sense that we track the environment
and parser state after each command so that edits can be applied
without recompiling code appearing earlier in the file. -/
structure EditableDocument where
  meta       : DocumentMeta
  /- The first snapshot is that after the header. -/
  headerSnap : Snapshot
  /- Subsequent snapshots occur after each command. -/
  cmdSnaps   : AsyncList ElabTaskError Snapshot
  cancelTk   : CancelToken
  deriving Inhabited

structure RpcSession where
  sessionId : USize
  /-- Objects that are being kept alive for the RPC client, together with their type names,
  mapped to by their RPC reference.

  Note that we may currently have multiple references to the same object. It is only disposed
  of once all of those are gone. This simplifies the client a bit as it can drop every reference
  received separately. -/
  aliveRefs : IO.Ref (Std.PersistentHashMap Lsp.RpcRef (Name × UntypedRef))

end Lean.Server.FileWorker
