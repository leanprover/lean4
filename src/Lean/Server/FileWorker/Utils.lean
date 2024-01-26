/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.Server.Utils
import Lean.Server.Snapshots
import Lean.Server.AsyncList
import Lean.Server.Rpc.Basic

namespace Lean.Server.FileWorker
open Snapshots
open IO

inductive ElabTaskError where
  | aborted
  | ioError (e : IO.Error)

instance : Coe IO.Error ElabTaskError :=
  ⟨ElabTaskError.ioError⟩

instance : MonadLift IO (EIO ElabTaskError) where
  monadLift act := act.toEIO (↑ ·)

structure CancelToken where
  ref : IO.Ref Bool

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

/-- A map from Diagnostics ID to resulting interactive objects. -/
abbrev DiagnosticsCache := RBMap Nat (Array Widget.InteractiveDiagnostic) compare

end Lean.Server.FileWorker
