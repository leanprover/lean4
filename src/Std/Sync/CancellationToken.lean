/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data
public import Init.System.Promise
public import Init.Data.Queue
public import Std.Sync.Mutex
public import Std.Internal.Async.Select

public section

/-!
This module implements a hierarchical cancellation token system with bottom-up cancellation propagation and automatic cleanup.
-/

namespace Std

open Std.Internal.IO.Async

/--
A cancellation token provides a way to cancel operations and gracefully shutdown.
-/
@[expose]
def CancellationToken := IO.Promise Unit

namespace CancellationToken

/--
Creates a new cancellation token.
-/
def new : IO CancellationToken :=
  IO.Promise.new

/--
Cancels the token.
-/
def cancel (token : CancellationToken) : BaseIO Unit :=
  token.resolve ()

/--
Creates a selector that resolves when the token is cancelled.
-/
def selector (token : CancellationToken) : Selector Unit where
  tryFn := do
    if ← token.isResolved then
      return some ()
    else
      return none

  registerFn waiter := do
      IO.chainTask token.result? fun
      | some _ => waiter.promise.resolve (.ok ())
      | none => return ()

  unregisterFn := return ()

end CancellationToken

end Std
