/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import Init.System.IO
import Init.Control.StateRef

namespace Std

/--
`AtomicT α m` is the monad that can be atomically executed inside mutual exclusion primitives like
`Mutex α` with outside monad `m`.
The action has access to the state `α` of the mutex (via `get` and `set`).
-/
abbrev AtomicT := StateRefT' IO.RealWorld

end Std
