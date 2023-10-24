/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

namespace Lake

/-- A sequence of calls donated by the key type `κ`. -/
abbrev CallStack κ := List κ

/-- A `CallStack` ending in a cycle. -/
abbrev Cycle κ := CallStack κ

/-- A transformer that equips a monad with a `CallStack` to detect cycles. -/
abbrev CycleT κ m := ReaderT (CallStack κ) <| ExceptT (Cycle κ) m

/-- Read the call stack from a CycleT.
  this specialized version exists to be used in e.g. `BuildM`. -/
def CycleT.readCallStack [Pure m] : CycleT κ m (CallStack κ) :=
  fun callStack => ExceptT.mk <| pure (Except.ok callStack)

/--
Add `key` to the monad's `CallStack` before invoking `act`.
If adding `key` produces a cycle, the cyclic call stack is thrown.
-/
@[inline] def guardCycle [BEq κ] [Monad m]
(key : κ) (act : CycleT κ m α) : CycleT κ m α := do
  let parents ← read
  if parents.contains key then
    throw <| key :: (parents.partition (· != key)).1 ++ [key]
  else
    act (key :: parents)
