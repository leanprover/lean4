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

/-- A monad equipped with a call stack and the ability to error on a cycle. -/
class MonadCycleOf (κ :  semiOutParam (Type u)) (m : Type u → Type v) where
  getCallStack : m (CallStack κ)
  withCallStack (stack : CallStack κ) (x : m α) : m α
  throwCycle (cycle : Cycle κ) : m α

/-- Similar to `MonadCycle`, but `κ` is an `outParam` for convenience. -/
class MonadCycle (κ :  outParam (Type u)) (m : Type u → Type v) where
  getCallStack : m (CallStack κ)
  withCallStack (stack : CallStack κ) (x : m α) : m α
  throwCycle (cycle : Cycle κ) : m α

instance [MonadCycleOf κ m] : MonadCycle κ m where
  getCallStack := MonadCycleOf.getCallStack
  withCallStack := MonadCycleOf.withCallStack
  throwCycle := MonadCycleOf.throwCycle

export MonadCycle (getCallStack withCallStack throwCycle)

instance [MonadLift m n] [MonadFunctor m n] [MonadCycleOf κ m] : MonadCycleOf κ n where
  getCallStack := liftM (m := m) getCallStack
  withCallStack s := monadMap (m := m) (withCallStack s ·)
  throwCycle cycle := liftM (m := m) (throwCycle cycle)

instance inhabitedOfMonadCycle [MonadCycle κ m] : Inhabited (m α) := ⟨throwCycle []⟩

/-- A transformer that equips a monad with a `CallStack`. -/
abbrev CallStackT κ m := ReaderT (CallStack κ) m

/-- A transformer that equips a monad with a `CallStack` to detect cycles. -/
abbrev CycleT κ m := CallStackT κ <| ExceptT (Cycle κ) m

instance [Monad m] : MonadCycleOf κ (CycleT κ m) where
  getCallStack := read
  withCallStack s x := x s
  throwCycle := throw

/--
Add `key` to the monad's `CallStack` before invoking `act`.
If adding `key` produces a cycle, the cyclic call stack is thrown.
-/
@[inline] def guardCycle
  [BEq κ] [Monad m] [MonadCycle κ m] (key : κ) (act : m α)
: m α := do
  let parents ← getCallStack
  if parents.contains key then
    throwCycle <| key :: (parents.partition (· != key)).1 ++ [key]
  else
    withCallStack (key :: parents) act
