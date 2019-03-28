/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Recursion monad transformer
-/
prelude
import init.control.reader init.lean.parser.parsec init.fix

namespace Lean.Parser

/-- A small wrapper of `ReaderT` that simplifies introducing and invoking
    recursion points in a computation. -/
def RecT (α δ : Type) (m : Type → Type) (β : Type) :=
ReaderT (α → m δ) m β

namespace RecT
variables {m : Type → Type} {α δ β : Type} [Monad m]
local attribute [reducible] RecT

/-- Continue at the recursion point stored at `run`. -/
@[inline] def recurse (a : α) : RecT α δ m δ :=
λ f, f a

/-- Execute `x`, executing `rec a` whenever `recurse a` is called.
    After `maxRec` recursion steps, `base` is executed instead. -/
@[inline] protected def run (x : RecT α δ m β) (base : α → m δ) (rec : α → RecT α δ m δ) : m β :=
x (fixCore base (λ a f, rec f a))

@[inline] protected def runParsec {γ : Type} [MonadParsec γ m] (x : RecT α δ m β) (rec : α → RecT α δ m δ) : m β :=
RecT.run x (λ _, MonadParsec.error "RecT.runParsec: no progress") rec

-- not clear how to auto-derive these given the additional constraints
instance : Monad (RecT α δ m) := inferInstance
instance [Alternative m] : Alternative (RecT α δ m) := inferInstance
instance : HasMonadLift m (RecT α δ m) := inferInstance
instance (ε) [MonadExcept ε m] : MonadExcept ε (RecT α δ m) := inferInstance
instance (μ) [MonadParsec μ m] : MonadParsec μ (RecT α δ m) :=
inferInstance
-- NOTE: does not allow to vary `m` because of its occurrence in the Reader State
instance [Monad m] : MonadFunctor m m (RecT α δ m) (RecT α δ m) :=
inferInstance
end RecT

class MonadRec (α δ : outParam Type) (m : Type → Type) :=
(recurse {} : α → m δ)
export MonadRec (recurse)

instance MonadRec.trans (α δ m m') [HasMonadLift m m'] [MonadRec α δ m] [Monad m] : MonadRec α δ m' :=
{ recurse := λ a, monadLift (recurse a : m δ) }

instance MonadRec.base (α δ m) [Monad m] : MonadRec α δ (RecT α δ m) :=
{ recurse := RecT.recurse }

end Lean.Parser
