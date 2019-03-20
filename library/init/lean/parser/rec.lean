/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Recursion monad transformer
-/
prelude
import init.lean.parser.parsec init.fix

namespace lean.parser

/-- A small wrapper of `readerT` that simplifies introducing and invoking
    recursion points in a computation. -/
def recT (α δ : Type) (m : Type → Type) (β : Type) :=
readerT (α → m δ) m β

namespace recT
variables {m : Type → Type} {α δ β : Type} [monad m]
local attribute [reducible] recT

/-- Continue at the recursion point stored at `run`. -/
@[inline] def recurse (a : α) : recT α δ m δ :=
λ f, f a

/-- Execute `x`, executing `rec a` whenever `recurse a` is called.
    After `maxRec` recursion steps, `base` is executed instead. -/
@[inline] protected def run (x : recT α δ m β) (base : α → m δ) (rec : α → recT α δ m δ) : m β :=
x (fixCore base (λ a f, rec f a))

@[inline] protected def runParsec {γ : Type} [monadParsec γ m] (x : recT α δ m β) (rec : α → recT α δ m δ) : m β :=
recT.run x (λ _, monadParsec.error "recT.runParsec: no progress") rec

-- not clear how to auto-derive these given the additional constraints
instance : monad (recT α δ m) := inferInstance
instance [alternative m] : alternative (recT α δ m) := inferInstance
instance : hasMonadLift m (recT α δ m) := inferInstance
instance (ε) [monadExcept ε m] : monadExcept ε (recT α δ m) := inferInstance
instance (μ) [monadParsec μ m] : monadParsec μ (recT α δ m) :=
inferInstance
-- NOTE: does not allow to vary `m` because of its occurrence in the reader state
instance [monad m] : monadFunctor m m (recT α δ m) (recT α δ m) :=
inferInstance
end recT

class monadRec (α δ : outParam Type) (m : Type → Type) :=
(recurse {} : α → m δ)
export monadRec (recurse)

instance monadRec.trans (α δ m m') [hasMonadLift m m'] [monadRec α δ m] [monad m] : monadRec α δ m' :=
{ recurse := λ a, monadLift (recurse a : m δ) }

instance monadRec.base (α δ m) [monad m] : monadRec α δ (recT α δ m) :=
{ recurse := recT.recurse }

end lean.parser
