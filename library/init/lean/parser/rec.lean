/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Recursion monad transformer
-/
prelude
import init.lean.parser.parsec init.lean.parser.syntax
import init.lean.parser.identifier init.data.rbmap init.lean.message

namespace lean.parser

/-- A small wrapper of `reader_t` that simplifies introducing and invoking
    recursion points in a computation. -/
def rec_t (α δ : Type) (m : Type → Type) (β : Type) :=
reader_t (α → m δ) m β

namespace rec_t
variables {m : Type → Type} {α δ β : Type} [monad m]
local attribute [reducible] rec_t

/-- Continue at the recursion point stored at `run`. -/
def recurse (a : α) : rec_t α δ m δ :=
do x ← read,
   monad_lift (x a)

variables (base : α → m δ) (rec : α → rec_t α δ m δ)
private def run_aux : nat → α → m δ
| 0     := base
| (n+1) := λ a, (rec a).run (run_aux n)

/-- Execute `rec a`, re-executing it whenever `recurse` (with a new `a`) is called.
    After `max_rec` recursion steps, `base` is executed instead. -/
protected def run (a : α) (max_rec := 1000) : m δ :=
(rec a).run (run_aux base rec max_rec)

-- not clear how to auto-derive these given the additional constraints
instance : monad (rec_t α δ m) := infer_instance
instance [alternative m] : alternative (rec_t α δ m) := infer_instance
instance : has_monad_lift m (rec_t α δ m) := infer_instance
instance (ε) [monad_except ε m] : monad_except ε (rec_t α δ m) := infer_instance
instance (μ) [monad_parsec μ m] : monad_parsec μ (rec_t α δ m) :=
infer_instance
end rec_t

class monad_rec (α δ : out_param Type) (m : Type → Type) :=
(recurse {} : α → m δ)
export monad_rec (recurse)

instance monad_rec.trans (α δ m m') [has_monad_lift m m'] [monad_rec α δ m] [monad m] : monad_rec α δ m' :=
{ recurse := λ a, monad_lift (recurse a : m δ) }

instance monad_rec.base (α δ m) [monad m] : monad_rec α δ (rec_t α δ m) :=
{ recurse := rec_t.recurse }

end lean.parser
