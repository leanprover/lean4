/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.ToString.Basic
universe u

namespace Lean

inductive LOption (α : Type u) where
  | none  : LOption α
  | some  : α → LOption α
  | undef : LOption α
  deriving Inhabited, BEq

instance [ToString α] : ToString (LOption α) where
  toString
    | .none   => "none"
    | .undef  => "undef"
    | .some a => "(some " ++ toString a ++ ")"

def LOption.toOption : LOption α → Option α
  | .some a => .some a
  | _ => .none

end Lean

def Option.toLOption {α : Type u} : Option α → Lean.LOption α
  | none   => .none
  | some a => .some a

@[inline] def toLOptionM {α} {m : Type → Type} [Monad m] (x : m (Option α)) : m (Lean.LOption α) := do
  let b ← x
  return b.toLOption
