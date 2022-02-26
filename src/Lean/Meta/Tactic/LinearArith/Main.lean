/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.LinearArith.Nat

namespace Lean.Meta.Linear

def simpCnstr? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  -- TODO: add support for `Int` and arbitrary ordered comm rings
  Nat.simpCnstr? e

end Lean.Meta.Linear
