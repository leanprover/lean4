/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.LinearArith.Solver
import Lean.Meta.Tactic.LinearArith.Nat.Basic

namespace Lean.Meta.Linear.Nat

namespace Collect

inductive LinearArith

structure Cnstr where
  cnstr : LinearArith
  proof : Expr

structure State where
  cnstrs : Array Cnstr

abbrev M := StateRefT State ToLinear.M

-- TODO

end Collect

end Lean.Meta.Linear.Nat
