/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr

namespace Lean

abbrev Perm := Std.HashMap Nat Nat

/--
Sorts the given expressions using `Expr.lt`, and creates a "permutation map" storing the new position of each expression.
-/
def sortExprs (es : Array Expr) : Array Expr × Perm :=
  let es := es.mapIdx fun i e => (e, i)
  let es := es.qsort fun (e₁, _) (e₂, _) => e₁.lt e₂
  let (_, perm) := es.foldl (init := (0, Std.HashMap.empty)) fun (i, perm) (_, j) => (i+1, perm.insert j i)
  let es := es.map (·.1)
  (es, perm)

end Lean
