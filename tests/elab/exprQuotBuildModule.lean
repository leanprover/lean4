/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Reser
-/
module

public import Lean

/-!
# Module-System Compatibility Tests for Term-Position `` `(expr[rel]| t) `` Building

Verifies that auxiliary `ExprTemplate` constants (`exprTmplExt`) and closed `ResolvedExprMatchRel`
hoisting compile cleanly in `module` files across `public` / `meta` sections.
-/

namespace ExprQuotBuildModuleTest

open Lean Meta

public meta def buildDoubleAdd (x : Expr) : MetaM Expr :=
  `(expr| Nat.add $x $x)

public meta def buildWithLocalAlias (x : Expr) : MetaM Expr := do
  `(expr| $x == $x)

public meta def buildWithHole (n : Expr) : MetaM Expr :=
  `(expr| @Eq.refl Nat $n)

#guard_msgs in
#eval show MetaM Unit from do
  let n := mkNatLit 5
  let e1 ← buildDoubleAdd n
  unless e1 == mkApp2 (mkConst ``Nat.add) n n do
    throwError "unexpected module buildDoubleAdd result: {e1}"
  let e2 ← buildWithLocalAlias n
  Meta.check e2
  let e3 ← buildWithHole n
  Meta.check e3

end ExprQuotBuildModuleTest
