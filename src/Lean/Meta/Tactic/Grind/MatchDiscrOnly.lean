/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Simp.Rewrite

namespace Lean.Meta.Grind
/--
Returns `Grind.simpMatchDiscrsOnly e`. Recall that `Grind.simpMatchDiscrsOnly` is
a gadget for instructing the `grind` simplifier to only normalize/simplify
the discriminants of a `match`-expression. See `reduceSimpMatchDiscrsOnly`.
-/
def markAsSimpMatchDiscrsOnly (e : Expr) : MetaM Expr :=
  mkAppM ``Grind.simpMatchDiscrsOnly #[e]

builtin_simproc_decl reduceSimpMatchDiscrsOnly (Grind.simpMatchDiscrsOnly _) := fun e => do
  let_expr Grind.simpMatchDiscrsOnly _ m ← e | return .continue
  let .const declName _ := m.getAppFn
    | return .done { expr := e }
  let some info ← getMatcherInfo? declName
    | return .done { expr := e }
  if let some r ← Simp.simpMatchDiscrs? info m then
    return .done { r with expr := (← markAsSimpMatchDiscrsOnly r.expr) }
  return .done { expr := e }

/-- Adds `reduceSimpMatchDiscrsOnly` to `s` -/
def addSimpMatchDiscrsOnly (s : Simprocs) : CoreM Simprocs := do
  s.add ``reduceSimpMatchDiscrsOnly (post := false)

/-- Erases `Grind.simpMatchDiscrsOnly` annotations. -/
def eraseSimpMatchDiscrsOnly (e : Expr) : CoreM Expr := do
  let pre (e : Expr) := do
    let_expr Grind.simpMatchDiscrsOnly _ a := e | return .continue e
    return .continue a
  Core.transform e (pre := pre)

end Lean.Meta.Grind
