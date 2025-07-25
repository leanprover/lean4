/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Types

public section

namespace Lean.Meta.Grind.Arith

def mkLetOfMap {_ : Hashable α} {_ : BEq α} (m : Std.HashMap α Expr) (e : Expr)
    (varPrefix : Name) (varType : Expr) (toExpr : α → Expr) : GoalM Expr := do
  if m.isEmpty then
    return e
  else
    let as := m.toArray
    let mut e := e.abstract <| as.map (·.2)
    let mut i := as.size
    for (p, _) in as.reverse do
      e := mkLet (varPrefix.appendIndexAfter i) varType (toExpr p) e
      i := i - 1
    return e

def mkLambdaN (ns : Array Name) (xs : Array Expr) (xsTypes : Array Expr) (b : Expr) : Expr :=
  if _ : xs.size ≠ xsTypes.size ∨ xs.size ≠ ns.size then unreachable! else
  let b := b.abstract xs
  xs.size.foldRev (init := b) fun i _ b =>
    let n := ns[i]
    let x := xs[i]
    let xType := xsTypes[i]
    let xType := xType.abstractRange i xs
    mkLambda n .default xType b

end Lean.Meta.Grind.Arith
