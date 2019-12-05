/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Data.LBool
import Init.Lean.Meta.InferType

namespace Lean
namespace Meta

partial def evalNat : Expr → Option Nat
| Expr.lit (Literal.natVal n) _ => pure n
| Expr.mdata _ e _              => evalNat e
| Expr.const `Nat.zero _ _      => pure 0
| e@(Expr.app _ a _)            =>
  let fn    := e.getAppFn;
  match fn with
  | Expr.const c _ _ =>
    let nargs := e.getAppNumArgs;
    if c == `Nat.succ && nargs == 1 then do
      v ← evalNat a; pure $ v+1
    else if c == `Nat.add && nargs == 2 then do
      v₁ ← evalNat (e.getArg! 0);
      v₂ ← evalNat (e.getArg! 1);
      pure $ v₁ + v₂
    else if c == `Nat.sub && nargs == 2 then do
      v₁ ← evalNat (e.getArg! 0);
      v₂ ← evalNat (e.getArg! 1);
      pure $ v₁ - v₂
    else if c == `Nat.mul && nargs == 2 then do
      v₁ ← evalNat (e.getArg! 0);
      v₂ ← evalNat (e.getArg! 1);
      pure $ v₁ * v₂
    else if c == `HasAdd.add && nargs == 4 then do
      v₁ ← evalNat (e.getArg! 2);
      v₂ ← evalNat (e.getArg! 3);
      pure $ v₁ + v₂
    else if c == `HasAdd.sub && nargs == 4 then do
      v₁ ← evalNat (e.getArg! 2);
      v₂ ← evalNat (e.getArg! 3);
      pure $ v₁ - v₂
    else if c == `HasAdd.mul && nargs == 4 then do
      v₁ ← evalNat (e.getArg! 2);
      v₂ ← evalNat (e.getArg! 3);
      pure $ v₁ * v₂
    else
      none
  | _ => none
| _ => none

/- Quick function for converting `e` into `s + k` s.t. `e` is definitionally equal to `Nat.add s k`. -/
private partial def getOffset : Expr → Expr × Nat
| e@(Expr.app _ a _) =>
  let fn := e.getAppFn;
  match fn with
  | Expr.const c _ _ =>
    let nargs := e.getAppNumArgs;
    if c == `Nat.succ && nargs == 1 then
      let (s, k) := getOffset a;
      (s, k+1)
    else if c == `Nat.add && nargs == 2 then
      match evalNat (e.getArg! 1) with
      | none   => (e, 0)
      | some v =>
        let (s, k) := getOffset (e.getArg! 0);
        (s, k+v)
    else if c == `HasAdd.add && nargs == 4 then
      match evalNat (e.getArg! 3) with
      | none   => (e, 0)
      | some v =>
        let (s, k) := getOffset (e.getArg! 0);
        (s, k+v)
    else
       (e, 0)
  | _ => (e, 0)
| e => (e, 0)

private partial def isOffset : Expr → Option (Expr × Nat)
| e@(Expr.app _ a _) =>
  let fn := e.getAppFn;
  match fn with
  | Expr.const c _ _ =>
    let nargs := e.getAppNumArgs;
    if (c == `Nat.succ && nargs == 1) || (c == `Nat.add && nargs == 2) || (c == `HasAdd.add && nargs == 4) then
      some (getOffset e)
    else none
  | _ => none
| _ => none

def isDefEqOffset (s t : Expr) : MetaM LBool :=
let isDefEq (s t) : MetaM LBool := toLBoolM $ isExprDefEqAux s t;
match isOffset s with
| some (s, k₁) => match isOffset t with
  | some (t, k₂) => -- s+k₁ =?= t+k₂
    if k₁ == k₂ then isDefEq s t
    else if k₁ < k₂ then isDefEq s (mkAppB (mkConst `Nat.add) t (mkNatLit $ k₂ - k₁))
    else isDefEq (mkAppB (mkConst `Nat.add) s (mkNatLit $ k₁ - k₂)) t
  | none => match evalNat t  with
    | some v₂ => -- s+k₁ =?= v₂
      if v₂ ≥ k₁ then isDefEq s (mkNatLit $ v₂ - k₁) else pure LBool.false
    | none    => pure LBool.undef
| none => match evalNat s with
  | some v₁ => match isOffset t with
    | some (t, k₂) => -- v₁ =?= t+k₂
      if v₁ ≥ k₂ then isDefEq s (mkNatLit $ v₁ - k₂) else pure LBool.false
    | none => match evalNat t with
      | some v₂ => pure (v₁ == v₂).toLBool -- v₁ =?= v₂
      | none    => pure LBool.undef
  | none    => pure LBool.undef

end Meta
end Lean
