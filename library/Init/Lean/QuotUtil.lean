/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean

/-- Auxiliary function for reducing `Quot.lift` and `Quot.ind` applications. -/
@[specialize] def reduceQuotRecAux {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (env : Environment)
    (rec : QuotVal) (recLvls : List Level) (recArgs : Array Expr) : m (Option Expr) :=
let process (majorPos argPos : Nat) : m (Option Expr) :=
  if h : majorPos < recArgs.size then do
    let major := recArgs.get ⟨majorPos, h⟩;
    major ← whnf major;
    match major with
    | Expr.app (Expr.app (Expr.app (Expr.const majorFn _) _) _) majorArg =>
      match env.find majorFn with
      | some (ConstantInfo.quotInfo { kind := QuotKind.ctor, .. }) =>
        let f := recArgs.get! argPos;
        let r := Expr.app f majorArg;
        let recArity := majorPos + 1;
        pure $ mkAppRange r recArity recArgs.size recArgs
      | _ => pure none
    | _ => pure none
  else
    pure none;
match rec.kind with
| QuotKind.lift => process 5 3
| QuotKind.ind  => process 4 3
| _             => pure none

end Lean
