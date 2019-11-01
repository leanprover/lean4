/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Environment

namespace Lean

/-- Auxiliary function for reducing `Quot.lift` and `Quot.ind` applications. -/
@[specialize] def reduceQuotRecAux {α} {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (env : Environment)
    (rec : QuotVal) (recLvls : List Level) (recArgs : Array Expr)
    (failK : Unit → m α)
    (successK : Expr → m α) : m α :=
let process (majorPos argPos : Nat) : m α :=
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
        successK $ mkAppRange r recArity recArgs.size recArgs
      | _ => failK ()
    | _ => failK ()
  else
    failK ();
match rec.kind with
| QuotKind.lift => process 5 3
| QuotKind.ind  => process 4 3
| _             => failK ()

@[inline] private def matchQuotRecApp {α} {m : Type → Type} [Monad m] (env : Environment)
   (e : Expr) (failK : Unit → m α) (k : QuotVal → List Level → Array Expr → m α) : m α :=
matchConst env e.getAppFn failK $ fun cinfo recLvls =>
  match cinfo with
  | ConstantInfo.quotInfo rec => k rec recLvls e.getAppArgs
  | _ => failK ()

@[specialize] def reduceQuotRec {α} {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (env : Environment) (e : Expr)
    (failK : Unit → m α)
    (successK : Expr → m α) : m α :=
matchQuotRecApp env e failK $ fun rec recLvls recArg => reduceQuotRecAux whnf env rec recLvls recArg failK successK

@[specialize] def isQuotRecStuck {m : Type → Type} [Monad m]
    (whnf : Expr → m Expr)
    (isStuck : Expr → m (Option Expr))
    (env : Environment) (e : Expr) : m (Option Expr) :=
matchQuotRecApp env e (fun _ => pure none) $ fun rec recLvls recArgs =>
  let process (majorPos : Nat) : m (Option Expr) :=
    if h : majorPos < recArgs.size then do
      let major := recArgs.get ⟨majorPos, h⟩;
      major ← whnf major;
      isStuck major
    else
      pure none;
  match rec.kind with
  | QuotKind.lift => process 5
  | QuotKind.ind  => process 4
  | _             => pure none

end Lean
