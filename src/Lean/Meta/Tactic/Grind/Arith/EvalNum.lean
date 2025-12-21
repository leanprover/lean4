/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.IntInstTesters
import Lean.Meta.NatInstTesters
public section

namespace Lean.Meta.Grind.Arith

/-!
This module provides functions for evaluating simple `Nat` and `Int` expressions that appear in type classes
(e.g., `ToInt` and `IsCharP`) used to configure `grind`.
Using `whnf` for this purpose is too expensive and can exhaust the stack.
We considered `evalExpr` as an alternative, but it introduces considerable overhead in files with
 many `grind` calls. We may still use `evalExpr` as a fallback in the future.
-/

def checkExp (k : Nat) : OptionT GrindM Unit := do
  if k > (← getConfig).exp then
    reportIssue! "exponent {k} exceeds threshold for exponentiation `(exp := {(← getConfig).exp})`"
    failure

/-
**Note**: It is safe to use (the more efficient) structural instances tests here because `grind` uses the canonicalizer.
-/
open Structural in
mutual
private partial def evalNatCore (e : Expr) : OptionT GrindM Nat := do
  match_expr e with
  | Nat.zero => return 0
  | Nat.succ a => return (← evalNatCore a) + 1
  | Int.toNat a => return (← evalIntCore a).toNat
  | Int.natAbs a => return (← evalIntCore a).natAbs
  | HAdd.hAdd _ _ _ inst a b => guard (← isInstHAddNat inst); return (← evalNatCore a) + (← evalNatCore b)
  | HMul.hMul _ _ _ inst a b => guard (← isInstHMulNat inst); return (← evalNatCore a) * (← evalNatCore b)
  | HSub.hSub _ _ _ inst a b => guard (← isInstHSubNat inst); return (← evalNatCore a) - (← evalNatCore b)
  | HDiv.hDiv _ _ _ inst a b => guard (← isInstHDivNat inst); return (← evalNatCore a) / (← evalNatCore b)
  | HMod.hMod _ _ _ inst a b => guard (← isInstHModNat inst); return (← evalNatCore a) % (← evalNatCore b)
  | OfNat.ofNat _ _ _ =>
    let some n ← getNatValue? e | failure
    return n
  | HPow.hPow _ _ _ inst a k =>
    guard (← isInstHPowNat inst)
    let k ← evalNatCore k
    checkExp k
    let a ← evalNatCore a
    return a ^ k
  /-
  Remark: possible improvements
  - Expand constants
  - `whnfCore`
  - `evalExpr` as an expensive fallback.
  -/
  | _ => failure

private partial def evalIntCore (e : Expr) : OptionT GrindM Int := do
  match_expr e with
  | Neg.neg _ i a => guard (← isInstNegInt i); return - (← evalIntCore a)
  | HAdd.hAdd _ _ _ i a b => guard (← isInstHAddInt i); return (← evalIntCore a) + (← evalIntCore b)
  | HSub.hSub _ _ _ i a b => guard (← isInstHSubInt i); return (← evalIntCore a) - (← evalIntCore b)
  | HMul.hMul _ _ _ i a b => guard (← isInstHMulInt i); return (← evalIntCore a) * (← evalIntCore b)
  | HDiv.hDiv _ _ _ i a b => guard (← isInstHDivInt i); return (← evalIntCore a) / (← evalIntCore b)
  | HMod.hMod _ _ _ i a b => guard (← isInstHModInt i); return (← evalIntCore a) % (← evalIntCore b)
  | HPow.hPow _ _ _ i a k =>
    guard (← isInstHPowInt i)
    let a ← evalIntCore a
    let k ← evalNatCore k
    checkExp k
    return a ^ k
  | OfNat.ofNat _ _ _ =>
    let some n ← getIntValue? e | failure
    return n
  | NatCast.natCast _ i a =>
    let_expr instNatCastInt ← i | failure
    return (← evalNatCore a)
  | Nat.cast _ i a =>
    let_expr instNatCastInt ← i | failure
    return (← evalNatCore a)
  /- See comment at `evalNatCore` -/
  | _ => failure

end

def evalNat? (e : Expr) : GrindM (Option Nat) :=
  evalNatCore e |>.run

def evalInt? (e : Expr) : GrindM (Option Int) :=
  evalIntCore e |>.run

end Lean.Meta.Grind.Arith
