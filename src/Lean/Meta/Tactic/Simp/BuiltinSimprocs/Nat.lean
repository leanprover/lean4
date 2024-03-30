/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Simproc
import Init.Data.Nat.Simproc
import Lean.Meta.LitValues
import Lean.Meta.Offset
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util

namespace Nat
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option Nat) :=
  getNatValue? e

@[inline] def reduceUnary (declName : Name) (arity : Nat) (op : Nat → Nat) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Nat → Nat → Nat) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

builtin_dsimproc [simp, seval] reduceSucc (Nat.succ _) := reduceUnary ``Nat.succ 1 (· + 1)

/-
The following code assumes users did not override the `Nat` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_dsimproc [simp, seval] reduceAdd ((_ + _ : Nat)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_dsimproc [simp, seval] reduceMul ((_ * _ : Nat)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_dsimproc [simp, seval] reduceSub ((_ - _ : Nat)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_dsimproc [simp, seval] reduceDiv ((_ / _ : Nat)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_dsimproc [simp, seval] reduceMod ((_ % _ : Nat)) := reduceBin ``HMod.hMod 6 (· % ·)
builtin_dsimproc [simp, seval] reducePow ((_ ^ _ : Nat)) := reduceBin ``HPow.hPow 6 (· ^ ·)
builtin_dsimproc [simp, seval] reduceGcd (gcd _ _)       := reduceBin ``gcd 2 gcd

builtin_simproc [simp, seval] reduceLT  (( _ : Nat) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Nat) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Nat) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Nat) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : Nat) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : Nat) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] reduceBEq  (( _ : Nat) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] reduceBNe  (( _ : Nat) != _)  := reduceBoolPred ``bne 4 (. != .)

/-- Return `.done` for Nat values. We don't want to unfold in the symbolic evaluator. -/
builtin_dsimproc [seval] isValue ((OfNat.ofNat _ : Nat)) := fun e => do
  let_expr OfNat.ofNat _ _ _ ← e | return .continue
  return .done e

/-- A literal natural number or a base + offset expression. -/
private inductive NatOffset where
  /- denotes expression definition equal to `n` -/
  | const (n : Nat)
  /-- denotes `e + o` where `o` is expression definitionally equal to `n` -/
  | offset (e o : Expr) (n : Nat)

/- Attempt to parse a `NatOffset` from an expression-/
private def NatOffset.fromExpr? (e : Expr) : Meta.SimpM (Option NatOffset) := do
  match ← Nat.fromExpr? e with
  | some n => pure (some (.const n))
  | none =>
    unless e.isAppOfArity ``HAdd.hAdd 6 do return none
    let inst := e.appFn!.appFn!.appArg!
    unless inst.isAppOfArity ``instHAdd 2 do return none
    unless inst.appArg!.isAppOfArity ``instAddNat 0 do return none
    let b := e.appFn!.appArg!
    let o := e.appArg!
    let some n ← Nat.fromExpr? o | return none
    pure (some (.offset b o n))

private def mkAddNat (x y : Expr) : Expr :=
  let lz := levelZero
  let nat := mkConst ``Nat
  let instHAdd := mkAppN (mkConst ``instHAdd [lz]) #[nat, mkConst ``instAddNat]
  mkAppN (mkConst ``HAdd.hAdd [lz, lz, lz]) #[nat, nat, nat, instHAdd, x, y]

private def mkSubNat (x y : Expr) : Expr :=
  let lz := levelZero
  let nat := mkConst ``Nat
  let instSub := mkConst ``instSubNat
  let instHSub := mkAppN (mkConst ``instHSub [lz]) #[nat, instSub]
  mkAppN (mkConst ``HSub.hSub [lz, lz, lz]) #[nat, nat, nat, instHSub, x, y]

private def mkEqNat (x y : Expr) : Expr :=
  mkAppN (mkConst ``Eq [levelOne]) #[mkConst ``Nat, x, y]

private def mkLENat (x y : Expr) : Expr :=
  mkAppN (.const ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat, x, y]

private def mkGENat (x y : Expr) : Expr := mkLENat y x

private def mkLTNat (x y : Expr) : Expr :=
  mkAppN (.const ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat, x, y]

private def mkGTNat (x y : Expr) : Expr := mkLTNat y x

private def mkOfDecideEqTrue (p : Expr) : MetaM Expr := do
  let d ← Meta.mkDecide p
  pure <| mkAppN (mkConst ``of_decide_eq_true) #[p, d.appArg!, (← Meta.mkEqRefl (mkConst ``true))]

builtin_simproc [simp, seval] reduceEqDiff ((_ : Nat) = _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do
    return .continue
  let x := e.appFn!.appArg!
  let some xno ← NatOffset.fromExpr? x | return .continue
  let y := e.appArg!
  let some yno ← NatOffset.fromExpr? y | return .continue
  match xno, yno with
  | .const xn, .const yn =>
    Meta.Simp.evalPropStep e (xn = yn)
  | .offset xb xo xn, .const yn => do
    if xn ≤ yn then
      unless (← getEnv).contains ``Nat.Simproc.add_eq_le do return .continue
      let leProp := mkLENat xo y
      let leProof ← mkOfDecideEqTrue leProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.add_eq_le) #[xb, xo, y, leProof]
      let finExpr := mkEqNat xb (toExpr (yn - xn))
      return .visit { expr := finExpr, proof? := finProof, cache := true }
    else
      unless (← getEnv).contains ``Nat.Simproc.add_eq_gt do return .continue
      let gtProp := mkGTNat xo y
      let gtProof ← mkOfDecideEqTrue gtProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.add_eq_gt) #[xb, xo, y, gtProof]
      let finExpr := mkConst ``False
      return .visit { expr := finExpr, proof? := finProof, cache := true }
  | .const xn, .offset yb yo yn => do
    if yn ≤ xn then
      unless (← getEnv).contains ``Nat.Simproc.eq_add_le do return .continue
      let leProp := mkLENat yo x
      let leProof ← mkOfDecideEqTrue leProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.eq_add_le) #[x, yb, yo, leProof]
      let finExpr := mkEqNat yb (toExpr (xn - yn))
      return .visit { expr := finExpr, proof? := finProof, cache := true }
    else
      unless (← getEnv).contains ``Nat.Simproc.eq_add_gt do return .continue
      let gtProp := mkGTNat yo x
      let gtProof ← mkOfDecideEqTrue gtProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.eq_add_gt) #[x, yb, yo, gtProof]
      let finExpr := mkConst ``False
      return .visit { expr := finExpr, proof? := finProof, cache := true }
  | .offset xb xo xn, .offset yb yo yn => do
    if xn ≤ yn then
      unless (← getEnv).contains ``Nat.Simproc.add_eq_add_le do return .continue
      let leProp := mkLENat xo yo
      let leProof ← mkOfDecideEqTrue leProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.add_eq_add_le) #[xb, yb, xo, yo, leProof]
      let finExpr := mkEqNat xb (if xn = yn then yb else mkAddNat yb (toExpr (yn - xn)))
      return .visit { expr := finExpr, proof? := finProof, cache := true }
    else
      unless (← getEnv).contains ``Nat.Simproc.add_eq_add_ge do return .continue
      let geProp := mkGENat xo yo
      let geProof ← mkOfDecideEqTrue geProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.add_eq_add_ge) #[xb, yb, xo, yo, geProof]
      let finExpr := mkEqNat (mkAddNat xb (toExpr (xn - yn))) yb
      return .visit { expr := finExpr, proof? := finProof, cache := true }

builtin_simproc [simp, seval] reduceSubDiff ((_ - _ : Nat)) := fun e => do
  unless e.isAppOfArity ``HSub.hSub 6 do
    return .continue
  let p := e.appFn!.appArg!
  let some pno ← NatOffset.fromExpr? p | return .continue
  let q := e.appArg!
  let some qno ← NatOffset.fromExpr? q | return .continue
  match pno, qno with
  | .const pn, .const qn =>
    -- Generate rfl proof  showing (p - q) = pn - qn
    let finExpr := toExpr (pn - qn)
    let finProof ← Meta.mkEqRefl finExpr
    return .done  { expr := finExpr, proof? := finProof, cache := true }
  | .offset pb po pn, .const n => do
    if pn ≤ n then
      let leProp := mkLENat po q
      let leProof ← mkOfDecideEqTrue leProp
      unless (← getEnv).contains ``Nat.Simproc.add_sub_le do return .continue
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.add_sub_le) #[pb, po, q, leProof]
      let finExpr := if pn = n then pb else mkSubNat pb (toExpr (n - pn))
      return .visit { expr := finExpr, proof? := finProof, cache := true }
    else
      let geProp := mkGENat po q
      let geProof ← mkOfDecideEqTrue geProp
      unless (← getEnv).contains ``Nat.add_sub_assoc do return .continue
      let finProof : Expr := mkAppN (mkConst ``Nat.add_sub_assoc) #[po, q, geProof, pb]
      let finExpr := mkAddNat pb (toExpr (pn - n))
      return .visit { expr := finExpr, proof? := finProof, cache := true }
  | .const po, .offset nb no nn => do
      unless (← getEnv).contains ``Nat.Simproc.sub_add_eq_comm do return .continue
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.sub_add_eq_comm) #[p, nb, no]
      let finExpr := mkSubNat (toExpr (po - nn)) nb
      return .visit { expr := finExpr, proof? := finProof, cache := true }
  | .offset pb po pn, .offset nb no nn => do
    if pn ≤ nn then
      unless (← getEnv).contains ``Nat.Simproc.add_sub_add_le do return .continue
      let leProp := mkLENat po no
      let leProof ← mkOfDecideEqTrue leProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.add_sub_add_le) #[pb, nb, po, no, leProof]
      let finExpr := mkSubNat pb (if pn = nn then nb else mkAddNat nb (toExpr (nn - pn)))
      return .visit { expr := finExpr, proof? := finProof, cache := true }
    else
      unless (← getEnv).contains ``Nat.Simproc.add_sub_add_ge do return .continue
      let geProp := mkGENat po no
      let geProof ← mkOfDecideEqTrue geProp
      let finProof : Expr := mkAppN (mkConst ``Nat.Simproc.add_sub_add_ge) #[pb, nb, po, no, geProof]
      let finExpr := mkSubNat (mkAddNat pb (toExpr (pn - nn))) nb
      return .visit { expr := finExpr, proof? := finProof, cache := true }

end Nat
