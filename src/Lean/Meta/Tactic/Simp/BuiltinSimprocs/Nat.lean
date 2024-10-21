/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Simproc
import Init.Data.Nat.Simproc
import Lean.Util.SafeExponentiation
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

builtin_dsimproc [simp, seval] reducePow ((_ ^ _ : Nat)) := fun e => do
  let_expr HPow.hPow _ _ _ _ n m := e | return .continue
  let some n ← fromExpr? n | return .continue
  let some m ← fromExpr? m | return .continue
  unless (← checkExponent m) do return .continue
  return .done <| toExpr (n ^ m)

builtin_dsimproc [simp, seval] reduceAnd ((_ &&& _ : Nat)) := reduceBin ``HOr.hOr 6 (· &&& ·)
builtin_dsimproc [simp, seval] reduceXor ((_ ^^^ _ : Nat)) := reduceBin ``HXor.hXor 6 (· ^^^ ·)
builtin_dsimproc [simp, seval] reduceOr ((_ ||| _ : Nat)) := reduceBin ``HOr.hOr 6 (· ||| ·)

builtin_dsimproc [simp, seval] reduceShiftLeft ((_ <<< _ : Nat)) :=
  reduceBin ``HShiftLeft.hShiftLeft 6 (· <<< ·)

builtin_dsimproc [simp, seval] reduceShiftRight ((_ >>> _ : Nat)) :=
  reduceBin ``HShiftRight.hShiftRight 6 (· >>> ·)

builtin_dsimproc [simp, seval] reduceGcd (gcd _ _)       := reduceBin ``gcd 2 gcd

builtin_simproc [simp, seval] reduceLT  (( _ : Nat) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceGT  (( _ : Nat) > _)  := reduceBinPred ``GT.gt 4 (. > .)
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
private partial def NatOffset.asOffset (e : Expr) : Meta.SimpM (Option (Expr × Nat)) := do
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let inst := e.appFn!.appFn!.appArg!
    unless ← matchesInstance inst Nat.mkInstHAdd do return none
    let b := e.appFn!.appArg!
    let o := e.appArg!
    let some n ← Nat.fromExpr? o | return none
    pure (some (b, n))
  else if e.isAppOfArity ``Add.add 4 then
    let inst := e.appFn!.appFn!.appArg!
    unless ← matchesInstance inst Nat.mkInstAdd do return none
    let b := e.appFn!.appArg!
    let some n ← Nat.fromExpr? e.appArg! | return none
    pure (some (b, n))
  else if e.isAppOfArity ``Nat.add 2 then
    let b := e.appFn!.appArg!
    let some n ← Nat.fromExpr? e.appArg! | return none
    pure (some (b, n))
  else if e.isAppOfArity ``Nat.succ 1 then
    let b := e.appArg!
    pure (some (b, 1))
  else
    pure none

/- Attempt to parse a `NatOffset` from an expression-/
private partial def NatOffset.fromExprAux (e : Expr) (inc : Nat) : Meta.SimpM (Option (Expr × Nat)) := do
  let e := e.consumeMData
  match ← asOffset e with
  | some (b, o) =>
    fromExprAux b (inc + o)
  | none =>
    return if inc != 0 then some (e, inc) else none

/- Attempt to parse a `NatOffset` from an expression-/
private def NatOffset.fromExpr? (e : Expr) (inc : Nat := 0) : Meta.SimpM (Option NatOffset) := do
  match ← Nat.fromExpr? e with
  | some n => pure (some (const (n + inc)))
  | none =>
    match ← fromExprAux e inc with
    | none => pure none
    | some (b, o) => pure (some (offset b (toExpr o) o))

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

private def mkBEqNatInstance : Expr :=
  mkAppN (mkConst ``instBEqOfDecidableEq [levelZero]) #[mkConst ``Nat, mkConst ``instDecidableEqNat []]

private def mkBEqNat (x y : Expr) : Expr :=
  mkAppN (mkConst ``BEq.beq [levelZero]) #[mkConst ``Nat, mkBEqNatInstance, x, y]

private def mkBneNat (x y : Expr) : Expr :=
  mkAppN (mkConst ``bne [levelZero]) #[mkConst ``Nat, mkBEqNatInstance, x, y]

private def mkLENat (x y : Expr) : Expr :=
  mkAppN (.const ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat, x, y]

private def mkGENat (x y : Expr) : Expr := mkLENat y x

private def mkLTNat (x y : Expr) : Expr :=
  mkAppN (.const ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat, x, y]

private def mkGTNat (x y : Expr) : Expr := mkLTNat y x

private def mkOfDecideEqTrue (p : Expr) : MetaM Expr := do
  let d ← Meta.mkDecide p
  pure <| mkAppN (mkConst ``of_decide_eq_true) #[p, d.appArg!, (← Meta.mkEqRefl (mkConst ``true))]

def applySimprocConst (expr : Expr) (nm : Name) (args : Array Expr) : SimpM Step := do
  unless (← getEnv).contains nm do return .continue
  let finProof := mkAppN (mkConst nm) args
  return .visit { expr, proof? := finProof, cache := true }

inductive EqResult where
| decide (b : Bool) : EqResult
| false (p : Expr) : EqResult
| eq (x y : Expr) (p : Expr) : EqResult

def applyEqLemma (e : Expr → EqResult) (lemmaName : Name) (args : Array Expr) : SimpM (Option EqResult) := do
  unless (← getEnv).contains lemmaName do
    return none
  return .some (e (mkAppN (mkConst lemmaName) args))

def reduceNatEqExpr (x y : Expr) : SimpM (Option EqResult):= do
  let some xno ← NatOffset.fromExpr? x | return none
  let some yno ← NatOffset.fromExpr? y | return none
  match xno, yno with
  | .const xn, .const yn =>
    return some (.decide (xn = yn))
  | .offset xb xo xn, .const yn => do
    if xn ≤ yn then
      let leProof ← mkOfDecideEqTrue (mkLENat xo y)
      applyEqLemma (.eq xb (toExpr (yn - xn))) ``Nat.Simproc.add_eq_le #[xb, xo, y, leProof]
    else
      let gtProof ← mkOfDecideEqTrue (mkGTNat xo y)
      applyEqLemma .false ``Nat.Simproc.add_eq_gt  #[xb, xo, y, gtProof]
  | .const xn, .offset yb yo yn => do
    if yn ≤ xn then
      let leProof ← mkOfDecideEqTrue (mkLENat yo x)
      applyEqLemma (.eq yb (toExpr (xn - yn))) ``Nat.Simproc.eq_add_le  #[x, yb, yo, leProof]
    else
      let gtProof ← mkOfDecideEqTrue (mkGTNat yo x)
      applyEqLemma .false ``Nat.Simproc.eq_add_gt #[x, yb, yo, gtProof]
  | .offset xb xo xn, .offset yb yo yn => do
    if xn ≤ yn then
      let zb := (if xn = yn then yb else mkAddNat yb (toExpr (yn - xn)))
      let leProof ← mkOfDecideEqTrue (mkLENat xo yo)
      applyEqLemma (.eq xb zb) ``Nat.Simproc.add_eq_add_le #[xb, yb, xo, yo, leProof]
    else
      let zb := mkAddNat xb (toExpr (xn - yn))
      let geProof ← mkOfDecideEqTrue (mkGENat xo yo)
      applyEqLemma (.eq zb yb) ``Nat.Simproc.add_eq_add_ge #[xb, yb, xo, yo, geProof]

builtin_simproc [simp, seval] reduceEqDiff ((_ : Nat) = _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do
    return .continue
  let x := e.appFn!.appArg!
  let y := e.appArg!
  match ← reduceNatEqExpr x y with
  | none =>
    return .continue
  | some (.decide true) =>
    let d ← mkDecide e
    let p := mkAppN (mkConst ``eq_true_of_decide)  #[e, d.appArg!, (← mkEqRefl (mkConst ``true))]
    return .done  { expr := mkConst ``True,  proof? := some p, cache := true }
  | some (.decide false) =>
    let d ← mkDecide e
    let p := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))]
    return .done  { expr := mkConst ``False, proof? := some p, cache := true }
  | some (.false p)  =>
    return .done  { expr := mkConst ``False, proof? := some p, cache := true }
  | some (.eq x y p) =>
    return .visit { expr := mkEqNat x y,     proof? := some p, cache := true }

builtin_simproc [simp, seval] reduceBeqDiff ((_ : Nat) == _) := fun e => do
  unless e.isAppOfArity ``BEq.beq 4 do
    return .continue
  let x := e.appFn!.appArg!
  let y := e.appArg!
  match ← reduceNatEqExpr x y with
  | none =>
    return .continue
  | some (.decide b) =>
    return .done { expr := toExpr b }
  | some (.false p) =>
    let q := mkAppN (mkConst ``Nat.Simproc.beqFalseOfEqFalse) #[x, y, p]
    return .done  { expr := mkConst ``false, proof? := some q, cache := true }
  | some (.eq u v p) =>
    let q := mkAppN (mkConst ``Nat.Simproc.beqEqOfEqEq) #[x, y, u, v, p]
    return .visit { expr := mkBEqNat u v, proof? := some q, cache := true }

builtin_simproc [simp, seval] reduceBneDiff ((_ : Nat) != _) := fun e => do
  unless e.isAppOfArity ``bne 4 do
    return .continue
  let x := e.appFn!.appArg!
  let y := e.appArg!
  match ← reduceNatEqExpr x y with
  | none =>
    return .continue
  | some (.decide b) =>
    return .done { expr := toExpr (!b) }
  | some (.false p) =>
    let q := mkAppN (mkConst ``Nat.Simproc.bneTrueOfEqFalse) #[x, y, p]
    return .done  { expr := mkConst ``true, proof? := some q, cache := true }
  | some (.eq u v p) =>
    let q := mkAppN (mkConst ``Nat.Simproc.bneEqOfEqEq) #[x, y, u, v, p]
    return .visit { expr := mkBneNat u v, proof? := some q, cache := true }

def reduceLTLE (nm : Name) (arity : Nat) (isLT : Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity nm arity do
    return .continue
  let x := e.appFn!.appArg!
  let y := e.appArg!
  let some xno ← NatOffset.fromExpr? x (inc := cond isLT 1 0) | return .continue
  let some yno ← NatOffset.fromExpr? y | return .continue
  match xno, yno with
  | .const xn, .const yn =>
    Meta.Simp.evalPropStep e (xn ≤ yn)
  | .offset xb xo xn, .const yn => do
    if xn ≤ yn then
      let finExpr := mkLENat xb (toExpr (yn - xn))
      let leProof ← mkOfDecideEqTrue (mkLENat xo y)
      applySimprocConst finExpr ``Nat.Simproc.add_le_le #[xb, xo, y, leProof]
    else
      let gtProof ← mkOfDecideEqTrue (mkGTNat xo y)
      applySimprocConst (mkConst ``False) ``Nat.Simproc.add_le_gt #[xb, xo, y, gtProof]
  | .const xn, .offset yb yo yn => do
    if xn ≤ yn then
      let leProof ← mkOfDecideEqTrue (mkLENat x yo)
      applySimprocConst (mkConst ``True) ``Nat.Simproc.le_add_le #[x, yb, yo, leProof]
    else
      let finExpr := mkLENat (toExpr (xn - yn)) yb
      let geProof ← mkOfDecideEqTrue (mkGENat x yo)
      applySimprocConst finExpr ``Nat.Simproc.le_add_ge #[x, yb, yo, geProof]
  | .offset xb xo xn, .offset yb yo yn => do
    if xn ≤ yn then
      let finExpr := mkLENat xb (if xn = yn then yb else mkAddNat yb (toExpr (yn - xn)))
      let leProof ← mkOfDecideEqTrue (mkLENat xo yo)
      applySimprocConst finExpr ``Nat.Simproc.add_le_add_le  #[xb, yb, xo, yo, leProof]
    else
      let finExpr := mkLENat (mkAddNat xb (toExpr (xn - yn))) yb
      let geProof ← mkOfDecideEqTrue (mkGENat xo yo)
      applySimprocConst finExpr ``Nat.Simproc.add_le_add_ge  #[xb, yb, xo, yo, geProof]

builtin_simproc [simp, seval] reduceLeDiff ((_ : Nat) ≤ _) := reduceLTLE ``LE.le 4 false

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
      let finExpr := if pn = n then pb else mkSubNat pb (toExpr (n - pn))
      let leProof ← mkOfDecideEqTrue (mkLENat po q)
      applySimprocConst finExpr ``Nat.Simproc.add_sub_le  #[pb, po, q, leProof]
    else
      let finExpr := mkAddNat pb (toExpr (pn - n))
      let geProof ← mkOfDecideEqTrue (mkGENat po q)
      applySimprocConst finExpr ``Nat.add_sub_assoc #[po, q, geProof, pb]
  | .const po, .offset nb no nn => do
      let finExpr := mkSubNat (toExpr (po - nn)) nb
      applySimprocConst finExpr ``Nat.Simproc.sub_add_eq_comm #[p, nb, no]
  | .offset pb po pn, .offset nb no nn => do
    if pn ≤ nn then
      let finExpr := mkSubNat pb (if pn = nn then nb else mkAddNat nb (toExpr (nn - pn)))
      let leProof ← mkOfDecideEqTrue (mkLENat po no)
      applySimprocConst finExpr ``Nat.Simproc.add_sub_add_le #[pb, nb, po, no, leProof]
    else
      let finExpr := mkSubNat (mkAddNat pb (toExpr (pn - nn))) nb
      let geProof ← mkOfDecideEqTrue (mkGENat po no)
      applySimprocConst finExpr ``Nat.Simproc.add_sub_add_ge #[pb, nb, po, no, geProof]

end Nat
