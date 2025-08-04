/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Grind.Ring.Basic
public import Init.Simproc
public import Lean.Meta.Tactic.Simp.Simproc
public import Lean.Meta.Tactic.Grind.SynthInstance

public section

namespace Lean.Meta.Grind.Arith

private def mkSemiringThm (declName : Name) (α : Expr) : MetaM (Option Expr) := do
  let some u ← getDecLevel? α | return none
  let semiring := mkApp (mkConst ``Grind.Semiring [u]) α
  let some semiringInst ← synthInstanceMeta? semiring | return none
  return mkApp2 (mkConst declName [u]) α semiringInst

/--
Applies `a^(m+n) = a^m * a^n`, `a^0 = 1`, `a^1 = a`.

We do normalize `a^0` and `a^1` when converting expressions into polynomials,
but we need to normalize them here when for other preprocessing steps such as
`a / b = a*b⁻¹`. If `b` is of the form `c^1`, it will be treated as an
atom in the comm ring module.
-/
builtin_simproc_decl expandPowAdd (_ ^ _) := fun e => do
  let_expr HPow.hPow α nat α' _ a k := e | return .continue
  let_expr Nat ← nat | return .continue
  if let some k ← getNatValue? k then
    if k == 0 then
      unless (← isDefEq α α') do return .continue
      let some h ← mkSemiringThm ``Grind.Semiring.pow_zero α | return .continue
      let r ← mkNumeral α 1
      return .done { expr := r, proof? := some (mkApp h a) }
    else if k == 1 then
      unless (← isDefEq α α') do return .continue
      let some h ← mkSemiringThm ``Grind.Semiring.pow_one α | return .continue
      return .done { expr := a, proof? := some (mkApp h a) }
    else
      return .continue
  else
    let_expr HAdd.hAdd _ _ _ _ m n := k | return .continue
    unless (← isDefEq α α') do return .continue
    let some h ← mkSemiringThm ``Grind.Semiring.pow_add α | return .continue
    let pwFn := e.appFn!.appFn!
    let r ← mkMul (mkApp2 pwFn a m) (mkApp2 pwFn a n)
    return .visit { expr := r, proof? := some (mkApp3 h a m n) }

private def notField : Std.HashSet Name :=
  [``Nat, ``Int, ``BitVec, ``UInt8, ``UInt16, ``UInt32, ``Int64, ``Int8, ``Int16, ``Int32, ``Int64].foldl (init := {}) (·.insert ·)

private def isNotFieldQuick (type : Expr) : Bool := Id.run do
  let .const declName _ := type.getAppFn | return false
  return notField.contains declName

builtin_simproc_decl expandDiv (_ / _) := fun e => do
  let_expr f@HDiv.hDiv α β γ _ a b ← e | return .continue
  if isNotFieldQuick α then return .continue
  unless (← isDefEq α β <&&> isDefEq α γ) do return .continue
  let us := f.constLevels!
  let [u, _, _] := us | return .continue
  let field := mkApp (mkConst ``Grind.Field [u]) α
  let some fieldInst ← synthInstanceMeta? field | return .continue
  let some mulInst ← synthInstanceMeta? (mkApp3 (mkConst ``HMul us) α α α) | return .continue
  let some invInst ← synthInstanceMeta? (mkApp (mkConst ``Inv [u]) α) | return .continue
  let expr := mkApp6 (mkConst ``HMul.hMul us) α α α mulInst a (mkApp3 (mkConst ``Inv.inv [u]) α invInst b)
  return .visit { expr, proof? := some <| mkApp4 (mkConst ``Grind.Field.div_eq_mul_inv [u]) α fieldInst a b }

/-!
Normalize arithmetic instances for `Nat` and `Int` operations.
Recall that both `Nat` and `Int` have builtin support in `grind`,
and we use the default instances. However, Mathlib may register
nonstandard ones after instances such as
```
instance instDistrib : Distrib Nat where
  mul := (· * ·)
```
are added to the environment.
-/

/-- Generic instance normalizer -/
def normInst (instPos : Nat) (inst : Expr) (e : Expr) : SimpM Simp.DStep := do
  unless instPos < e.getAppNumArgs do return .continue
  let instCurr := e.getArg! instPos
  if inst == instCurr then return .continue
  unless (← isDefEq inst instCurr) do return .continue
  e.withApp fun f args => do
    let args := args.set! instPos inst
    return .visit (mkAppN f args)

builtin_dsimproc_decl normNatAddInst ((_ + _ : Nat)) := normInst 3 Nat.mkInstHAdd
builtin_dsimproc_decl normNatMulInst ((_ * _ : Nat)) := normInst 3 Nat.mkInstHMul
builtin_dsimproc_decl normNatSubInst ((_ - _ : Nat)) := normInst 3 Nat.mkInstHSub
builtin_dsimproc_decl normNatDivInst ((_ / _ : Nat)) := normInst 3 Nat.mkInstHDiv
builtin_dsimproc_decl normNatModInst ((_ % _ : Nat)) := normInst 3 Nat.mkInstMod
builtin_dsimproc_decl normNatPowInst ((_ ^ _ : Nat)) := normInst 3 Nat.mkInstHPow

builtin_dsimproc_decl normIntNegInst ((- _ : Int)) := normInst 1 Int.mkInstNeg
builtin_dsimproc_decl normIntAddInst ((_ + _ : Int)) := normInst 3 Int.mkInstHAdd
builtin_dsimproc_decl normIntMulInst ((_ * _ : Int)) := normInst 3 Int.mkInstHMul
builtin_dsimproc_decl normIntSubInst ((_ - _ : Int)) := normInst 3 Int.mkInstHSub
builtin_dsimproc_decl normIntDivInst ((_ / _ : Int)) := normInst 3 Int.mkInstHDiv
builtin_dsimproc_decl normIntModInst ((_ % _ : Int)) := normInst 3 Int.mkInstMod
builtin_dsimproc_decl normIntPowInst ((_ ^ _ : Int)) := normInst 3 Int.mkInstHPow

/-!
Add additional arithmetic simprocs
-/

def addSimproc (s : Simprocs) : CoreM Simprocs := do
  let s ← s.add ``expandPowAdd (post := true)
  let s ← s.add ``expandDiv (post := true)
  let s ← s.add ``normNatAddInst (post := false)
  let s ← s.add ``normNatMulInst (post := false)
  let s ← s.add ``normNatSubInst (post := false)
  let s ← s.add ``normNatDivInst (post := false)
  let s ← s.add ``normNatModInst (post := false)
  let s ← s.add ``normNatPowInst (post := false)
  let s ← s.add ``normIntNegInst (post := false)
  let s ← s.add ``normIntAddInst (post := false)
  let s ← s.add ``normIntMulInst (post := false)
  let s ← s.add ``normIntSubInst (post := false)
  let s ← s.add ``normIntDivInst (post := false)
  let s ← s.add ``normIntModInst (post := false)
  let s ← s.add ``normIntPowInst (post := false)
  return s

end Lean.Meta.Grind.Arith
