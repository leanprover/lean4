/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.Basic
public import Init.Simproc
public import Lean.Meta.Tactic.Grind.SynthInstance
import Init.Grind.Ring.Field
import Lean.Meta.Tactic.Grind.Arith.FieldNormNum
public section
namespace Lean.Meta.Grind.Arith

def mkSemiringThm (declName : Name) (α : Expr) : MetaM (Option Expr) := do
  let some u ← getDecLevel? α | return none
  let semiring := mkApp (mkConst ``Grind.Semiring [u]) α
  let some semiringInst ← synthInstanceMeta? semiring | return none
  return mkApp2 (mkConst declName [u]) α semiringInst

/--
Applies `a^0 = 1`, `a^1 = a`.

We do normalize `a^0` and `a^1` when converting expressions into polynomials,
but we need to normalize them here when for other preprocessing steps such as
`a / b = a*b⁻¹`. If `b` is of the form `c^1`, it will be treated as an
atom in the ring module.

**Note**: We used to expand `a^(n+m)` here, but it prevented `grind` from solving
simple problems such as
```
example {k : Nat} (h : k - 1 + 1 = k) :
    2 ^ (k - 1 + 1) = 2 ^ k := by
  grind
```
We now use a propagator for `a^(n+m)` which adds the `a^n*a^m` to the equivalence class.
-/
builtin_simproc_decl expandPow01 (_ ^ _) := fun e => do
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
  return .continue

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

builtin_simproc_decl normFieldInv (_ ⁻¹) := fun e => do
  let_expr Inv.inv α _ a ← e | return .continue
  if isNotFieldQuick α then return .continue
  match_expr a with
  | NatCast.natCast _ _ _ => return .continue -- Already normalized
  | OfNat.ofNat _ _ _ => return .continue -- Already normalized
  | _ =>
  let some (expr, h) ← normFieldExpr? e α | return .continue
  checkWithKernel h
  return .done { expr, proof? := h }

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
  unless (← withReducibleAndInstances <| isDefEq inst instCurr) do return .continue
  e.withApp fun f args => do
    let args := args.set! instPos inst
    return .visit (mkAppN f args)

builtin_dsimproc_decl normNatAddInst ((_ + _ : Nat)) := normInst 3 Nat.mkInstHAdd
builtin_dsimproc_decl normNatMulInst ((_ * _ : Nat)) := normInst 3 Nat.mkInstHMul
builtin_dsimproc_decl normNatSubInst ((_ - _ : Nat)) := normInst 3 Nat.mkInstHSub
builtin_dsimproc_decl normNatDivInst ((_ / _ : Nat)) := normInst 3 Nat.mkInstHDiv
builtin_dsimproc_decl normNatModInst ((_ % _ : Nat)) := normInst 3 Nat.mkInstMod
builtin_dsimproc_decl normNatPowInst ((_ ^ _ : Nat)) := normInst 3 Nat.mkInstHPow

/--
Returns `true`, if `@OfNat.ofNat α n inst` is the standard way we represent `Nat` numerals in Lean.
-/
private def isNormNatNum (α n inst : Expr) : Bool := Id.run do
  unless α.isConstOf ``Nat do return false
  let .lit (.natVal _) := n | return false
  unless inst.isAppOfArity ``instOfNatNat 1 do return false
  return inst.appArg! == n

builtin_dsimproc_decl normNatOfNatInst ((OfNat.ofNat _: Nat)) := fun e => do
  let_expr OfNat.ofNat α n inst := e | return .continue
  if isNormNatNum α n inst then
    return .done e
  let some n ← getNatValue? e | return .continue
  return .done (mkNatLit n)

builtin_dsimproc_decl normIntNegInst ((- _ : Int)) := normInst 1 Int.mkInstNeg
builtin_dsimproc_decl normIntAddInst ((_ + _ : Int)) := normInst 3 Int.mkInstHAdd
builtin_dsimproc_decl normIntMulInst ((_ * _ : Int)) := normInst 3 Int.mkInstHMul
builtin_dsimproc_decl normIntSubInst ((_ - _ : Int)) := normInst 3 Int.mkInstHSub
builtin_dsimproc_decl normIntDivInst ((_ / _ : Int)) := normInst 3 Int.mkInstHDiv
builtin_dsimproc_decl normIntModInst ((_ % _ : Int)) := normInst 3 Int.mkInstMod
builtin_dsimproc_decl normIntPowInst ((_ ^ _ : Int)) := normInst 3 Int.mkInstHPow
builtin_dsimproc_decl normNatCastInst ((NatCast.natCast _ : Int)) := normInst 1 Int.mkInstNatCast

/--
Returns `true`, if `@OfNat.ofNat α n inst` is the standard way we represent `Int` numerals in Lean.
-/
private def isNormIntNum (α n inst : Expr) : Bool := Id.run do
  unless α.isConstOf ``Int do return false
  let .lit (.natVal _) := n | return false
  unless inst.isAppOfArity ``instOfNat 1 do return false
  return inst.appArg! == n

builtin_dsimproc_decl normIntOfNatInst ((OfNat.ofNat _: Int)) := fun e => do
  let_expr OfNat.ofNat α n inst := e | return .continue
  if isNormIntNum α n inst then
    return .done e
  let some n ← getIntValue? e | return .continue
  return .done (mkIntLit n)

builtin_simproc_decl normNatCastNum (NatCast.natCast _) := fun e => do
  let_expr f@NatCast.natCast α _ a := e | return .continue
  let some k ← getNatValue? a | return .continue
  let us := f.constLevels!
  let semiring := mkApp (mkConst ``Grind.Semiring us) α
  let some semiringInst ← synthInstanceMeta? semiring | return .continue
  let n ← mkNumeral α k
  -- **Note**: TODO missing sanity check on instances
  let h := mkApp3 (mkConst ``Grind.Semiring.natCast_eq_ofNat us) α semiringInst a
  return .done { expr := n, proof? := some h }

builtin_simproc_decl normIntCastNum (IntCast.intCast _) := fun e => do
  let_expr f@IntCast.intCast α _ a := e | return .continue
  let some k ← getIntValue? a | return .continue
  let us := f.constLevels!
  let ring := mkApp (mkConst ``Grind.Ring us) α
  let some ringInst ← synthInstanceMeta? ring | return .continue
  let n ← mkNumeral α k.natAbs
  -- **Note**: TODO missing sanity check on instances
  if k < 0 then
    let some negInst ← synthInstanceMeta? (mkApp (mkConst ``Neg us) α) | return .continue
    let n := mkApp3 (mkConst ``Neg.neg us) α negInst n
    let h := mkApp4 (mkConst ``Grind.Ring.intCast_eq_ofNat_of_nonpos us) α ringInst a eagerReflBoolTrue
    return .done { expr := n, proof? := some h }
  else
    let h := mkApp4 (mkConst ``Grind.Ring.intCast_eq_ofNat_of_nonneg us) α ringInst a eagerReflBoolTrue
    return .done { expr := n, proof? := some h }

builtin_dsimproc [simp, seval] normPowRatInt ((_ : Rat) ^ (_ : Int)) := fun e => do
  let_expr HPow.hPow _ _ _ _ a b ← e | return .continue
  let some v₁ ← getRatValue? a | return .continue
  let some v₂ ← getIntValue? b | return .continue
  let warning := (← Simp.getConfig).warnExponents
  unless (← checkExponent v₂.natAbs (warning := warning)) do return .continue
  if v₂ < 0 then
    -- **Note**: we use `Rat.zpow_neg` as a normalization rule
    return .continue
  else
    return .done <| toExpr (v₁ ^ v₂)

/-!
Add additional arithmetic simprocs
-/

def addSimproc (s : Simprocs) : CoreM Simprocs := do
  let s ← s.add ``expandPow01 (post := true)
  let s ← s.add ``expandDiv (post := true)
  let s ← s.add ``normNatAddInst (post := false)
  let s ← s.add ``normNatMulInst (post := false)
  let s ← s.add ``normNatSubInst (post := false)
  let s ← s.add ``normNatDivInst (post := false)
  let s ← s.add ``normNatModInst (post := false)
  let s ← s.add ``normNatPowInst (post := false)
  let s ← s.add ``normNatOfNatInst (post := false)
  let s ← s.add ``normIntNegInst (post := false)
  let s ← s.add ``normIntAddInst (post := false)
  let s ← s.add ``normIntMulInst (post := false)
  let s ← s.add ``normIntSubInst (post := false)
  let s ← s.add ``normIntDivInst (post := false)
  let s ← s.add ``normIntModInst (post := false)
  let s ← s.add ``normIntPowInst (post := false)
  let s ← s.add ``normNatCastInst (post := false)
  let s ← s.add ``normIntOfNatInst (post := false)
  let s ← s.add ``normNatCastNum (post := false)
  let s ← s.add ``normIntCastNum (post := false)
  let s ← s.add ``normPowRatInt (post := false)
  let s ← s.add ``normFieldInv (post := false)
  return s

end Lean.Meta.Grind.Arith
