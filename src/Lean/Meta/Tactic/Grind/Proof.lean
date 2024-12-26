/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Sorry -- TODO: remove
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

private def isEqProof (h : Expr) : MetaM Bool := do
  return (← whnfD (← inferType h)).isAppOf ``Eq

private def flipProof (h : Expr) (flipped : Bool) (heq : Bool) : MetaM Expr := do
  let mut h' := h
  if (← pure heq <&&> isEqProof h') then
    h' ← mkHEqOfEq h'
  if flipped then
    if heq then mkHEqSymm h' else mkEqSymm h'
  else
    return h'

private def mkRefl (a : Expr) (heq : Bool) : MetaM Expr :=
  if heq then mkHEqRefl a else mkEqRefl a

private def mkTrans (h₁ h₂ : Expr) (heq : Bool) : MetaM Expr :=
  if heq then
    mkHEqTrans h₁ h₂
  else
    mkEqTrans h₁ h₂

private def mkTrans' (h₁ : Option Expr) (h₂ : Expr) (heq : Bool) : MetaM Expr := do
  let some h₁ := h₁ | return h₂
  mkTrans h₁ h₂ heq

/--
Given `h : HEq a b`, returns a proof `a = b` if `heq == false`.
Otherwise, it returns `h`.
-/
private def mkEqOfHEqIfNeeded (h : Expr) (heq : Bool) : MetaM Expr := do
  if heq then return h else mkEqOfHEq h

/--
Given `lhs` and `rhs` that are in the same equivalence class,
find the common expression that are in the paths from `lhs` and `rhs` to
the root of their equivalence class.
Recall that this expression must exist since it is the root itself in the
worst case.
-/
private def findCommon (lhs rhs : Expr) : GoalM Expr := do
  let mut visited : RBMap Nat Expr compare := {}
  let mut it := lhs
  -- Mark elements found following the path from `lhs` to the root.
  repeat
    let n ← getENode it
    visited := visited.insert n.idx n.self
    let some target := n.target? | break
    it := target
  -- Find the marked element from the path from `rhs` to the root.
  it := rhs
  repeat
    let n ← getENode it
    if let some common := visited.find? n.idx then
      return common
    let some target := n.target? | unreachable! --
    it := target
  unreachable!

mutual
  private partial def mkNestedProofCongr (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    let p  := lhs.appFn!.appArg!
    let hp := lhs.appArg!
    let q  := rhs.appFn!.appArg!
    let hq := rhs.appArg!
    let h  := mkApp5 (mkConst ``Lean.Grind.nestedProof_congr) p q (← mkEqProofCore p q false) hp hq
    mkEqOfHEqIfNeeded h heq

  private partial def mkCongrProof (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let numArgs := lhs.getAppNumArgs
    assert! rhs.getAppNumArgs == numArgs
    if f.isConstOf ``Lean.Grind.nestedProof && g.isConstOf ``Lean.Grind.nestedProof && numArgs == 2 then
      mkNestedProofCongr lhs rhs heq
    else
      let thm ← mkHCongrWithArity f numArgs
      assert! thm.argKinds.size == numArgs
      let rec loop (lhs rhs : Expr) (i : Nat) : GoalM Expr := do
        let i := i - 1
        if lhs.isApp then
          let proof ← loop lhs.appFn! rhs.appFn! i
          let a₁  := lhs.appArg!
          let a₂  := rhs.appArg!
          let k   := thm.argKinds[i]!
          return mkApp3 proof a₁ a₂ (← mkEqProofCore a₁ a₂ (k matches .heq))
        else
          return thm.proof
      let proof ← loop lhs rhs numArgs
      if isSameExpr f g then
        mkEqOfHEqIfNeeded proof heq
      else
        /-
        `lhs` is of the form `f a_1 ... a_n`
        `rhs` is of the form `g b_1 ... b_n`
        `proof : HEq (f a_1 ... a_n) (f b_1 ... b_n)`
        We construct a proof for `HEq (f a_1 ... a_n) (g b_1 ... b_n)` using `Eq.ndrec`
        -/
        let motive ← withLocalDeclD (← mkFreshUserName `x) (← inferType f) fun x => do
          mkLambdaFVars #[x] (← mkHEq lhs (mkAppN x rhs.getAppArgs))
        let fEq ← mkEqProofCore f g false
        let proof ← mkEqNDRec motive proof fEq
        mkEqOfHEqIfNeeded proof heq

  private partial def realizeEqProof (lhs rhs : Expr) (h : Expr) (flipped : Bool) (heq : Bool) : GoalM Expr := do
    let h ← if h == congrPlaceholderProof then
      mkCongrProof lhs rhs heq
    else
      flipProof h flipped heq

  /-- Given `acc : lhs₀ = lhs`, returns a proof of `lhs₀ = common`. -/
  private partial def mkProofTo (lhs : Expr) (common : Expr) (acc : Option Expr) (heq : Bool) : GoalM (Option Expr) := do
    if isSameExpr lhs common then
      return acc
    let n ← getENode lhs
    let some target := n.target? | unreachable!
    let some h := n.proof? | unreachable!
    let h ← realizeEqProof lhs target h n.flipped heq
    -- h : lhs = target
    let acc ← mkTrans' acc h heq
    mkProofTo target common (some acc) heq

  /-- Given `lhsEqCommon : lhs = common`, returns a proof for `lhs = rhs`. -/
  private partial def mkProofFrom (rhs : Expr) (common : Expr) (lhsEqCommon? : Option Expr) (heq : Bool) : GoalM (Option Expr) := do
    if isSameExpr rhs common then
      return lhsEqCommon?
    let n ← getENode rhs
    let some target := n.target? | unreachable!
    let some h := n.proof? | unreachable!
    let h ← realizeEqProof target rhs h (!n.flipped) heq
    -- `h : target = rhs`
    let h' ← mkProofFrom target common lhsEqCommon? heq
    -- `h' : lhs = target`
    mkTrans' h' h heq

  private partial def mkEqProofCore (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    if isSameExpr lhs rhs then
      return (← mkRefl lhs heq)
    let n₁ ← getENode lhs
    let n₂ ← getENode rhs
    assert! isSameExpr n₁.root n₂.root
    let common ← findCommon lhs rhs
    let lhsEqCommon? ← mkProofTo lhs common none heq
    let some lhsEqRhs ← mkProofFrom rhs common lhsEqCommon? heq | unreachable!
    return lhsEqRhs
end

/--
Returns a proof that `a = b` (or `HEq a b`).
It assumes `a` and `b` are in the same equivalence class.
-/
def mkEqProof (a b : Expr) : GoalM Expr := do
  let p ← go
  trace[grind.proof.detail] "{p}"
  return p
where
  go : GoalM Expr := do
    let n ← getRootENode a
    if !n.heqProofs then
      trace[grind.proof] "{a} = {b}"
      mkEqProofCore a b (heq := false)
    else
      if (← withDefault <| isDefEq (← inferType a) (← inferType b)) then
        trace[grind.proof] "{a} = {b}"
        mkEqOfHEq (← mkEqProofCore a b (heq := true))
      else
        trace[grind.proof] "{a} ≡ {b}"
        mkEqProofCore a b (heq := true)

def mkHEqProof (a b : Expr) : GoalM Expr :=
  mkEqProofCore a b (heq := true)

/--
Returns a proof that `a = True`.
It assumes `a` and `True` are in the same equivalence class.
-/
def mkEqTrueProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getTrueExpr)

/--
Returns a proof that `a = False`.
It assumes `a` and `False` are in the same equivalence class.
-/
def mkEqFalseProof (a : Expr) : GoalM Expr := do
  mkEqProof a (← getFalseExpr)

end Lean.Meta.Grind
