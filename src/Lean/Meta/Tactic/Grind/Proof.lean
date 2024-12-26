/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Sorry -- TODO: remove
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

-- TODO: delete after done
private def mkTodo (a b : Expr) (heq : Bool) : MetaM Expr := do
  if heq then
    mkSorry (← mkHEq a b) (synthetic := false)
  else
    mkSorry (← mkEq a b) (synthetic := false)

private def isProtoProof (h : Expr) : Bool :=
  isSameExpr h congrPlaceholderProof

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
  private partial def mkCongrProof (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    -- TODO: implement
    mkTodo lhs rhs heq

  private partial def realizeEqProof (lhs rhs : Expr) (h : Expr) (flipped : Bool) (heq : Bool) : GoalM Expr := do
    let h ← if h == congrPlaceholderProof then
      mkCongrProof lhs rhs heq
    else
      flipProof h flipped heq

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

  /--
  Given `lhsEqCommon : lhs = common`, returns a proof for `lhs = rhs`.
  -/
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
  let n ← getRootENode a
  trace[grind.proof] "{a} {if n.heqProofs then "≡" else "="} {b}"
  if !n.heqProofs then
    mkEqProofCore a b (heq := false)
  else if (← withDefault <| isDefEq (← inferType a) (← inferType b)) then
    mkEqProofCore a b (heq := false)
  else
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
