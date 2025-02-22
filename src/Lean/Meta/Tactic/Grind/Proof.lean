/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
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
  if heq then return h else mkEqOfHEq h (check := false)

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

/--
Returns `true` if we can construct a congruence proof for `lhs = rhs` using `congrArg`, `congrFun`, and `congr`.
`f` (`g`) is the function of the `lhs` (`rhs`) application. `numArgs` is the number of arguments.
-/
private partial def isCongrDefaultProofTarget (lhs rhs : Expr) (f g : Expr) (numArgs : Nat) : GoalM Bool := do
  unless isSameExpr f g do return false
  let info := (← getFunInfo f).paramInfo
  let rec loop (lhs rhs : Expr) (i : Nat) : GoalM Bool := do
    if lhs.isApp then
      let a₁ := lhs.appArg!
      let a₂ := rhs.appArg!
      let i  := i - 1
      unless isSameExpr a₁ a₂ do
        if h : i < info.size then
          if info[i].hasFwdDeps then
            -- Cannot use `congrArg` because there are forward dependencies
            return false
        else
          return false -- Don't have information about argument
      loop lhs.appFn! rhs.appFn! i
    else
      return true
  loop lhs rhs numArgs

mutual
  /--
  Given `lhs` and `rhs` proof terms of the form `nestedProof p hp` and `nestedProof q hq`,
  constructs a congruence proof for `HEq (nestedProof p hp) (nestedProof q hq)`.
  `p` and `q` are in the same equivalence class.
  -/
  private partial def mkNestedProofCongr (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    let p  := lhs.appFn!.appArg!
    let hp := lhs.appArg!
    let q  := rhs.appFn!.appArg!
    let hq := rhs.appArg!
    let h  := mkApp5 (mkConst ``Lean.Grind.nestedProof_congr) p q (← mkEqProofCore p q false) hp hq
    mkEqOfHEqIfNeeded h heq

  /--
  Constructs a congruence proof for `lhs` and `rhs` using `congr`, `congrFun`, and `congrArg`.
  This function assumes `isCongrDefaultProofTarget` returned `true`.
  -/
  private partial def mkCongrDefaultProof (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    let rec loop (lhs rhs : Expr) : GoalM (Option Expr) := do
      if lhs.isApp then
        let a₁ := lhs.appArg!
        let a₂ := rhs.appArg!
        if let some proof ← loop lhs.appFn! rhs.appFn! then
          if isSameExpr a₁ a₂ then
            mkCongrFun proof a₁
          else
            mkCongr proof (← mkEqProofCore a₁ a₂ false)
        else if isSameExpr a₁ a₂ then
          return none -- refl case
        else
          mkCongrArg lhs.appFn! (← mkEqProofCore a₁ a₂ false)
      else
        return none
    let r := (← loop lhs rhs).get!
    if heq then mkHEqOfEq r else return r

  private partial def mkHCongrProof (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let numArgs := lhs.getAppNumArgs
    assert! rhs.getAppNumArgs == numArgs
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

  private partial def mkEqCongrProof (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    let_expr f@Eq α₁ a₁ b₁ := lhs | unreachable!
    let_expr Eq α₂ a₂ b₂ := rhs | unreachable!
    let enodes := (← get).enodes
    let us := f.constLevels!
    if !isSameExpr α₁ α₂ then
      mkHCongrProof lhs rhs heq
    else if hasSameRoot enodes a₁ a₂ && hasSameRoot enodes b₁ b₂ then
      return mkApp7 (mkConst ``Grind.eq_congr us) α₁ a₁ b₁ a₂ b₂ (← mkEqProofCore a₁ a₂ false) (← mkEqProofCore b₁ b₂ false)
    else
      assert! hasSameRoot enodes a₁ b₂ && hasSameRoot enodes b₁ a₂
      return mkApp7 (mkConst ``Grind.eq_congr' us) α₁ a₁ b₁ a₂ b₂ (← mkEqProofCore a₁ b₂ false) (← mkEqProofCore b₁ a₂ false)

  /-- Constructs a congruence proof for `lhs` and `rhs`. -/
  private partial def mkCongrProof (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    let f := lhs.getAppFn
    let g := rhs.getAppFn
    let numArgs := lhs.getAppNumArgs
    assert! rhs.getAppNumArgs == numArgs
    if f.isConstOf ``Lean.Grind.nestedProof && g.isConstOf ``Lean.Grind.nestedProof && numArgs == 2 then
      mkNestedProofCongr lhs rhs heq
    else if f.isConstOf ``Eq && g.isConstOf ``Eq && numArgs == 3 then
      mkEqCongrProof lhs rhs heq
    else if (← isCongrDefaultProofTarget lhs rhs f g numArgs) then
      mkCongrDefaultProof lhs rhs heq
    else
      mkHCongrProof lhs rhs heq

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

  /--
  Returns a proof of `lhs = rhs` (`HEq lhs rhs`) if `heq = false` (`heq = true`).
  If `heq = false`, this function assumes that `lhs` and `rhs` have the same type.
  -/
  private partial def mkEqProofCore (lhs rhs : Expr) (heq : Bool) : GoalM Expr := do
    if isSameExpr lhs rhs then
      return (← mkRefl lhs heq)
    -- The equivalence class contains `HEq` proofs. So, we build a proof using HEq. Otherwise, we use `Eq`.
    let heqProofs := (← getRootENode lhs).heqProofs
    let n₁ ← getENode lhs
    let n₂ ← getENode rhs
    assert! isSameExpr n₁.root n₂.root
    let common ← findCommon lhs rhs
    let lhsEqCommon? ← mkProofTo lhs common none heqProofs
    let some lhsEqRhs ← mkProofFrom rhs common lhsEqCommon? heqProofs | unreachable!
    if heq == heqProofs then
      return lhsEqRhs
    else if heq then
      mkHEqOfEq lhsEqRhs
    else
      mkEqOfHEq lhsEqRhs (check := false)

end

/--
Returns a proof that `a = b`.
It assumes `a` and `b` are in the same equivalence class.
-/
@[export lean_grind_mk_eq_proof]
def mkEqProofImpl (a b : Expr) : GoalM Expr := do
  assert! (← hasSameType a b)
  mkEqProofCore a b (heq := false)

@[export lean_grind_mk_heq_proof]
def mkHEqProofImpl (a b : Expr) : GoalM Expr :=
  mkEqProofCore a b (heq := true)

end Lean.Meta.Grind
