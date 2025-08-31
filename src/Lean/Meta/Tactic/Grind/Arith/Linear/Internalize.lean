/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
public import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
public import Lean.Meta.Tactic.Grind.Arith.Linear.Reify

public section

namespace Lean.Meta.Grind.Arith


namespace Linear

/-- If `e` is a function application supported by the linarith module, return its type. -/
private def getType? (e : Expr) : Option Expr :=
  match_expr e with
  | HAdd.hAdd _ _ α _ _ _ => some α
  | HSub.hSub _ _ α _ _ _ => some α
  | HMul.hMul _ _ α _ _ _ => some α
  | HSMul.hSMul _ _ α _ _ _ => some α
  | Neg.neg α _ _ => some α
  | Zero.zero α _ => some α
  | One.one α _ => some α
  | OfNat.ofNat α _ _ => some α
  | NatCast.natCast α _ _ => some α
  | IntCast.intCast α _ _ => some α
  | _ => none

private def isForbiddenParent (parent? : Option Expr) : Bool :=
  if let some parent := parent? then
    if getType? parent |>.isSome then
      true
    else
      -- We also ignore the following parents.
      -- Remark: `HDiv` should appear in `getType?` as soon as we add support for `Field`
      match_expr parent with
      | LT.lt _ _ _ _ => true
      | LE.le _ _ _ _ => true
      | HDiv.hDiv _ _ _ _ _ _ => true
      | HMod.hMod _ _ _ _ _ _ => true
      | _ => false
  else
    true

partial def markVars (e : Expr) : LinearM Unit := do
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if isAddInst (← getStruct) i then markVars a; markVars b else markVar e
  | HSub.hSub _ _ _ i a b => if isSubInst (← getStruct) i then markVars a; markVars b else markVar e
  | HMul.hMul _ _ _ i a b =>
    if isHomoMulInst (← getStruct) i then
      if isNumeral a then
        return (← markVar b)
      else if isNumeral b then
        return (← markVar a)
      else
        markVar a; markVar b; markVar e
        return
    markVar e
  | HSMul.hSMul _ _ _ i a b =>
    if isSMulIntInst (← getStruct) i then
      if (← getIntValue? a).isSome then
        return (← markVar b)
    if isSMulNatInst (← getStruct) i then
      if (← getNatValue? a).isSome then
        return (← markVar b)
    markVar e
  | Neg.neg _ _ a => markVars a
  | Zero.zero _ _ => return ()
  | OfNat.ofNat _ _ _ => return ()
  | _ => markVar e
where
  markVar (e : Expr) : LinearM Unit :=
    discard <| mkVar e
  isNumeral (e : Expr) : Bool :=
    match_expr e with
    | Neg.neg _ _ a => isNumeral a
    | OfNat.ofNat _ n _ => isNatNum n
    | _ => false

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).linarith do return ()
  if isIntModuleVirtualParent parent? then
    -- `e` is an auxiliary term used to convert `CommRing` to `IntModule`
    return ()
  let some type := getType? e | return ()
  if isForbiddenParent parent? then return ()
  let some structId ← getStructId? type | return ()
  LinearM.run structId do
    trace[grind.linarith.internalize] "{e}"
    setTermStructId e
    markAsLinarithTerm e
    markVars e

end Lean.Meta.Grind.Arith.Linear
