/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify

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

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).linarith do return ()
  let some type := getType? e | return ()
  if isForbiddenParent parent? then return ()
  let some structId ← getStructId? type | return ()
  LinearM.run structId do
    trace[grind.linarith.internalize] "{e}"
    setTermStructId e
    markAsLinarithTerm e

end Lean.Meta.Grind.Arith.Linear
