/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify

namespace Lean.Meta.Grind.Arith.CommRing

/-- If `e` is a function application supported by the `CommRing` module, return its type. -/
private def getType? (e : Expr) : Option Expr :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => some α
  | HSub.hSub α _ _ _ _ _ => some α
  | HMul.hMul α _ _ _ _ _ => some α
  | HPow.hPow α β _ _ _ _ =>
    let_expr Nat := β | none
    some α
  | Neg.neg α _ _ => some α
  | OfNat.ofNat α _ _ => some α
  | NatCast.natCast α _ _ => some α
  | IntCast.intCast α _ _ => some α
  | _ => none

private def isForbiddenParent (parent? : Option Expr) : Bool :=
  if let some parent := parent? then
    getType? parent |>.isSome
  else
    false

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).ring do return ()
  let some type := getType? e | return ()
  if isForbiddenParent parent? then return ()
  let some ringId ← getRingId? type | return ()
  let some re ← reify? e ringId | return ()
  trace[grind.ring.internalize] "[{ringId}]: {e}"
  markAsCommRingTerm e
  modifyRing ringId fun s => { s with denote := s.denote.insert { expr := e } re }

end Lean.Meta.Grind.Arith.CommRing
