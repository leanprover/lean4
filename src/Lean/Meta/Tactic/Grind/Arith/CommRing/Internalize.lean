/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId

namespace Lean.Meta.Grind.Arith.CommRing

private inductive SupportedTermKind where
  | add | mul | num | sub | neg | pow
  deriving BEq

private def getKindAndType? (e : Expr) : Option (SupportedTermKind × Expr) :=
  match_expr e with
  | HAdd.hAdd α _ _ _ _ _ => some (.add, α)
  | HSub.hSub α _ _ _ _ _ => some (.sub, α)
  | HMul.hMul α _ _ _ _ _ => some (.mul, α)
  | HPow.hPow α β _ _ _ _ =>
    let_expr Nat := β | none
    some (.pow, α)
  | Neg.neg α _ a =>
    let_expr OfNat.ofNat _ _ _ := a | some (.neg, α)
    some (.num, α)
  | OfNat.ofNat α _ _ => some (.num, α)
  | _ => none

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).ring do return ()
  let some (kind, type) := getKindAndType? e | return ()
  let some ringId ← getRingId? type | return ()
  trace[grind.ring.internalize] "{e}, {ringId}, {parent?}"
  return ()

end Lean.Meta.Grind.Arith.CommRing
