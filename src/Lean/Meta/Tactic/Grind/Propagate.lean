/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Grind.Proof

namespace Lean.Meta.Grind

/--
Propagates equalities for a conjunction `a ∧ b` based on the truth values
of its components `a` and `b`. This function checks the truth value of `a` and `b`,
and propagates the following equalities:

- If `a = True`, propagates `(a ∧ b) = b`.
- If `b = True`, propagates `(a ∧ b) = a`.
- If `a = False`, propagates `(a ∧ b) = False`.
- If `b = False`, propagates `(a ∧ b) = False`.
-/
private def propagateAndUp (e : Expr) : GoalM Unit := do
  let a := e.appFn!.appArg!
  let b := e.appArg!
  if (← isEqTrue a) then
    -- a = True → (a ∧ b) = b
    pushEq e b <| mkApp3 (mkConst ``Lean.Grind.and_eq_of_eq_true_left) a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    -- b = True → (a ∧ b) = a
    pushEq e a <| mkApp3 (mkConst ``Lean.Grind.and_eq_of_eq_true_right) a b (← mkEqTrueProof b)
  else if (← isEqFalse a) then
    -- a = False → (a ∧ b) = False
    pushEqFalse e <| mkApp3 (mkConst ``Lean.Grind.and_eq_of_eq_false_left) a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    -- b = False → (a ∧ b) = False
    pushEqFalse e <| mkApp3 (mkConst ``Lean.Grind.and_eq_of_eq_false_right) a b (← mkEqFalseProof b)

/--
Propagates truth values downwards for a conjunction `a ∧ b` when the
expression itself is known to be `True`.
-/
private def propagateAndDown (e : Expr) : GoalM Unit := do
  if (← isEqTrue e) then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let h ← mkEqTrueProof e
    pushEqTrue a <| mkApp3 (mkConst ``Lean.Grind.eq_true_of_and_eq_true_left) a b h
    pushEqTrue b <| mkApp3 (mkConst ``Lean.Grind.eq_true_of_and_eq_true_right) a b h

/--
Propagates equalities for a disjunction `a ∨ b` based on the truth values
of its components `a` and `b`. This function checks the truth value of `a` and `b`,
and propagates the following equalities:

- If `a = False`, propagates `(a ∨ b) = b`.
- If `b = False`, propagates `(a ∨ b) = a`.
- If `a = True`, propagates `(a ∨ b) = True`.
- If `b = True`, propagates `(a ∨ b) = True`.
-/
private def propagateOrUp (e : Expr) : GoalM Unit := do
  let a := e.appFn!.appArg!
  let b := e.appArg!
  if (← isEqFalse a) then
    -- a = False → (a ∨ b) = b
    pushEq e b <| mkApp3 (mkConst ``Lean.Grind.or_eq_of_eq_false_left) a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    -- b = False → (a ∨ b) = a
    pushEq e a <| mkApp3 (mkConst ``Lean.Grind.or_eq_of_eq_false_right) a b (← mkEqFalseProof b)
  else if (← isEqTrue a) then
    -- a = True → (a ∨ b) = True
    pushEqTrue e <| mkApp3 (mkConst ``Lean.Grind.or_eq_of_eq_true_left) a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    -- b = True → (a ∧ b) = True
    pushEqTrue e <| mkApp3 (mkConst ``Lean.Grind.or_eq_of_eq_true_right) a b (← mkEqTrueProof b)

/--
Propagates truth values downwards for a disjuction `a ∨ b` when the
expression itself is known to be `False`.
-/
private def propagateOrDown (e : Expr) : GoalM Unit := do
  if (← isEqFalse e) then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let h ← mkEqFalseProof e
    pushEqFalse a <| mkApp3 (mkConst ``Lean.Grind.eq_false_of_or_eq_false_left) a b h
    pushEqFalse b <| mkApp3 (mkConst ``Lean.Grind.eq_false_of_or_eq_false_right) a b h

/--
Propagates equalities for a negation `Not a` based on the truth value of `a`.
This function checks the truth value of `a` and propagates the following equalities:

- If `a = False`, propagates `(Not a) = True`.
- If `a = True`, propagates `(Not a) = False`.
-/
private def propagateNotUp (e : Expr) : GoalM Unit := do
  let a := e.appArg!
  if (← isEqFalse a) then
    -- a = False → (Not a) = True
    pushEqTrue e <| mkApp2 (mkConst ``Lean.Grind.not_eq_of_eq_false) a (← mkEqFalseProof a)
  else if (← isEqTrue a) then
    -- a = True → (Not a) = False
    pushEqFalse e <| mkApp2 (mkConst ``Lean.Grind.not_eq_of_eq_true) a (← mkEqTrueProof a)

/--
Propagates truth values downwards for a negation expression `Not a` based on the truth value of `Not a`.
This function performs the following:

- If `(Not a) = False`, propagates `a = True`.
- If `(Not a) = True`, propagates `a = False`.
-/
private def propagateNotDown (e : Expr) : GoalM Unit := do
  if (← isEqFalse e) then
    let a := e.appArg!
    pushEqTrue a <| mkApp2 (mkConst ``Lean.Grind.eq_true_of_not_eq_false) a (← mkEqFalseProof e)
  else if (← isEqTrue e) then
    let a := e.appArg!
    pushEqFalse a <| mkApp2 (mkConst ``Lean.Grind.eq_false_of_not_eq_true) a (← mkEqTrueProof e)

/-- Propagates `Eq` upwards -/
def propagateEqUp (e : Expr) : GoalM Unit := do
  let a := e.appFn!.appArg!
  let b := e.appArg!
  if (← isEqTrue a) then
    pushEq e b <| mkApp3 (mkConst ``Lean.Grind.eq_eq_of_eq_true_left) a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    pushEq e a <| mkApp3 (mkConst ``Lean.Grind.eq_eq_of_eq_true_right) a b (← mkEqTrueProof b)
  else if (← isEqv a b) then
    pushEqTrue e <| mkApp2 (mkConst ``of_eq_true) e (← mkEqProof a b)

/-- Propagates `Eq` downwards -/
def propagateEqDown (e : Expr) : GoalM Unit := do
  if (← isEqTrue e) then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    pushEq a b <| mkApp2 (mkConst ``of_eq_true) e (← mkEqTrueProof e)

/-- Propagates `HEq` downwards -/
def propagateHEqDown (e : Expr) : GoalM Unit := do
  if (← isEqTrue e) then
    let a := e.appFn!.appFn!.appArg!
    let b := e.appArg!
    pushHEq a b <| mkApp2 (mkConst ``of_eq_true) e (← mkEqTrueProof e)

/-- Propagates equalities upwards for logical connectives. -/
def propagateConectivesUp (e : Expr) : GoalM Unit := do
  let .const declName _ := e.getAppFn | return ()
  if declName == ``Eq && e.getAppNumArgs == 3 then
    propagateEqUp e
  else if declName == ``And && e.getAppNumArgs == 2 then
    propagateAndUp e
  else if declName == ``Or && e.getAppNumArgs == 2 then
    propagateOrUp e
  else if declName == ``Not && e.getAppNumArgs == 1 then
    propagateNotUp e
  -- TODO support for equality between Props

/-- Propagates equalities downwards for logical connectives. -/
def propagateConnectivesDown (e : Expr) : GoalM Unit := do
  let .const declName _ := e.getAppFn | return ()
  if declName == ``Eq && e.getAppNumArgs == 3 then
    propagateEqDown e
  else if declName == ``HEq && e.getAppNumArgs == 4 then
    propagateHEqDown e
  else if declName == ``And && e.getAppNumArgs == 2 then
    propagateAndDown e
  else if declName == ``Or && e.getAppNumArgs == 2 then
    propagateOrDown e
  else if declName == ``Not && e.getAppNumArgs == 1 then
    propagateNotDown e
  -- TODO support for `if-then-else`, equality between Props

end Lean.Meta.Grind
