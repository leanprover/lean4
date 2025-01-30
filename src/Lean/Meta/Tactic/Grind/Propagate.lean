/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind
import Lean.Meta.Tactic.Grind.Proof
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Ext
import Lean.Meta.Tactic.Grind.Internalize

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
builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And a b := e | return ()
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
builtin_grind_propagator propagateAndDown ↓And := fun e => do
  if (← isEqTrue e) then
    let_expr And a b := e | return ()
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
builtin_grind_propagator propagateOrUp ↑Or := fun e => do
  let_expr Or a b := e | return ()
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
builtin_grind_propagator propagateOrDown ↓Or := fun e => do
  if (← isEqFalse e) then
    let_expr Or a b := e | return ()
    let h ← mkEqFalseProof e
    pushEqFalse a <| mkApp3 (mkConst ``Lean.Grind.eq_false_of_or_eq_false_left) a b h
    pushEqFalse b <| mkApp3 (mkConst ``Lean.Grind.eq_false_of_or_eq_false_right) a b h

/--
Propagates equalities for a negation `Not a` based on the truth value of `a`.
This function checks the truth value of `a` and propagates the following equalities:

- If `a = False`, propagates `(Not a) = True`.
- If `a = True`, propagates `(Not a) = False`.
-/
builtin_grind_propagator propagateNotUp ↑Not := fun e => do
  let_expr Not a := e | return ()
  if (← isEqFalse a) then
    -- a = False → (Not a) = True
    pushEqTrue e <| mkApp2 (mkConst ``Lean.Grind.not_eq_of_eq_false) a (← mkEqFalseProof a)
  else if (← isEqTrue a) then
    -- a = True → (Not a) = False
    pushEqFalse e <| mkApp2 (mkConst ``Lean.Grind.not_eq_of_eq_true) a (← mkEqTrueProof a)
  else if (← isEqv e a) then
    closeGoal <| mkApp2 (mkConst ``Lean.Grind.false_of_not_eq_self) a (← mkEqProof e a)

/--
Propagates truth values downwards for a negation expression `Not a` based on the truth value of `Not a`.
This function performs the following:

- If `(Not a) = False`, propagates `a = True`.
- If `(Not a) = True`, propagates `a = False`.
-/
builtin_grind_propagator propagateNotDown ↓Not := fun e => do
  let_expr Not a := e | return ()
  if (← isEqFalse e) then
    pushEqTrue a <| mkApp2 (mkConst ``Lean.Grind.eq_true_of_not_eq_false) a (← mkEqFalseProof e)
  else if (← isEqTrue e) then
    pushEqFalse a <| mkApp2 (mkConst ``Lean.Grind.eq_false_of_not_eq_true) a (← mkEqTrueProof e)
  else if (← isEqv e a) then
    closeGoal <| mkApp2 (mkConst ``Lean.Grind.false_of_not_eq_self) a (← mkEqProof e a)

/-- Propagates `Eq` upwards -/
builtin_grind_propagator propagateEqUp ↑Eq := fun e => do
  let_expr Eq _ a b := e | return ()
  if (← isEqTrue a) then
    pushEq e b <| mkApp3 (mkConst ``Lean.Grind.eq_eq_of_eq_true_left) a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    pushEq e a <| mkApp3 (mkConst ``Lean.Grind.eq_eq_of_eq_true_right) a b (← mkEqTrueProof b)
  else if (← isEqv a b) then
    pushEqTrue e <| mkEqTrueCore e (← mkEqProof a b)
  let aRoot ← getRootENode a
  let bRoot ← getRootENode b
  if aRoot.ctor && bRoot.ctor && aRoot.self.getAppFn != bRoot.self.getAppFn then
    -- ¬a = b
    let hne ← withLocalDeclD `h (← mkEq a b) fun h => do
      let hf ← mkEqTrans (← mkEqProof aRoot.self a) h
      let hf ← mkEqTrans hf (← mkEqProof b bRoot.self)
      let hf ← mkNoConfusion (← getFalseExpr) hf
      mkLambdaFVars #[h] hf
    pushEqFalse e <| mkApp2 (mkConst ``eq_false) e hne

/-- Propagates `Eq` downwards -/
builtin_grind_propagator propagateEqDown ↓Eq := fun e => do
  if (← isEqTrue e) then
    let_expr Eq _ a b := e | return ()
    pushEq a b <| mkOfEqTrueCore e (← mkEqTrueProof e)
  else if (← isEqFalse e) then
    let_expr Eq α lhs rhs := e | return ()
    let thms ← getExtTheorems α
    if !thms.isEmpty then
      /-
      Heuristic for lists: If `lhs` or `rhs` are contructors we do not apply extensionality theorems.
      For example, we don't want to apply the extensionality theorem to things like `xs ≠ []`.
      TODO: polish this hackish heuristic later.
      -/
      if α.isAppOf ``List && ((← getRootENode lhs).ctor || (← getRootENode rhs).ctor) then
        return ()
      for thm in (← getExtTheorems α) do
        instantiateExtTheorem thm e

/-- Propagates `EqMatch` downwards -/
builtin_grind_propagator propagateEqMatchDown ↓Grind.EqMatch := fun e => do
  if (← isEqTrue e) then
    let_expr Grind.EqMatch _ a b origin := e | return ()
    markCaseSplitAsResolved origin
    pushEq a b <| mkOfEqTrueCore e (← mkEqTrueProof e)

/-- Propagates `HEq` downwards -/
builtin_grind_propagator propagateHEqDown ↓HEq := fun e => do
  if (← isEqTrue e) then
    let_expr HEq _ a _ b := e | return ()
    pushHEq a b <| mkOfEqTrueCore e (← mkEqTrueProof e)

/-- Propagates `HEq` upwards -/
builtin_grind_propagator propagateHEqUp ↑HEq := fun e => do
  let_expr HEq _ a _ b := e | return ()
  if (← isEqv a b) then
    pushEqTrue e <| mkEqTrueCore e (← mkHEqProof a b)

/-- Propagates `ite` upwards -/
builtin_grind_propagator propagateIte ↑ite := fun e => do
  let_expr f@ite α c h a b := e | return ()
  if (← isEqTrue c) then
    internalize a (← getGeneration e)
    pushEq e a <| mkApp6 (mkConst ``ite_cond_eq_true f.constLevels!) α c h a b (← mkEqTrueProof c)
  else if (← isEqFalse c) then
    internalize b (← getGeneration e)
    pushEq e b <| mkApp6 (mkConst ``ite_cond_eq_false f.constLevels!) α c h a b (← mkEqFalseProof c)

/-- Propagates `dite` upwards -/
builtin_grind_propagator propagateDIte ↑dite := fun e => do
  let_expr f@dite α c h a b := e | return ()
  if (← isEqTrue c) then
     let h₁ ← mkEqTrueProof c
     let ah₁ := mkApp a (mkOfEqTrueCore c h₁)
     let p ← simp ah₁
     let r := p.expr
     let h₂ ← p.getProof
     internalize r (← getGeneration e)
     pushEq e r <| mkApp8 (mkConst ``Grind.dite_cond_eq_true' f.constLevels!) α c h a b r h₁ h₂
  else if (← isEqFalse c) then
     let h₁ ← mkEqFalseProof c
     let bh₁ := mkApp b (mkApp2 (mkConst ``of_eq_false) c h₁)
     let p ← simp bh₁
     let r := p.expr
     let h₂ ← p.getProof
     internalize r (← getGeneration e)
     pushEq e r <| mkApp8 (mkConst ``Grind.dite_cond_eq_false' f.constLevels!) α c h a b r h₁ h₂

builtin_grind_propagator propagateDecideDown ↓decide := fun e => do
  let root ← getRootENode e
  unless root.ctor do return ()
  let_expr decide p h := e | return ()
  if root.self.isConstOf ``true then
    pushEqTrue p <| mkApp3 (mkConst ``Grind.of_decide_eq_true) p h (← mkEqProof e root.self)
  else if root.self.isConstOf ``false then
    pushEqFalse p <| mkApp3 (mkConst ``Grind.of_decide_eq_false) p h (← mkEqProof e root.self)

builtin_grind_propagator propagateDecideUp ↑decide := fun e => do
  let_expr decide p h := e | return ()
  if (← isEqTrue p) then
    pushEq e (← getBoolTrueExpr) <| mkApp3 (mkConst ``Grind.decide_eq_true) p h (← mkEqTrueProof p)
  else if (← isEqFalse p) then
    pushEq e (← getBoolFalseExpr) <| mkApp3 (mkConst ``Grind.decide_eq_false) p h (← mkEqFalseProof p)

end Lean.Meta.Grind
