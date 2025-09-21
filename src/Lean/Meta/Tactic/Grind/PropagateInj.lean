/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Injective
import Lean.Meta.Tactic.Grind.Proof
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Injective
namespace Lean.Meta.Grind
/--
If `e` is an application of the form `f a` where `f` is an injective function
in `(← get).inj.fns`, asserts `f⁻¹ (f a) = a`
-/
public def mkInjEq (e : Expr) : GoalM Unit := do
  let .app f a := e | return ()
  let some info := (← get).inj.fns.find? { expr := f } | return ()
  let invApp := mkApp info.inv e
  internalize invApp (← getGeneration e)
  trace[grind.inj.assert] "{invApp}, {a}"
  pushEq invApp a <| mkApp info.heq a

def initInjFn (us : List Level) (α β : Expr) (f : Expr) (h : Expr) : GoalM Unit := do
  let hidx := f.toHeadIndex
  let mut first := true
  for e in (← get).appMap.findD hidx [] do
    if e.isApp && isSameExpr e.appFn! f then
      if first then
        initLeftInv e.appArg!
        first := false
      mkInjEq e
where
  initLeftInv (a : Expr) : GoalM Unit := do
    let [u, _] := us | unreachable!
    let nonEmpty := mkApp2 (mkConst ``Nonempty.intro [u]) α a
    let inv := mkApp5 (mkConst ``Grind.leftInv us) α β f h nonEmpty
    let inv ← preprocessLight inv
    let args := inv.getAppArgs
    let heq := mkAppN (mkConst ``Grind.leftInv_eq us) args
    modify fun s => { s with inj.fns := s.inj.fns.insert { expr := f } { inv, heq } }

builtin_grind_propagator propagateInj ↓Function.Injective := fun e => do
  let_expr i@Function.Injective α β f := e | return ()
  if (← isEqTrue e) then
    let f' := f.eta
    let f ← if isSameExpr f f' then
      pure f
    else
      let f' ← preprocessLight f'
      internalize f' (← getGeneration e)
      pure f'
    initInjFn i.constLevels! α β f (mkOfEqTrueCore e (← mkEqTrueProof e))

end Lean.Meta.Grind
