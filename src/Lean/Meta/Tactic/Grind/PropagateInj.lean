/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Propagator
import Init.Grind.Injective
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Simp
namespace Lean.Meta.Grind

def getInvFor? (f : Expr) (a : Expr) : GoalM (Option (Expr × Expr)) := do
  let some info := (← get).inj.fns.find? { expr := f } | return none
  if let some inv := info.inv? then
    return some inv
  let [u, _] := info.us | unreachable!
  let nonEmpty := mkApp2 (mkConst ``Nonempty.intro [u]) info.α a
  let inv := mkApp5 (mkConst ``Grind.leftInv info.us) info.α info.β f info.h nonEmpty
  let inv ← preprocessLight inv
  let args := inv.getAppArgs
  let heq := mkAppN (mkConst ``Grind.leftInv_eq info.us) args
  let inv? := some (inv, heq)
  let info := { info with inv? }
  modify fun s => { s with inj.fns := s.inj.fns.insert { expr := f } info }
  return inv?

/--
If `e` is an application of the form `f a` where `f` is an injective function
in `(← get).inj.fns`, asserts `f⁻¹ (f a) = a`
-/
public def mkInjEq (e : Expr) : GoalM Unit := do
  let .app f a := e | return ()
  let some (inv, heq) ← getInvFor? f a | return ()
  let r ← preprocessAndInternalize (mkApp inv e) (← getGeneration e)
  let proof := mkApp heq a
  let proof ← match r.proof? with
    | some hp => mkEqTrans (← mkEqSymm hp) proof
    | none => pure proof
  trace[grind.inj.assert] "{r.expr}, {a}"
  pushEq r.expr a proof

def initInjFn (us : List Level) (α β : Expr) (f : Expr) (h : Expr) : GoalM Unit := do
  modify fun s => { s with inj.fns := s.inj.fns.insert { expr := f } { us, α, β, h } }
  let hidx := f.toHeadIndex
  for e in (← get).appMap.findD hidx [] do
    if e.isApp && isSameExpr e.appFn! f then
      mkInjEq e

builtin_grind_propagator propagateInj ↓Function.Injective := fun e => do
  let_expr i@Function.Injective α β f := e | return ()
  if (← isEqTrue e) then
    let f' := f.eta
    let f ← if isSameExpr f f' then
      pure f
    else
      let r ← preprocessAndInternalize f' (← getGeneration e)
      pure r.expr
    initInjFn i.constLevels! α β f (mkOfEqTrueCore e (← mkEqTrueProof e))

end Lean.Meta.Grind
