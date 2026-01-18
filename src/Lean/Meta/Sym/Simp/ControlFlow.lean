/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.Simp.App
import Lean.Meta.SynthInstance
import Lean.Expr
import Init.Sym.Lemmas
namespace Lean.Meta.Sym.Simp
open Internal

def simpIte : Simproc := fun e => do
  let numArgs := e.getAppNumArgs
  if numArgs < 5 then return .rfl (done := true)
  propagateOverApplied e (numArgs - 5) fun e => do
    let_expr ite _ c _ a b := e | return .rfl
    match (← simp c) with
    | .rfl _ => return .rfl (done := true)
    | .step c' h _ =>
      if c'.isTrue then
        return .step a <| mkApp (e.replaceFn ``ite_cond_eq_true) h
      else if c'.isFalse then
        return .step b <| mkApp (e.replaceFn ``ite_cond_eq_false) h
      else
        let .some inst' ← trySynthInstance (mkApp (mkConst ``Decidable) c') | return .rfl
        let e' := e.getBoundedAppFn 4
        let e' ← mkAppS₄ e' c' inst' a b
        let h' := mkApp3 (e.replaceFn ``Lean.Sym.ite_cond_congr) c' inst' h
        return .step e' h' (done := true)

/--
Simplifies control-flow expressions such as `if-then-else` and `match` expressions.
It visits only the conditions and discriminants.
-/
public def simpControl : Simproc := fun e => do
  if !e.isApp then return .rfl
  let .const declName _ := e.getAppFn | return .rfl
  if declName == ``ite then
    simpIte e
  else
    -- **TODO**: Add more cases
    return .rfl

end Lean.Meta.Sym.Simp
