/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
import Init.Simproc
public import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.MethodSpecs
import Lean.Meta.Tactic.Simp.Main

open Lean Meta Simp

def reduceMethod (opName : String) (e : Expr) : SimpM Simp.Step := do
  let xs := e.getAppArgsN 3
  let inst := xs[0]!
  let lhs := xs[1]!
  let rhs := xs[2]!
  unless inst.getAppFn.isConst do return .continue
  let some _ ← isConstructorApp? lhs | return .continue
  let some _ ← isConstructorApp? rhs | return .continue
  let some thms ← getMethodSpecTheorems inst.getAppFn.constName! opName | return .continue
  for thm in thms do
    let simpThms ← mkSimpTheoremFromConst thm
    assert! simpThms.size = 1
    if let some r ← Simp.tryTheorem? e simpThms[0]! then
      return .visit r
  return .continue

public section

/--
This simproc reduces `_ == _` when both arguments are constructor applications and the `BEq` instance
in question has been annotated with `@[method_specs]`.
-/
builtin_simproc_decl reduceBEq (_ == _) := fun e => do
  unless e.isAppOfArity ``BEq.beq 4 do return .continue
  reduceMethod "beq" e

/--
This simproc reduces `Ord.compare _ _` when both arguments are constructor applications and the
`Ord` instance in question has been annotated with `@[method_specs]`.
-/
builtin_simproc_decl reduceOrd (Ord.compare _ _) := fun e => do
  unless e.isAppOfArity ``Ord.compare 4 do return .continue
  reduceMethod "compare" e

end
