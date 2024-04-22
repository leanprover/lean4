/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro, Leonardo de Moura
-/
prelude
import Lean.Attributes
import Lean.ScopedEnvExtension
import Lean.Meta.FunInfo

/-!
# The `@[coe]` attribute, used to delaborate coercion functions as `↑`

When writing a coercion, if the pattern
```
@[coe]
def A.toB (a : A) : B := sorry

instance : Coe A B where coe := A.toB
```
is used, then `A.toB a` will be pretty-printed as `↑a`.
-/

namespace Lean.Meta

/-- The different types of coercions that are supported by the `coe` attribute. -/
inductive CoeFnType
  /-- The basic coercion `↑x`, see `CoeT.coe` -/
  | coe
  /-- The coercion to a function type, see `CoeFun.coe` -/
  | coeFun
  /-- The coercion to a type, see `CoeSort.coe` -/
  | coeSort
  deriving Inhabited, Repr, DecidableEq

instance : ToExpr CoeFnType where
  toTypeExpr := mkConst ``CoeFnType
  toExpr := open CoeFnType in fun
    | coe => mkConst ``coe
    | coeFun => mkConst ``coeFun
    | coeSort => mkConst ``coeSort

/-- Information associated to a coercion function to enable sensible delaboration. -/
structure CoeFnInfo where
  /-- The number of arguments to the coercion function -/
  numArgs : Nat
  /-- The argument index that represents the value being coerced -/
  coercee : Nat
  /-- The type of coercion -/
  type : CoeFnType
  deriving Inhabited, Repr

instance : ToExpr CoeFnInfo where
  toTypeExpr := mkConst ``CoeFnInfo
  toExpr | ⟨a, b, c⟩ => mkApp3 (mkConst ``CoeFnInfo.mk) (toExpr a) (toExpr b) (toExpr c)

/-- The environment extension for tracking coercion functions for delaboration -/
-- TODO: does it need to be a scoped extension
initialize coeExt : SimpleScopedEnvExtension (Name × CoeFnInfo) (NameMap CoeFnInfo) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun st (n, i) => st.insert n i
    initial := {}
  }

/-- Lookup the coercion information for a given function -/
def getCoeFnInfo? (fn : Name) : CoreM (Option CoeFnInfo) :=
  return (coeExt.getState (← getEnv)).find? fn

/-- Add `name` to the coercion extension and add a coercion delaborator for the function. -/
def registerCoercion (name : Name) (info : Option CoeFnInfo := none) : MetaM Unit := do
  let info ← match info with | some info => pure info | none => do
    let fnInfo ← getFunInfo (← mkConstWithLevelParams name)
    let some coercee := fnInfo.paramInfo.findIdx? (·.binderInfo.isExplicit)
      | throwError "{name} has no explicit arguments"
    pure { numArgs := coercee + 1, coercee, type := .coe }
  modifyEnv fun env => coeExt.addEntry env (name, info)

builtin_initialize registerBuiltinAttribute {
  name := `coe
  descr := "Adds a definition as a coercion"
  add := fun decl _stx kind => MetaM.run' do
    unless kind == .global do
      throwError "cannot add local or scoped coe attribute"
    registerCoercion decl
}

end Lean.Meta
