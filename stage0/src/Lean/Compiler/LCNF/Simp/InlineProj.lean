/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Simp.SimpM

namespace Lean.Compiler.LCNF
namespace Simp

/--
Auxiliary function for projecting "type class dictionary access".
That is, we are trying to extract one of the type class instance elements.
Remark: We do not consider parent instances to be elements.
For example, suppose `e` is `_x_4.1`, and we have
```
_x_2 : Monad (ReaderT Bool (ExceptT String Id)) := @ReaderT.Monad Bool (ExceptT String Id) _x_1
_x_3 : Applicative (ReaderT Bool (ExceptT String Id)) := _x_2.1
_x_4 : Functor (ReaderT Bool (ExceptT String Id)) := _x_3.1
```
Then, we will expand `_x_4.1` since it corresponds to the `Functor` `map` element,
and its type is not a type class, but is of the form
```
{α β : Type u} → (α → β) → ...
```
In the example above, the compiler should not expand `_x_3.1` or `_x_2.1` because they are
type class applications: `Functor` and `Applicative` respectively.
By eagerly expanding them, we may produce inefficient and bloated code.
For example, we may be using `_x_3.1` to invoke a function that expects a `Functor` instance.
By expanding `_x_3.1` we will be just expanding the code that creates this instance.

The result is representing a sequence of code containing let-declarations and local function declarations (`Array CodeDecl`)
and the free variable containing the result (`FVarId`). The resulting `FVarId` often depends only on a small
subset of `Array CodeDecl`. However, this method does try to filter the relevant ones.
We rely on the `used` var set available in `SimpM` to filter them. See `attachCodeDecls`.
-/
partial def inlineProjInst? (e : LetValue) : SimpM (Option (Array CodeDecl × FVarId)) := do
  let .proj _ i s := e | return none
  let sType ← getType s
  unless (← isClass? sType).isSome do return none
  let eType ← e.inferType
  unless  (← isClass? eType).isNone do return none
  let (fvarId?, decls) ← visit s [i] |>.run |>.run #[]
  if let some fvarId := fvarId? then
    return some (decls, fvarId)
  else
    eraseCodeDecls decls
    return none
where
  visit (fvarId : FVarId) (projs : List Nat) : OptionT (StateRefT (Array CodeDecl) SimpM) FVarId := do
    let some letDecl ← findLetDecl? fvarId | failure
    match letDecl.value with
    | .proj _ i s => visit s (i :: projs)
    | .fvar .. | .value .. | .erased => failure
    | .const declName us args =>
      if let some (.ctorInfo ctorVal) := (← getEnv).find? declName then
        let i :: projs := projs | unreachable!
        let arg := args[ctorVal.numParams + i]!
        let fvarId ← match arg with
          | .fvar fvarId => pure fvarId
          | .erased | .type .. =>
            let auxDecl ← mkLetDeclErased
            modify (·.push (.let auxDecl))
            pure auxDecl.fvarId
        if projs.isEmpty then
          return fvarId
        else
          visit fvarId projs
      else
        let some decl ← getDecl? declName | failure
        guard (decl.getArity == args.size)
        let params := decl.instantiateParamsLevelParams us
        let code := decl.instantiateValueLevelParams us
        let code ← betaReduce params code args (mustInline := true)
        visitCode code projs

  visitCode (code : Code) (projs : List Nat) : OptionT (StateRefT (Array CodeDecl) SimpM) FVarId := do
    match code with
    | .let decl k => modify (·.push (.let decl)); visitCode k projs
    | .fun decl k => modify (·.push (.fun decl)); visitCode k projs
    | .return fvarId => visit fvarId projs
    | _ => eraseCode code; failure
