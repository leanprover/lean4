/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.CompatibleTypes

namespace Lean.Compiler.LCNF

/-!
# Note: Type compatibility checking for LCNF

We used to have a type compatibility relation `≃` for LCNF types.
It treated erased types/values as wildcards. Examples:
- `List Nat ≃ List ◾`
- `(List ◾ → List ◾) ≃ (List Nat → List Bool)`

We used this relation to sanity check compiler passes, and detect
buggy transformations that broke type compatibility. For example,
given an application `f a`, we would check whether `a`s type as
compatible with the type expected by `f`.

However, the type compatibility relation is not transitive. Example:
- `List Nat ≃ List ◾`, `List ◾ ≃ List String`, but `List Nat` and `List String` are **not** compatible.

We tried address the issue above by adding casts, which required us
to then add `cast` elimination simplifications, and generated a significant overhead in
the code generator.

Here is an example of transformation that would require the insertion of a cast operation.
```
def foo (g : List A → List A) (a : List B) :=
  fun f (x : List ◾) :=
    let _x.1 := g x
    ...
  let _x.2 := f a
  ...
```
The code above would not trigger any type compatibility issue, but
by inlining `f` without adding cast operations, we would get the
following type incorrect code.
```
def foo (g : List A → List A) (a : List B) :=
let _x.2 := g a -- Type error
...
```

We have considered using a reflexive and transitive subtype relation `≺`.
- `A ≺ A`
- `(Nat × Nat) ≺ (Nat × ◾) ≺ (◾ × ◾) ≺ ◾`
- `List Nat ≺ List ◾ ⊀ List String`
- `(List ◾ → List Nat) ≺ (List Bool → List ◾)`
Note that `A ≺ B` implies `A ≃ B`

The subtype relation has better properties, but also has problems.
First, when converting to LCNF we would have to add more casts. Example:
the function takes a `List ◾`, but the value has type `◾`.
Moreover, recall that `(List Nat → List Nat) ⊀ (◾ → ◾)` forcing us
to add many casts operations when moving to the mono phase where
we erase type parameters.

Recall that type compatibility and subtype relationships do not help with memory layout.
We have that `(UInt32 × UInt32) ≺ (◾ × ◾) ≺ ◾` but elements of these types have
different runtime representation.

Thus, we have decided to abandon the type compatibility checks and cast operations
in LCNF. The only drawback is that we lose the capability of catching simple bugs
at compiler passes.

In the future, we can try to add a sanity check flag that instructs the compiler to use
the subtype relation in sanity checks and add the necessary casts.

-/

namespace Check
open InferType

/-
Type and structural properties checker for LCNF expressions.
-/

structure Context where
  /-- Join points that are in scope. -/
  jps : FVarIdSet := {}
  /-- Variables and local functions in scope -/
  vars : FVarIdSet := {}

structure State where
  /-- All free variables found -/
  all : FVarIdHashSet := {}

abbrev CheckM := ReaderT Context $ StateRefT State InferTypeM

def checkTypes : CheckM Bool := do
  return (← getConfig).checkTypes

def checkFVar (fvarId : FVarId) : CheckM Unit :=
  unless (← read).vars.contains fvarId do
    throwError "invalid out of scope free variable {← getBinderName fvarId}"

/-- Return true `f` is a constructor and `i` is less than its number of parameters. -/
def isCtorParam (f : Expr) (i : Nat) : CoreM Bool := do
  let .const declName _ := f | return false
  let .ctorInfo info ← getConstInfo declName | return false
  return i < info.numParams

def checkAppArgs (f : Expr) (args : Array Arg) : CheckM Unit := do
  let mut fType ← inferType f
  let mut j := 0
  for h : i in [:args.size] do
    let arg := args[i]
    if fType.isErased then
      return ()
    fType := fType.headBeta
    let (d, b) ←
      match fType with
      | .forallE _ d b _ => pure (d, b)
      | _ =>
        fType := instantiateRevRangeArgs fType j i args |>.headBeta
        match fType with
        | .forallE _ d b _ => j := i; pure (d, b)
        | _ => return ()
    let expectedType := instantiateRevRangeArgs d j i args
    if (← checkTypes) then
      let argType ← arg.inferType
      unless (← InferType.compatibleTypes argType expectedType) do
        throwError "type mismatch at LCNF application{indentExpr (mkAppN f (args.map Arg.toExpr))}\nargument {arg.toExpr} has type{indentExpr argType}\nbut is expected to have type{indentExpr expectedType}"
    unless (← pure (maybeTypeFormerType expectedType) <||> isErasedCompatible expectedType) do
      match arg with
      | .fvar fvarId => checkFVar fvarId
      | .erased => pure ()
      | .type _ =>
        -- Constructor parameters that are not type formers are erased at phase .mono
        unless (← getPhase) ≥ .mono && (← isCtorParam f i) do
          throwError "invalid LCNF application{indentExpr (mkAppN f (args.map (·.toExpr)))}\nargument{indentExpr arg.toExpr}\nhas type{indentExpr expectedType}\nmust be a free variable"
    fType := b

def checkLetValue (e : LetValue) : CheckM Unit := do
  match e with
  | .value .. | .erased => pure ()
  | .const declName us args => checkAppArgs (mkConst declName us) args
  | .fvar fvarId args => checkFVar fvarId; checkAppArgs (.fvar fvarId) args
  | .proj _ _ fvarId => checkFVar fvarId

def checkJpInScope (jp : FVarId) : CheckM Unit := do
  unless (← read).jps.contains jp do
    /-
    We cannot jump to join points defined out of the scope of a local function declaration.
    For example, the following is an invalid LCNF.
    ```
    jp_1 := fun x => ... -- Some join point
    let f := fun y => -- Local function declaration.
      ...
      jp_1 _x.n -- jump to a join point that is not in the scope of `f`.
    ```
    -/
    throwError "invalid jump to out of scope join point `{mkFVar jp}`"

def checkParam (param : Param) : CheckM Unit := do
  unless param == (← getParam param.fvarId) do
    throwError "LCNF parameter mismatch at `{param.binderName}`, does not value in local context"

def checkParams (params : Array Param) : CheckM Unit :=
  params.forM checkParam

def checkLetDecl (letDecl : LetDecl) : CheckM Unit := do
  checkLetValue letDecl.value
  if (← checkTypes) then
    let valueType ← letDecl.value.inferType
    unless (← InferType.compatibleTypes letDecl.type valueType) do
      throwError "type mismatch at `{letDecl.binderName}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr letDecl.type}"
  unless letDecl == (← getLetDecl letDecl.fvarId) do
    throwError "LCNF let declaration mismatch at `{letDecl.binderName}`, does not match value in local context"

def addFVarId (fvarId : FVarId) : CheckM Unit := do
  if (← get).all.contains fvarId then
    throwError "invalid LCNF, free variables are not unique `{fvarId.name}`"
  modify fun s => { s with all := s.all.insert fvarId }

@[inline] def withFVarId (fvarId : FVarId) (x : CheckM α) : CheckM α := do
  addFVarId fvarId
  withReader (fun ctx => { ctx with vars := ctx.vars.insert fvarId }) x

@[inline] def withJp (fvarId : FVarId) (x : CheckM α) : CheckM α := do
  addFVarId fvarId
  withReader (fun ctx => { ctx with jps := ctx.jps.insert fvarId }) x

@[inline] def withParams (params : Array Param) (x : CheckM α) : CheckM α := do
  params.forM (addFVarId ·.fvarId)
  withReader (fun ctx => { ctx with vars := params.foldl (init := ctx.vars) fun vars p => vars.insert p.fvarId })
    x

mutual

set_option linter.all false

partial def checkFunDeclCore (declName : Name) (params : Array Param) (type : Expr) (value : Code) : CheckM Unit := do
  checkParams params
  withParams params do
    discard <| check value
    if (← checkTypes) then
      let valueType ← mkForallParams params (← value.inferType)
      unless (← InferType.compatibleTypes type valueType) do
        throwError "type mismatch at `{declName}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr type}"

partial def checkFunDecl (funDecl : FunDecl) : CheckM Unit := do
  checkFunDeclCore funDecl.binderName funDecl.params funDecl.type funDecl.value
  let decl ← getFunDecl funDecl.fvarId
  unless decl.binderName == funDecl.binderName do
    throwError "LCNF local function declaration mismatch at `{funDecl.binderName}`, binder name in local context `{decl.binderName}`"
  unless decl.type == funDecl.type do
    throwError "LCNF local function declaration mismatch at `{funDecl.binderName}`, type in local context{indentExpr decl.type}\nexpected{indentExpr funDecl.type}"
  unless (← getFunDecl funDecl.fvarId) == funDecl do
    throwError "LCNF local function declaration mismatch at `{funDecl.binderName}`, declaration in local context does match"

partial def checkCases (c : Cases) : CheckM Unit := do
  let mut ctorNames : NameSet := {}
  let mut hasDefault := false
  checkFVar c.discr
  for alt in c.alts do
    match alt with
    | .default k => hasDefault := true; check k
    | .alt ctorName params k =>
      checkParams params
      if ctorNames.contains ctorName then
        throwError "invalid LCNF `cases`, alternative `{ctorName}` occurs more than once"
      ctorNames := ctorNames.insert ctorName
      let .ctorInfo val ← getConstInfo ctorName | throwError "invalid LCNF `cases`, `{ctorName}` is not a constructor name"
      unless val.induct == c.typeName do
        throwError "invalid LCNF `cases`, `{ctorName}` is not a constructor of `{c.typeName}`"
      unless params.size == val.numFields do
        throwError "invalid LCNF `cases`, `{ctorName}` has # {val.numFields} fields, but alternative has # {params.size} alternatives"
      withParams params do check k

partial def check (code : Code) : CheckM Unit := do
  match code with
  | .let decl k => checkLetDecl decl; withFVarId decl.fvarId do check k
  | .fun decl k =>
    -- Remark: local function declarations should not jump to out of scope join points
    withReader (fun ctx => { ctx with jps := {} }) do checkFunDecl decl
    withFVarId decl.fvarId do check k
  | .jp decl k => checkFunDecl decl; withJp decl.fvarId do check k
  | .cases c => checkCases c
  | .jmp fvarId args =>
    checkJpInScope fvarId
    let decl ← getFunDecl fvarId
    unless decl.getArity == args.size do
      throwError "invalid LCNF `goto`, join point {decl.binderName} has #{decl.getArity} parameters, but #{args.size} were provided"
    checkAppArgs (.fvar fvarId) args
  | .return fvarId => checkFVar fvarId
  | .unreach .. => pure ()

end

def run (x : CheckM α) : CompilerM α :=
  x |>.run {} |>.run' {} |>.run {}

end Check

def Decl.check (decl : Decl) : CompilerM Unit := do
  Check.run do Check.checkFunDeclCore decl.name decl.params decl.type decl.value

/--
Check whether every local declaration in the local context is used in one of given `decls`.
-/
partial def checkDeadLocalDecls (decls : Array Decl) : CompilerM Unit := do
  let (_, s) := visitDecls decls |>.run {}
  let usesFVar (binderName : Name) (fvarId : FVarId) :=
    unless s.contains fvarId do
      throwError "LCNF local context contains unused local variable declaration `{binderName}`"
  let lctx := (← get).lctx
  lctx.params.forM fun fvarId decl => usesFVar decl.binderName fvarId
  lctx.letDecls.forM fun fvarId decl => usesFVar decl.binderName fvarId
  lctx.funDecls.forM fun fvarId decl => usesFVar decl.binderName fvarId
where
  visitFVar (fvarId : FVarId) : StateM FVarIdHashSet Unit :=
    modify (·.insert fvarId)

  visitParam (param : Param) : StateM FVarIdHashSet Unit := do
    visitFVar param.fvarId

  visitParams (params : Array Param) : StateM FVarIdHashSet Unit := do
    params.forM visitParam

  visitCode (code : Code) : StateM FVarIdHashSet Unit := do
    match code with
    | .jmp .. | .return .. | .unreach .. => return ()
    | .let decl k => visitFVar decl.fvarId; visitCode k
    | .fun decl k | .jp decl k =>
      visitFVar decl.fvarId; visitParams decl.params; visitCode decl.value
      visitCode k
    | .cases c => c.alts.forM fun alt => do
      match alt with
      | .default k => visitCode k
      | .alt _ ps k => visitParams ps; visitCode k

  visitDecl (decl : Decl) : StateM FVarIdHashSet Unit := do
    visitParams decl.params
    visitCode decl.value

  visitDecls (decls : Array Decl) : StateM FVarIdHashSet Unit :=
    decls.forM visitDecl

end Lean.Compiler.LCNF
