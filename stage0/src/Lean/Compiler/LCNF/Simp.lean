/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Recognizers
import Lean.Meta.Instances
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.ElimDead
import Lean.Compiler.LCNF.Bind
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.Stage1
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.AlphaEqv

namespace Lean.Compiler.LCNF

/--
Return `true` if the arrow type contains an instance implicit argument.
-/
def hasLocalInst (type : Expr) : Bool :=
  match type with
  | .forallE _ _ b bi => bi.isInstImplicit || hasLocalInst b
  | _ => false

/--
Return `true` if `decl` is supposed to be inlined/specialized.
-/
def isTemplateLike (decl : Decl) : CoreM Bool := do
  if hasLocalInst decl.type then
    return true -- `decl` applications will be specialized
  else if (← Meta.isInstance decl.name) then
    return true -- `decl` is "fuel" for code specialization
  else if hasInlineAttribute (← getEnv) decl.name || hasSpecializeAttribute (← getEnv) decl.name then
    return true -- `decl` is going to be inlined or specialized
  else
    return false

namespace Simp

/--
Local function usage information used to decide whether it should be inlined or not.
The information is an approximation, but it is on the "safe" side. That is, if we tagged
a function with `.once`, then it is applied only once. A local function may be marked as
`.many`, but after simplifications the number of applications may reduce to 1. This is not
a big problem in practice because we run the simplifier multiple times, and this information
is recomputed from scratch at the beginning of each simplification step.
-/
inductive FunDeclInfo where
  /--
  Local function is applied once, and must be inlined.
  -/
  | once
  /--
  Local function is applied many times, and will only be inlined
  if it is small.
  -/
  | many
  /--
  Function must be inlined.
  -/
  | mustInline
  deriving Repr, Inhabited

/--
Local function declaration statistics.
-/
structure FunDeclInfoMap where
  /--
  Mapping from local function name to inlining information.
  -/
  map : Std.HashMap FVarId FunDeclInfo := {}
  deriving Inhabited

def FunDeclInfoMap.format (s : FunDeclInfoMap) : CompilerM Format := do
  let mut result := Format.nil
  for (fvarId, info) in s.map.toList do
    let binderName ← getBinderName fvarId
    result := result ++ "\n" ++ f!"{binderName} ↦ {repr info}"
  return result

/--
Add new occurrence for the local function with binder name `key`.
-/
def FunDeclInfoMap.add (s : FunDeclInfoMap) (fvarId : FVarId) : FunDeclInfoMap :=
  match s with
  | { map } =>
    match map.find? fvarId with
    | some .once => { map := map.insert fvarId .many }
    | none       => { map := map.insert fvarId .once }
    | _          => { map }

/--
Add new occurrence for the local function with binder name `key`.
-/
def FunDeclInfoMap.addMustInline (s : FunDeclInfoMap) (fvarId : FVarId) : FunDeclInfoMap :=
  match s with
  | { map } => { map := map.insert fvarId .mustInline }

def FunDeclInfoMap.restore (s : FunDeclInfoMap) (fvarId : FVarId) (saved? : Option FunDeclInfo) : FunDeclInfoMap :=
  match s, saved? with
  | { map }, none => { map := map.erase fvarId }
  | { map }, some saved => { map := map.insert fvarId saved }

partial def findFunDecl? (e : Expr) : CompilerM (Option FunDecl) := do
  match e with
  | .fvar fvarId =>
    if let some decl ← LCNF.findFunDecl? fvarId then
      return some decl
    else if let some decl ← findLetDecl? fvarId then
      findFunDecl? decl.value
    else
      return none
  | .mdata _ e => findFunDecl? e
  | _ => return none

partial def findExpr (e : Expr) (skipMData := true) : CompilerM Expr := do
  match e with
  | .fvar fvarId =>
    let some decl ← findLetDecl? fvarId | return e
    findExpr decl.value
  | .mdata _ e' => if skipMData then findExpr e' else return e
  | _ => return e

structure Config where
  /--
  Any local function declaration or join point with size `≤ smallThresold` is inlined
  even if there are multiple occurrences.
  We currently don't do the same for global declarations because we are not saving
  the stage1 compilation result in .olean files yet.
  -/
  smallThreshold : Nat := 1
  /--
  If `etaPoly` is true, we eta expand any global function application when
  the function takes local instances. The idea is that we do not generate code
  for this kind of application, and we want all of them to specialized or inlined.
  -/
  etaPoly : Bool := false
  /--
  If `inlinePartial` is `true`, we inline partial function applications tagged
  with `[inline]`. Note that this option is automatically disabled when processing
  declarations tagged with `[inline]`, marked to be specialized, or instances.
  -/
  inlinePartial := false
  /--
  If `implementedBy` is `true`, we apply the `implementedBy` replacements.
  Remark: we only apply `casesOn` replacements at phase 2 because `cases` constructor
  may not have enough information for reconstructing the original `casesOn` application at
  phase 1.
  -/
  implementedBy := false
  deriving Inhabited

structure Context where
  /--
  Name of the declaration being simplified.
  We currently use this information because we are generating phase1 declarations  on demand,
  and it may trigger non-termination when trying to access the phase1 declaration.
  -/
  declName : Name
  config : Config := {}
  discrCtorMap : FVarIdMap Expr := {}

structure State where
  /--
  Free variable substitution. We use it to implement inlining and removing redundant variables `let _x.i := _x.j`
  -/
  subst : FVarSubst := {}
  /--
  Track used local declarations to be able to eliminate dead variables.
  -/
  used : UsedLocalDecls := {}
  /--
  Mapping used to decide whether a local function declaration must be inlined or not.
  -/
  funDeclInfoMap : FunDeclInfoMap := {}
  /--
  `true` if some simplification was performed in the current simplification pass.
  -/
  simplified : Bool := false
  /--
  Number of visited `let-declarations` and terminal values.
  This is a performance counter, and currently has no impact on code generation.
  -/
  visited : Nat := 0
  /--
  Number of definitions inlined.
  This is a performance counter.
  -/
  inline : Nat := 0
  /--
  Number of local functions inlined.
  This is a performance counter.
  -/
  inlineLocal : Nat := 0

abbrev SimpM := ReaderT Context $ StateRefT State CompilerM

instance : MonadFVarSubst SimpM where
  getSubst := return (← get).subst

/--
Use `findExpr`, and if the result is a free variable, check whether it is in the map `discrCtorMap`.
We use this method when simplifying projections and cases-constructor.
-/
def findCtor (e : Expr) : SimpM Expr := do
  let e ← findExpr e
  let .fvar fvarId := e | return e
  let some ctor := (← read).discrCtorMap.find? fvarId | return e
  return ctor

/--
Execute `x` with the information that `discr = ctorName ctorFields`.
We use this information to simplify nested cases on the same discriminant.

Remark: we do not perform the reverse direction at this phase.
That is, we do not replace occurrences of `ctorName ctorFields` with `discr`.
We wait more type information to be erased.
-/
def withDiscrCtor (discr : FVarId) (ctorName : Name) (ctorFields : Array Param) (x : SimpM α) : SimpM α := do
  let ctorInfo ← getConstInfoCtor ctorName
  let mut ctor := mkConst ctorName
  for _ in [:ctorInfo.numParams] do
    ctor := .app ctor erasedExpr -- the parameters are irrelevant for optimizations that use this information
  for field in ctorFields do
    ctor := .app ctor (.fvar field.fvarId)
  withReader (fun ctx => { ctx with discrCtorMap := ctx.discrCtorMap.insert discr ctor }) do
    x

/-- Set the `simplified` flag to `true`. -/
def markSimplified : SimpM Unit :=
  modify fun s => { s with simplified := true }

/-- Increment `visited` performance counter. -/
def incVisited : SimpM Unit :=
  modify fun s => { s with visited := s.visited + 1 }

/-- Increment `inline` performance counter. It is the number of inlined global declarations. -/
def incInline : SimpM Unit :=
  modify fun s => { s with inline := s.inline + 1 }

/-- Increment `inlineLocal` performance counter. It is the number of inlined local function and join point declarations. -/
def incInlineLocal : SimpM Unit :=
  modify fun s => { s with inlineLocal := s.inlineLocal + 1 }

/-- Mark the local function declaration or join point with the given id as a "must inline". -/
def addMustInline (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.addMustInline fvarId }

/-- Add a new occurrence of local function `fvarId`. -/
def addFunOcc (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.add fvarId }

/--
Traverse `code` and update function occurrence map.
This map is used to decide whether we inline local functions or not.
If `mustInline := true`, then all local function declarations occurring in
`code` are tagged as `.mustInline`.
Recall that we use `.mustInline` for local function declarations occurring in type class instances.
-/
partial def updateFunDeclInfo (code : Code) (mustInline := false) : SimpM Unit :=
  go code
where
  go (code : Code) : SimpM Unit := do
  match code with
  | .let decl k =>
    if decl.value.isApp then
      if let some funDecl ← findFunDecl? decl.value.getAppFn then
        addFunOcc funDecl.fvarId
    go k
  | .fun decl k =>
    if mustInline then
      addMustInline decl.fvarId
    go decl.value; go k
  | .jp decl k => go decl.value; go k
  | .cases c => c.alts.forM fun alt => go alt.getCode
  | .jmp fvarId .. =>
    let funDecl ← getFunDecl fvarId
    addFunOcc funDecl.fvarId
  | .return .. | .unreach .. => return ()

/--
Execute `x` with `fvarId` set as `mustInline`.
After execution the original setting is restored.
-/
def withAddMustInline (fvarId : FVarId) (x : SimpM α) : SimpM α := do
  let saved? := (← get).funDeclInfoMap.map.find? fvarId
  try
    addMustInline fvarId
    x
  finally
    modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.restore fvarId saved? }

/--
Return true if the given local function declaration or join point id is marked as
`once` or `mustInline`. We use this information to decide whether to inline them.
-/
def isOnceOrMustInline (fvarId : FVarId) : SimpM Bool := do
  match (← get).funDeclInfoMap.map.find? fvarId with
    | some .once | some .mustInline  => return true
    | _ => return false

/--
Return `true` if the given local function declaration is considered "small".
-/
def isSmall (decl : FunDecl) : SimpM Bool :=
  return decl.value.sizeLe (← read).config.smallThreshold

/--
Return `true` if the given local function declaration should be inlined.
-/
def shouldInlineLocal (decl : FunDecl) : SimpM Bool := do
  if (← isOnceOrMustInline decl.fvarId) then
    return true
  else
    isSmall decl

/--
Result of `inlineCandidate?`.
It contains information for inlining local and global functions.
-/
structure InlineCandidateInfo where
  isLocal : Bool
  params  : Array Param
  /-- Value (lambda expression) of the function to be inlined. -/
  value   : Code
  f       : Expr
  args    : Array Expr

/-- The arity (aka number of parameters) of the function to be inlined. -/
def InlineCandidateInfo.arity : InlineCandidateInfo → Nat
  | { params, .. } => params.size

/--
Return `some i` if `decl` is of the form
```
def f (a_0 ... a_i ...) :=
  ...
  cases a_i
  | ...
  | ...
```
That is, `f` is a sequence of declarations followed by a `cases` on the parameter `i`.
We use this function to decide whether we should inline a declaration tagged with
`[inlineIfReduce]` or not.
-/
def isCasesOnParam? (decl : Decl) : Option Nat :=
  go decl.value
where
  go (code : Code) : Option Nat :=
    match code with
    | .let _ k | .jp _ k | .fun _ k => go k
    | .cases c => decl.params.findIdx? fun param => param.fvarId == c.discr
    | _ => none

/--
Return `some info` if `e` should be inlined.
-/
def inlineCandidate? (e : Expr) : SimpM (Option InlineCandidateInfo) := do
  let mut e := e
  let mut mustInline := false
  if e.isAppOfArity ``inline 2 then
    e ← findExpr e.appArg!
    mustInline := true
  let numArgs := e.getAppNumArgs
  let f := e.getAppFn
  if let .const declName us ← findExpr f then
    if declName == (← read).declName then return none -- TODO: remove after we start storing phase1 code in .olean files
    let inlineIfReduce := hasInlineIfReduceAttribute (← getEnv) declName
    unless mustInline || hasInlineAttribute (← getEnv) declName || inlineIfReduce do return none
    -- TODO: check whether function is recursive or not.
    -- We can skip the test and store function inline so far.
    let some decl ← getStage1Decl? declName | return none
    let arity := decl.getArity
    let inlinePartial := (← read).config.inlinePartial
    if !mustInline && !inlinePartial && numArgs < arity then return none
    if inlineIfReduce then
      let some paramIdx := isCasesOnParam? decl | return none
      unless paramIdx < numArgs do return none
      let arg ← findCtor (e.getArg! paramIdx)
      unless arg.isConstructorApp (← getEnv) do return none
    let params := decl.instantiateParamsLevelParams us
    let value := decl.instantiateValueLevelParams us
    incInline
    return some {
      isLocal := false
      f       := e.getAppFn
      args    := e.getAppArgs
      params, value
    }
  else if let some decl ← findFunDecl? f then
    unless numArgs > 0 do return none -- It is not worth to inline a local function that does not take any arguments
    unless mustInline || (← shouldInlineLocal decl) do return none
    -- Remark: we inline local function declarations even if they are partial applied
    incInlineLocal
    modify fun s => { s with inlineLocal := s.inlineLocal + 1 }
    return some {
      isLocal := true
      f       := e.getAppFn
      args    := e.getAppArgs
      params  := decl.params
      value   := decl.value
    }
  else
    return none

/--
Add substitution `fvarId ↦ val`. `val` is a free variable, or
it is a type, type former, or `lcErased`.
-/
def addSubst (fvarId : FVarId) (val : Expr) : SimpM Unit :=
  modify fun s => { s with subst := s.subst.insert fvarId val }

/--
Return `true` if `c` has only one exit point.
This is a quick approximation. It does not check cases
such as: a `cases` with many but only one alternative is not reachable.
It is only used to avoid the creation of auxiliary join points, and does not need
to be precise.
-/
private partial def oneExitPointQuick (c : Code) : Bool :=
  go c
where
  go (c : Code) : Bool :=
    match c with
    | .let _ k | .fun _ k => go k
    -- Approximation, the cases may have many unreachable alternatives, and only reachable.
    | .cases c => c.alts.size == 1 && c.alts.any fun alt => go alt.getCode
    -- Approximation, we assume that any code containing join points have more than one exit point
    | .jp .. | .jmp .. => false
    | .return .. | .unreach .. => true

/--
"Beta-reduce" `(fun params => code) args`.
If `mustInline` is true, the local function declarations in the resulting code are marked as `.mustInline`.
See comment at `updateFunDeclInfo`.
-/
def betaReduce (params : Array Param) (code : Code) (args : Array Expr) (mustInline := false) : SimpM Code := do
  -- TODO: add necessary casts to `args`
  let mut subst := {}
  for param in params, arg in args do
    subst := subst.insert param.fvarId arg
  let code ← code.internalize subst
  updateFunDeclInfo code mustInline
  return code

/--
Create a new local function declaration when `info.args.size < info.params.size`.
We use this function to inline/specialize a partial application of a local function.
-/
def specializePartialApp (info : InlineCandidateInfo) : SimpM FunDecl := do
  let mut subst := {}
  for param in info.params, arg in info.args do
    subst := subst.insert param.fvarId arg
  let mut paramsNew := #[]
  for param in info.params[info.args.size:] do
    let type ← replaceExprFVars param.type subst
    let paramNew ← mkAuxParam type
    paramsNew := paramsNew.push paramNew
    subst := subst.insert param.fvarId (.fvar paramNew.fvarId)
  let code ← info.value.internalize subst
  updateFunDeclInfo code
  mkAuxFunDecl paramsNew code

/--
If the value of the given let-declaration is an application that can be inlined, inline it.

`k` is the "continuation" for the let declaration.
-/
partial def inlineApp? (letDecl : LetDecl) (k : Code) : SimpM (Option Code) := do
  if k matches .unreach .. then return some k
  let some info ← inlineCandidate? letDecl.value | return none
  markSimplified
  let numArgs := info.args.size
  trace[Compiler.simp.inline] "inlining {letDecl.value}"
  let fvarId := letDecl.fvarId
  if numArgs < info.arity then
    let funDecl ← specializePartialApp info
    addSubst letDecl.fvarId (.fvar funDecl.fvarId)
    return some (.fun funDecl k)
  else
    let code ← betaReduce info.params info.value info.args[:info.arity]
    if k.isReturnOf fvarId && numArgs == info.arity then
      /- Easy case, the continuation `k` is just returning the result of the application. -/
      return code
    else if oneExitPointQuick code then
      /-
      `code` has only one exit point, thus we can attach the continuation directly there,
      and simplify the result.
      -/
      code.bind fun fvarId' => do
        /- fvarId' is the result of the computation -/
        if numArgs > info.arity then
          let decl ← mkAuxLetDecl (mkAppN (.fvar fvarId') info.args[info.arity:])
          let k ← replaceFVar k fvarId decl.fvarId
          return .let decl k
        else
          replaceFVar k fvarId fvarId'
    else
      /-
      `code` has multiple exit points, and the continuation is non-trivial
      Thus, we create an auxiliary join point.
      -/
      let jpParam ← mkAuxParam (← inferType (mkAppN info.f info.args[:info.arity]))
      let jpValue ← if numArgs > info.arity then
        let decl ← mkAuxLetDecl (mkAppN (.fvar jpParam.fvarId) info.args[info.arity:])
        let k ← replaceFVar k fvarId decl.fvarId
        pure <| .let decl k
      else
        replaceFVar k fvarId jpParam.fvarId
      let jpDecl ← mkAuxJpDecl #[jpParam] jpValue
      let code ← code.bind fun fvarId => return .jmp jpDecl.fvarId #[.fvar fvarId]
      return Code.jp jpDecl code

/--
Try to inline a join point.
-/
partial def inlineJp? (fvarId : FVarId) (args : Array Expr) : SimpM (Option Code) := do
  let some decl ← LCNF.findFunDecl? fvarId | return none
  unless (← shouldInlineLocal decl) do return none
  markSimplified
  betaReduce decl.params decl.value args

/--
Mark `fvarId` as an used free variable.
This is information is used to eliminate dead local declarations.
-/
def markUsedFVar (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with used := s.used.insert fvarId }

/--
Mark all free variables occurring in `e` as used.
This is information is used to eliminate dead local declarations.
-/
def markUsedExpr (e : Expr) : SimpM Unit :=
  modify fun s => { s with used := collectLocalDecls s.used e }

/--
Mark all free variables occurring on the right-hand side of the given let declaration as used.
This is information is used to eliminate dead local declarations.
-/
def markUsedLetDecl (letDecl : LetDecl) : SimpM Unit :=
  markUsedExpr letDecl.value

mutual
/--
Mark all free variables occurring in `code` as used.
-/
partial def markUsedCode (code : Code) : SimpM Unit := do
  match code with
  | .let decl k => markUsedLetDecl decl; markUsedCode k
  | .jp decl k | .fun decl k => markUsedFunDecl decl; markUsedCode k
  | .return fvarId => markUsedFVar fvarId
  | .unreach .. => return ()
  | .jmp fvarId args => markUsedFVar fvarId; args.forM markUsedExpr
  | .cases c => markUsedFVar c.discr; c.alts.forM fun alt => markUsedCode alt.getCode

/--
Mark all free variables occurring in `funDecl` as used.
-/
partial def markUsedFunDecl (funDecl : FunDecl) : SimpM Unit :=
  markUsedCode funDecl.value
end

/--
Return `true` if `fvarId` is in the `used` set.
-/
def isUsed (fvarId : FVarId) : SimpM Bool :=
  return (← get).used.contains fvarId

/--
Attach the given `decls` to `code`. For example, assume `decls` is `#[.let _x.1 := 10, .let _x.2 := true]`,
then the result is
```
let _x.1 := 10
let _x.2 := true
<code>
```
-/
def attachCodeDecls (decls : Array CodeDecl) (code : Code) : SimpM Code := do
  go decls.size code
where
  go (i : Nat) (code : Code) : SimpM Code := do
    if i > 0 then
      let decl := decls[i-1]!
      if (← isUsed decl.fvarId) then
        match decl with
        | .let decl => markUsedLetDecl decl; go (i-1) (.let decl code)
        | .fun decl => markUsedFunDecl decl; go (i-1) (.fun decl code)
        | .jp decl => markUsedFunDecl decl; go (i-1) (.jp decl code)
      else
        eraseCodeDecl decl
        go (i-1) code
    else
      return code

/--
Erase all free variables occurring in `decls` from the local context.
-/
def eraseCodeDecls (decls : Array CodeDecl) : SimpM Unit := do
  decls.forM fun decl => eraseCodeDecl decl

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
partial def inlineProjInst? (e : Expr) : SimpM (Option (Array CodeDecl × FVarId)) := do
  let .proj _ i s := e | return none
  let sType ← inferType s
  unless (← isClass? sType).isSome do return none
  let eType ← inferType e
  unless  (← isClass? eType).isNone do return none
  let (fvarId?, decls) ← visit s [i] |>.run |>.run #[]
  if let some fvarId := fvarId? then
    return some (decls, fvarId)
  else
    eraseCodeDecls decls
    return none
where
  visit (e : Expr) (projs : List Nat) : OptionT (StateRefT (Array CodeDecl) SimpM) FVarId := do
    let e ← findExpr e
    if let .proj _ i s := e then
      visit s (i :: projs)
    else if let some (ctorVal, ctorArgs) := e.constructorApp? (← getEnv) then
      let i :: projs := projs | unreachable!
      let e := ctorArgs[ctorVal.numParams + i]!
      if projs.isEmpty then
        let .fvar fvarId := e | unreachable!
        return fvarId
      else
        visit e projs
    else
      let .const declName us := e.getAppFn | failure
      let some decl ← getStage1Decl? declName | failure
      guard (decl.getArity == e.getAppNumArgs)
      let code := decl.instantiateValueLevelParams us
      let code ← betaReduce decl.params code e.getAppArgs (mustInline := true)
      visitCode code projs

  visitCode (code : Code) (projs : List Nat) : OptionT (StateRefT (Array CodeDecl) SimpM) FVarId := do
    match code with
    | .let decl k => modify (·.push (.let decl)); visitCode k projs
    | .fun decl k => modify (·.push (.fun decl)); visitCode k projs
    | .return fvarId => visit (.fvar fvarId) projs
    | _ => failure

/--
Return `some _jp.k` if the given `cases` is of the form
```
cases _x.i
  (... let _x.j₁ := ctorⱼ₁ ...; _jp.k _x.j₁)
  ...
  (... let _x.jₙ := ctorⱼₙ ...; _jp.k _x.jₙ)
```
where `_jp.k` is a join point of the form
```
let _jp.k y :=
  cases y ...
```
The goal is to mark `_jp.k` as must inline in this scenario.
The function also allows `_jp.k` to have a small prefix before
`cases y`. The small prefix is set using the configuration option
`config.smallThreshold`. It is currently the same threshold used to
decide when to inline a function that has multiple occurrences.

Example: consider the following declarations
```
@[inline] def pred? (x : Nat) : Option Nat :=
  match x with
  | 0 => none
  | x+1 => some x

def isZero (x : Nat) :=
 match pred? x with
 | some _ => false
 | none => true
```
After inlining `pred?` in `isZero`, this simplification is applicable, producing

Remark: this method does not assume `cases` has already been normalized,
but returns a normalized `FVarId` in case of success.
-/
def isCasesOnCases? (cases : Cases) : OptionT SimpM FVarId := do
  let jpFirst ← isCtorJmp? cases.alts[0]!.getCode
  let funDecl ← getFunDecl jpFirst
  guard <| (← isJpCases funDecl)
  for alt in cases.alts[1:] do
    let jp ← isCtorJmp? alt.getCode
    guard <| jpFirst == jp
  return jpFirst
where
  isCtorJmp? (code : Code) : OptionT SimpM FVarId := do
    match code with
    | .let _ k | .jp _ k | .fun _ k => isCtorJmp? k
    | .return .. | .unreach .. | .cases .. => failure
    | .jmp jpFVarId args =>
      let #[arg] := args | failure
      let arg ← findExpr (← normExpr arg)
      guard <| arg.isConstructorApp (← getEnv)
      normFVar jpFVarId

  isJpCases (funDecl : FunDecl) : SimpM Bool := do
    let param := funDecl.params[0]!
    let smallThreshold := (← read).config.smallThreshold
    let rec go (code : Code) (prefixSize : Nat) : Bool :=
      prefixSize <= smallThreshold &&
      match code with
      | .let _ k => go k (prefixSize + 1)
      | .cases c => c.discr == param.fvarId
      | _ => false
    return go funDecl.value 0

/--
Return the alternative in `alts` whose body appears in most arms,
and the number of occurrences.
We use this function to decide whether to create a `.default` case
or not.
-/
private def getMaxOccs (alts : Array Alt) : Alt × Nat := Id.run do
  let mut maxAlt := alts[0]!
  let mut max    := getNumOccsOf alts 0
  for i in [1:alts.size] do
    let curr := getNumOccsOf alts i
    if curr > max then
       maxAlt := alts[i]!
       max    := curr
  return (maxAlt, max)
where
  /--
  Return the number of occurrences of `alts[i]` in `alts`.
  We use alpha equivalence.
  Note that the number of occurrences can be greater than 1 only when
  the alternative does not depend on field parameters
  -/
  getNumOccsOf (alts : Array Alt) (i : Nat) : Nat := Id.run do
    let code := alts[i]!.getCode
    let mut n := 1
    for j in [i+1:alts.size] do
      if Code.alphaEqv alts[j]!.getCode code then
        n := n+1
    return n

/--
Add a default case to the given `cases` alternatives if there
are alternatives with equivalent (aka alpha equivalent) right hand sides.
-/
private def addDefault (alts : Array Alt) : SimpM (Array Alt) := do
  if alts.size <= 1 || alts.any (· matches .default ..) then
    return alts
  else
    let (max, noccs) := getMaxOccs alts
    if noccs == 1 then
      return alts
    else
      let mut altsNew := #[]
      let mut first := true
      markSimplified
      for alt in alts do
        if Code.alphaEqv alt.getCode max.getCode then
          let .alt _ ps k := alt | unreachable!
          eraseParams ps
          unless first do
            eraseCode k
          first := false
        else
          altsNew := altsNew.push alt
      return altsNew.push (.default max.getCode)

/--
Try to simplify projections `.proj _ i s` where `s` is constructor.
-/
def simpProj? (e : Expr) : OptionT SimpM Expr := do
  let .proj _ i s := e | failure
  let s ← findCtor s
  let some (ctorVal, args) := s.constructorApp? (← getEnv) | failure
  markSimplified
  return args[ctorVal.numParams + i]!

/--
Application over application.
```
let _x.i := f a
_x.i b
```
is simplified to `f a b`.
-/
def simpAppApp? (e : Expr) : OptionT SimpM Expr := do
  guard e.isApp
  let f := e.getAppFn
  guard f.isFVar
  let f ← findExpr f
  guard <| f.isApp || f.isConst
  markSimplified
  return mkAppN f e.getAppArgs

def applyImplementedBy? (e : Expr) : OptionT SimpM Expr := do
  guard <| (← read).config.implementedBy
  let .const declName us := e.getAppFn | failure
  let some declNameNew := getImplementedBy? (← getEnv) declName | failure
  markSimplified
  return mkAppN (.const declNameNew us) e.getAppArgs

/-- Try to apply simple simplifications. -/
def simpValue? (e : Expr) : SimpM (Option Expr) :=
  -- TODO: more simplifications
  simpProj? e <|> simpAppApp? e <|> applyImplementedBy? e

/--
Erase the given let-declaration from the local context,
and set the `simplified` flag to true.
-/
def eraseLetDecl (decl : LetDecl) : SimpM Unit := do
  LCNF.eraseLetDecl decl
  markSimplified

/--
Erase the given local function declaration from the local context,
and set the `simplified` flag to true.
-/
def eraseFunDecl (decl : FunDecl) : SimpM Unit := do
  LCNF.eraseFunDecl decl
  markSimplified

/--
When the configuration flag `etaPoly = true`, we eta-expand
partial applications of functions that take local instances as arguments.
This kind of function is inlined or specialized, and we create new
simplification opportunities by eta-expanding them.
-/
def etaPolyApp? (letDecl : LetDecl) : OptionT SimpM FunDecl := do
  guard <| (← read).config.etaPoly
  let .const declName _ := letDecl.value.getAppFn | failure
  let some info := (← getEnv).find? declName | failure
  guard <| hasLocalInst info.type
  guard <| !(← Meta.isInstance declName)
  let some decl ← getStage1Decl? declName | failure
  let numArgs := letDecl.value.getAppNumArgs
  guard <| decl.getArity > numArgs
  let params ← mkNewParams letDecl.type
  let value := mkAppN letDecl.value (params.map (.fvar ·.fvarId))
  let auxDecl ← mkAuxLetDecl value
  let funDecl ← mkAuxFunDecl params (.let auxDecl (.return auxDecl.fvarId))
  addSubst letDecl.fvarId (.fvar funDecl.fvarId)
  eraseLetDecl letDecl
  return funDecl

mutual
/--
Simplify the given local function declaration.
-/
partial def simpFunDecl (decl : FunDecl) : SimpM FunDecl := do
  let type ← normExpr decl.type
  let params ← normParams decl.params
  let value ← simp decl.value
  decl.update type params value

/--
Try to simplify `cases` of `constructor`
-/
partial def simpCasesOnCtor? (cases : Cases) : SimpM (Option Code) := do
  let discr ← normFVar cases.discr
  let discrExpr ← findCtor (.fvar discr)
  let some (ctorVal, ctorArgs) := discrExpr.constructorApp? (← getEnv) (useRaw := true) | return none
  let (alt, cases) := cases.extractAlt! ctorVal.name
  eraseCode (.cases cases)
  markSimplified
  match alt with
  | .default k => simp k
  | .alt _ params k =>
    let fields := ctorArgs[ctorVal.numParams:]
    let mut auxDecls := #[]
    for param in params, field in fields do
      /-
      `field` may not be a free variable. Recall that `constructorApp?` has special support for numerals,
      and `ctorArgs` contains a numeral if `discrExpr` is a numeral. We may have other cases in the future.
      To make the code robust, we add auxiliary declarations whenever the `field` is not a free variable.
      -/
      if field.isFVar then
        addSubst param.fvarId field
      else
        let auxDecl ← mkAuxLetDecl field
        auxDecls := auxDecls.push (CodeDecl.let auxDecl)
        addSubst param.fvarId (.fvar auxDecl.fvarId)
    let k ← simp k
    eraseParams params
    attachCodeDecls auxDecls k

/--
Simplify `code`
-/
partial def simp (code : Code) : SimpM Code := withIncRecDepth do
  incVisited
  match code with
  | .let decl k =>
    let mut decl ← normLetDecl decl
    if let some value ← simpValue? decl.value then
      decl ← decl.updateValue value
    if let some funDecl ← etaPolyApp? decl then
      simp (.fun funDecl k)
    else if decl.value.isFVar then
      /- Eliminate `let _x_i := _x_j;` -/
      addSubst decl.fvarId decl.value
      eraseLetDecl decl
      simp k
    else if let some code ← inlineApp? decl k then
      eraseLetDecl decl
      simp code
    else if let some (decls, fvarId) ← inlineProjInst? decl.value then
      addSubst decl.fvarId (.fvar fvarId)
      eraseLetDecl decl
      let k ← simp k
      attachCodeDecls decls k
    else
      let k ← simp k
      if (← isUsed decl.fvarId) then
        markUsedLetDecl decl
        return code.updateLet! decl k
      else
        /- Dead variable elimination -/
        eraseLetDecl decl
        return k
  | .fun decl k | .jp decl k =>
    let mut decl := decl
    let toBeInlined ← isOnceOrMustInline decl.fvarId
    if toBeInlined then
      /-
      If the declaration will be inlined, it is wasteful to eagerly simplify it.
      So, we just normalize it (i.e., apply the substitution to it).
      -/
      decl ← normFunDecl decl
    else
      /-
      Note that functions in `decl` will be marked as used even if `decl` is not actually used.
      They will only be deleted in the next pass.
      -/
      if code.isFun then
        if decl.isEtaExpandCandidate then
          /- We must apply substitution before trying to eta-expand, otherwise `inferType` may fail. -/
          decl ← normFunDecl decl
          /-
          We want to eta-expand **before** trying to simplify local function declaration because
          eta-expansion creates many optimization opportunities.
          -/
          decl ← decl.etaExpand
          markSimplified
      decl ← simpFunDecl decl
    let k ← simp k
    if (← isUsed decl.fvarId) then
      if toBeInlined then
        /-
        `decl` was supposed to be inlined, but there are still references to it.
        Thus, we must all variables in `decl` as used. Recall it was not eagerly simplified.
        -/
        markUsedFunDecl decl
      return code.updateFun! decl k
    else
      /- Dead function elimination -/
      eraseFunDecl decl
      return k
  | .return fvarId =>
    let fvarId ← normFVar fvarId
    markUsedFVar fvarId
    return code.updateReturn! fvarId
  | .unreach type =>
    return code.updateUnreach! (← normExpr type)
  | .jmp fvarId args =>
    let fvarId ← normFVar fvarId
    let args ← normExprs args
    if let some code ← inlineJp? fvarId args then
      simp code
    else
      markUsedFVar fvarId
      args.forM markUsedExpr
      return code.updateJmp! fvarId args
  | .cases c =>
    if let some k ← simpCasesOnCtor? c then
      return k
    else
      let simpCasesDefault := do
        let discr ← normFVar c.discr
        let resultType ← normExpr c.resultType
        markUsedFVar discr
        let alts ← c.alts.mapMonoM fun alt =>
          match alt with
          | .alt ctorName ps k =>
            withDiscrCtor discr ctorName ps do
              return alt.updateCode (← simp k)
          | .default k => return alt.updateCode (← simp k)
        let alts ← addDefault alts
        if alts.size == 1 && alts[0]! matches .default .. then
          return alts[0]!.getCode
        else
          return code.updateCases! resultType discr alts
      if let some jpFVarId ← isCasesOnCases? c then
        withAddMustInline jpFVarId simpCasesDefault
      else
        simpCasesDefault

end

end Simp

open Simp

def Decl.simp? (decl : Decl) : SimpM (Option Decl) := do
  updateFunDeclInfo decl.value
  trace[Compiler.simp.inline.info] "{decl.name}:{Format.nest 2 (← (← get).funDeclInfoMap.format)}"
  traceM `Compiler.simp.step do ppDecl decl
  let value ← simp decl.value
  traceM `Compiler.simp.step.new do return m!"{decl.name} :=\n{← ppCode value}"
  let s ← get
  trace[Compiler.simp.stat] "{decl.name}, size: {value.size}, # visited: {s.visited}, # inline: {s.inline}, # inline local: {s.inlineLocal}"
  if (← get).simplified then
    return some { decl with value }
  else
    return none

partial def Decl.simp (decl : Decl) (config : Config) : CompilerM Decl := do
  let mut config := config
  if (← isTemplateLike decl) then
    /-
    We do not eta-expand or inline partial applications in template like code.
    Recall we don't want to generate code for them.
    Remark: by eta-expanding partial applications in instances, we also make the simplifier
    work harder when inlining instance projections.
    -/
    config := { config with etaPoly := false, inlinePartial := false }
  go decl config
where
  go (decl : Decl) (config : Config) : CompilerM Decl := do
    if let some decl ← decl.simp? |>.run { config, declName := decl.name } |>.run' {} then
      -- TODO: bound number of steps?
      go decl config
    else
      return decl

def simp (config : Config := {}) (occurrence : Nat := 0) : Pass :=
  .mkPerDeclaration `simp (Decl.simp · config) .base (occurrence := occurrence)

builtin_initialize
  registerTraceClass `Compiler.simp (inherited := true)
  registerTraceClass `Compiler.simp.inline
  registerTraceClass `Compiler.simp.stat
  registerTraceClass `Compiler.simp.step
  registerTraceClass `Compiler.simp.step.new

end Lean.Compiler.LCNF
