/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.Recognizers
import Lean.Compiler.InlineAttrs
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.ElimDead
import Lean.Compiler.LCNF.Bind
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.Stage1

namespace Lean.Compiler.LCNF
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
  | /--
    Local function is applied once, and must be inlined.
    -/
    once
  | /--
    Local function is applied many times, and will only be inlined
    if it is small.
    -/
    many
  | /--
    Function must be inlined.
    -/
    mustInline
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
    let localDecl ← getLocalDecl fvarId
    result := result ++ "\n" ++ f!"{localDecl.userName} ↦ {repr info}"
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

partial def findFunDecl? (e : Expr) : CompilerM (Option FunDecl) := do
  match e with
  | .fvar fvarId =>
    if let some decl ← LCNF.findFunDecl? fvarId then
      return some decl
    else if let .ldecl (value := v) .. ← getLocalDecl fvarId then
      findFunDecl? v
    else
      return none
  | .mdata _ e => findFunDecl? e
  | _ => return none

partial def findExpr (e : Expr) (skipMData := true) : CompilerM Expr := do
  match e with
  | .fvar fvarId =>
    let .ldecl (value := v) .. ← getLocalDecl fvarId | return e
    findExpr v
  | .mdata _ e' => if skipMData then findExpr e' else return e
  | _ => return e

structure Config where
  smallThreshold : Nat := 1

structure Context where
  config : Config := {}

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

def markSimplified : SimpM Unit :=
  modify fun s => { s with simplified := true }

def incVisited : SimpM Unit :=
  modify fun s => { s with visited := s.visited + 1 }

def incInline : SimpM Unit :=
  modify fun s => { s with inline := s.inline + 1 }

def incInlineLocal : SimpM Unit :=
  modify fun s => { s with inlineLocal := s.inlineLocal + 1 }

partial def updateFunDeclInfo (code : Code) (mustInline := false) : SimpM Unit :=
  go code
where
  go (code : Code) : SimpM Unit := do
  match code with
  | .let decl k =>
    if decl.value.isApp then
      if let some funDecl ← findFunDecl? decl.value.getAppFn then
        modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.add funDecl.fvarId }
    go k
  | .fun decl k =>
    if mustInline then
      modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.addMustInline decl.fvarId }
    go decl.value; go k
  | .jp decl k => go decl.value; go k
  | .cases c => c.alts.forM fun alt => go alt.getCode
  | .return .. | .jmp .. | .unreach .. => return ()

def isOnceOrMustInline (fvarId : FVarId) : SimpM Bool := do
  match (← get).funDeclInfoMap.map.find? fvarId with
    | some .once | some .mustInline  => return true
    | _ => return false

def isSmall (decl : FunDecl) : SimpM Bool :=
  return decl.value.sizeLe (← read).config.smallThreshold

def shouldInlineLocal (decl : FunDecl) : SimpM Bool := do
  if (← isOnceOrMustInline decl.fvarId) then
    return true
  else
    isSmall decl

structure InlineCandidateInfo where
  isLocal : Bool
  params  : Array Param
  /-- Value (lambda expression) of the function to be inlined. -/
  value   : Code

def InlineCandidateInfo.arity : InlineCandidateInfo → Nat
  | { params, .. } => params.size

def inlineCandidate? (e : Expr) : SimpM (Option InlineCandidateInfo) := do
  let f := e.getAppFn
  if let .const declName us ← findExpr f then
    unless hasInlineAttribute (← getEnv) declName do return none
    -- TODO: check whether function is recursive or not.
    -- We can skip the test and store function inline so far.
    let some decl ← getStage1Decl? declName | return none
    let numArgs := e.getAppNumArgs
    let arity := decl.getArity
    if numArgs < arity then return none
    let params := decl.instantiateParamsLevelParams us
    let value := decl.instantiateValueLevelParams us
    incInline
    return some {
      isLocal := false
      params, value
    }
  else if let some decl ← findFunDecl? f then
    unless (← shouldInlineLocal decl) do return none
    let numArgs := e.getAppNumArgs
    let arity := decl.getArity
    if numArgs < arity then return none
    incInlineLocal
    modify fun s => { s with inlineLocal := s.inlineLocal + 1 }
    return some {
      isLocal := true
      params  := decl.params
      value   := decl.value
    }
  else
    return none

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

def betaReduce (params : Array Param) (code : Code) (args : Array Expr) : SimpM Code := do
  -- TODO: add necessary casts to `args`
  let mut subst := {}
  for param in params, arg in args do
    subst := subst.insert param.fvarId arg
  let code ← code.internalize subst
  updateFunDeclInfo code
  return code

/--
If `e` is an application that can be inlined, inline it.

`k?` is the optional "continuation" for `e`, and it may contain loose bound variables
that need to instantiated with `xs`. That is, if `k? = some k`, then `k.instantiateRev xs`
is an expression without loose bound variables.
-/
partial def inlineApp? (letDecl : LetDecl) (k : Code) : SimpM (Option Code) := do
  if k matches .unreach .. then return some k
  let e := letDecl.value
  let some info ← inlineCandidate? e | return none
  markSimplified
  let args := e.getAppArgs
  let numArgs := args.size
  trace[Compiler.simp.inline] "inlining {e}"
  let code ← betaReduce info.params info.value args[:info.arity]
  let fvarId := letDecl.fvarId
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
        let decl ← mkAuxLetDecl (mkAppN (.fvar fvarId') args[info.arity:])
        let k ← replaceFVar k fvarId decl.fvarId
        return .let decl k
      else
        replaceFVar k fvarId fvarId'
  else
    /-
    `code` has multiple exit points, and the continuation is non-trivial
    Thus, we create an auxiliary join point.
    -/
    let jpParam ← mkAuxParam (← inferType (mkAppN e.getAppFn args[:info.arity]))
    let jpValue ← if numArgs > info.arity then
      let decl ← mkAuxLetDecl (mkAppN (.fvar jpParam.fvarId) args[info.arity:])
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
  betaReduce decl.params decl.value args

def findCtor (e : Expr) : SimpM Expr := do
  -- TODO: add support for mapping discriminants to constructors in branches
  findExpr e

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

def markUsedFVar (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with used := s.used.insert fvarId }

def markUsedExpr (e : Expr) : SimpM Unit :=
  modify fun s => { s with used := collectLocalDecls s.used e }

def markUsedLetDecl (letDecl : LetDecl) : SimpM Unit :=
  markUsedExpr letDecl.value

def isUsed (fvarId : FVarId) : SimpM Bool :=
  return (← get).used.contains fvarId

def eraseLocalDecl (fvarId : FVarId) : SimpM Unit := do
  eraseFVar fvarId
  markSimplified

/--
Add substitution `fvarId ↦ val`. `val` is a free variable, or
it is a type, type former, or `lcErased`.
-/
def addSubst (fvarId : FVarId) (val : Expr) : SimpM Unit :=
  modify fun s => { s with subst := s.subst.insert fvarId val }

/-- Try to apply simple simplifications. -/
def simpValue? (e : Expr) : SimpM (Option Expr) :=
  simpProj? e <|> simpAppApp? e

mutual
partial def simpFunDecl (decl : FunDecl) : SimpM FunDecl := do
  let type ← normExpr decl.type
  let params ← normParams decl.params
  let value ← simp decl.value
  decl.update type params value

/-- Try to simplify `cases` of `constructor` -/
partial def simpCasesOnCtor? (cases : Cases) : SimpM (Option Code) := do
  let discr ← normFVar cases.discr
  let discrExpr ← findExpr (.fvar discr)
  let some (ctorVal, ctorArgs) := discrExpr.constructorApp? (← getEnv) | return none
  let (alt, cases) := cases.extractAlt! ctorVal.name
  eraseFVarsAt (.cases cases)
  markSimplified
  match alt with
  | .default k => simp k
  | .alt _ params k =>
    let fields := ctorArgs[ctorVal.numParams:]
    for param in params, field in fields do
      addSubst param.fvarId field
    let k ← simp k
    eraseParams params
    return k

partial def simp (code : Code) : SimpM Code := do
  incVisited
  match code with
  | .let decl k =>
    let mut decl ← normLetDecl decl
    if decl.value.isFVar then
      /- Eliminate `let _x_i := _x_j;` -/
      addSubst decl.fvarId decl.value
      eraseLocalDecl decl.fvarId
      simp k
    else if let some code ← inlineApp? decl k then
      eraseFVar decl.fvarId
      simp code
    else
      if let some value ← simpValue? decl.value then
        decl ← decl.updateValue value
      /- TODO: simple value simplifications & inlining -/
      let k ← simp k
      if !decl.pure || (← isUsed decl.fvarId) then
        markUsedLetDecl decl
        return code.updateLet! decl k
      else
        /- Dead variable elimination -/
        eraseLocalDecl decl.fvarId
        return k
  | .fun decl k | .jp decl k =>
    /-
    Variables in `decl` will be marked as used even if the function is eliminated.
    Thus, they will only be deleted in the second pass.

    Pontential improvement: if `decl.fvarId` is marked with `once` or `mustInline`, we will probably
    inline this declaration, and it may be wasteful to simplify it here.
    The alternative option is to just normalize `decl`, and if used mark all occurring there as used.
    -/
    let decl ← simpFunDecl decl
    let k ← simp k
    if (← isUsed decl.fvarId) then
      return code.updateFun! decl k
    else
      /- Dead function elimination -/
      eraseLocalDecl decl.fvarId
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
      -- TODO: other cases simplifications
      let discr ← normFVar c.discr
      let resultType ← normExpr c.resultType
      markUsedFVar discr
      let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← simp alt.getCode)
      return code.updateCases! resultType discr alts

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

partial def Decl.simp (decl : Decl) : CompilerM Decl := do
  if let some decl ← decl.simp? |>.run {} |>.run' {} then
    -- TODO: bound number of steps?
    decl.simp
  else
    return decl

builtin_initialize
  registerTraceClass `Compiler.simp.inline
  registerTraceClass `Compiler.simp.inline.info
  registerTraceClass `Compiler.simp.stat
  registerTraceClass `Compiler.simp.step
  registerTraceClass `Compiler.simp.step.new
  registerTraceClass `Compiler.simp.projInst

end Lean.Compiler.LCNF

#exit -- TODO: port rest of file


namespace Lean.Compiler
namespace Simp


/-
Ensure binder names are unique, and update local function information.
If `mustInline = true`, then local functions in `e` are marked with binders of the
form `_mustInline.<idx>`.
Remark: we used to store the `mustInline` information in the map `localInfoMap`,
using a `.mustInline` constructor at `LocalFunInfo`. However, this was incorrect
because there is no guarantee that we will be able to inline all occurrences of the
function in the current `simp` step. Since, we recompute `localInfoMap` from scratch
at the beginning of each compiler pass, the information was being lost.
-/


/--
This function performs the following operations in the given expression in a single pass.
- Ensure binder names for let-declarations are unique.
- Update local function information. That is, it updates the map `localInfoMap`.
- Apply `e.instantiateRev args`.

We use it to "internalize" expressions at startup and when performing inlining.
-/
def instantiateRevInternalize (e : Expr) (args : Array Expr) (mustInline := false) : SimpM Expr := do
  let lctx ← getLCtx
  let nextIdx := (← getThe CompilerM.State).nextIdx
  let localInfoMap ← modifyGet fun s => (s.localInfoMap, { s with localInfoMap := {} })
  let (e, { localInfoMap, nextIdx }) := instantiateRevInternalizeCore lctx e args mustInline |>.run { nextIdx, localInfoMap }
  modifyThe CompilerM.State fun s => { s with nextIdx }
  modify fun s => { s with localInfoMap }
  return e


def isSmallValue (value : Expr) : SimpM Bool := do
  lcnfSizeLe value (← read).config.smallThreshold

def shouldInlineLocal (localDecl : LocalDecl) : SimpM Bool := do
  if (← isOnceOrMustInline localDecl.userName) then
    return true
  else
    isSmallValue localDecl.value


/--
If `e` if a free variable that expands to a valid LCNF terminal `let`-block expression `e'`,
return `e'`.
-/
def expandTrivialExpr (e : Expr) : SimpM Expr := do
  if e.isFVar then
    let e' ← findExpr e
    unless e'.isLambda do
      if e != e' then
        markSimplified
        return e'
  return e

/--
Given `value` of the form `let x_1 := v_1; ...; let x_n := v_n; e`,
return `let x_1; ...; let x_n := v_n; let y : type := e; body`.

This methods assumes `type` and `value` do not have loose bound variables.

Remark: `body` may have many loose bound variables, and the loose bound variables > 0
must be lifted by `n`.
-/
private def mkFlatLet (y : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool := false) : Expr :=
  match value with
  | .letE binderName type value'@(.lam ..) (.bvar 0) nonDep =>
    /- Easy case that is often generated by `inlineProjInst?` -/
    .letE binderName type value' body nonDep
  | _ => go value 0
where
  go (value : Expr) (i : Nat) : Expr :=
    match value with
    | .letE n t v b d => .letE n t v (go b (i+1)) d
    | _ => .letE y type value (body.liftLooseBVars 1 i) nonDep

def mkLetUsingScope (e : Expr) : SimpM Expr := do
  modify fun s => { s with mkLet := s.mkLet + 1 }
  Compiler.mkLetUsingScope e

def mkLambda (as : Array Expr) (e : Expr) : SimpM Expr := do
  modify fun s => { s with mkLambda := s.mkLambda + 1 }
  Compiler.mkLambda as e

/--
Helper function for simplifying expressions such as
```
let _x.1 := fun {α β} => ReaderT.bind ... α β;
_x.1
```
to `ReaderT.bing ...`
This kind of expression is often generated by `inlineProjInst?`.
They are a side-effect of the implicit lambda feature when we write
```
instance [Monad m] : Monad (ReaderT ρ m) where
  bind := ReaderT.bind
```
Lean introduces implicit lambdas at the `ReaderT.bind` above.
-/
private def simpUsingEtaReduction (e : Expr) : Expr :=
  match e with
  | .letE _ _ v@(.lam ..) (.bvar 0) _ =>
    let v := v.eta
    if v.isLambda then e else v
  | .letE n t v b d => .letE n t v (simpUsingEtaReduction b) d
  | _ => e

private def etaExpand (type : Expr) (value : Expr) : SimpM Expr := do
  let typeArity := getArrowArity type
  let valueArity := getLambdaArity value
  if typeArity <= valueArity then
    -- It can be < because of the "any" type
    return value
  else
    withNewScope do
      let (xs, _) ← visitArrow type
      let value := getLambdaBody value
      let value := value.instantiateRev xs[:valueArity]
      let valueType ← inferType value
      let f ← mkLocalDecl (← mkFreshUserName `_f) valueType
      let k ← mkLambda #[f] (mkAppN f xs[valueArity:])
      let value ← attachJp value k
      mkLambda xs value

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
-/
partial def inlineProjInst? (e : Expr) : OptionT SimpM Expr := do
  let .proj _ _ s := e | failure
  let sType ← inferType s
  guard (← isClass? sType).isSome
  let eType ← inferType e
  guard (← isClass? eType).isNone
  /-
  We use `withNewScope` + `mkLetUsingScope` to filter the relevant let-declarations.
  Recall that we are extracting only one of the type class elements.
  -/
  let value ← withNewScope do mkLetUsingScope (← visitProj e)
  markSimplified
  let value := simpUsingEtaReduction value
  let value ← internalize value (mustInline := true)
  trace[Compiler.simp.projInst] "{e} =>\n{value}"
  return value
where
  visitProj (e : Expr) : OptionT SimpM Expr := do
    let .proj _ i s := e | unreachable!
    let s ← visit s
    if let some (ctorVal, ctorArgs) := s.constructorApp? (← getEnv) then
      return ctorArgs[ctorVal.numParams + i]!
    else
      failure

  visit (e : Expr) : OptionT SimpM Expr := do
    let e ← findExpr e
    if e.isConstructorApp (← getEnv) then
      return e
    else if e.isProj then
      /- We may have nested projections as we traverse parent classes. -/
      visit (← visitProj e)
    else
      let .const declName us := e.getAppFn | failure
      let some decl ← getStage1Decl? declName | failure
      guard <| decl.getArity == e.getAppNumArgs
      let value := decl.value.instantiateLevelParams decl.levelParams us
      let value := value.beta e.getAppArgs
      /-
      Here, we just go inside of the let-declaration block without trying to simplify it.
      Reason: a type class instannce may have many elements, and it does not make sense to simplify
      all of them when we are extracting only one of them.
      -/
      let value ← Compiler.visitLet (m := SimpM) value fun _ value => return value
      visit value

def betaReduce (e : Expr) (args : Array Expr) : SimpM Expr := do
  -- TODO: add necessary casts to `args`
  let result ← instantiateRevInternalize (getLambdaBody e) args
  return result

/--
Try "cases on cases" simplification.
If `casesFn args` is of the form
```
casesOn _x.i
  (... let _x.j₁ := ctorⱼ₁ ...; _jp.k _x.j₁)
  ...
  (... let _x.jₙ := ctorⱼₙ ...; _jp.k _x.jₙ)
```
where `_jp.k` is a join point of the form
```
let _jp.k := fun y =>
  casesOn y ...
```
Then, inline `_jp.k`. The idea is to force the `casesOn` application in the join point to
reduce after the inlining step.
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
After inlining `pred?` in `isZero`, we have
```
let _jp.1 := fun y : Option Nat =>
  casesOn y true (fun y => false)
casesOn x
  (let _x.1 := none; _jp.1 _x.1)
  (fun n => let _x.2 := some n; _jp.1 _x.2)
```
and this simplification is applicable, producing
```
casesOn x true (fun n => false)
```
-/
def simpCasesOnCases? (casesInfo : CasesInfo) (casesFn : Expr) (args : Array Expr) : OptionT SimpM Expr := do
  let mut jpFirst? := none
  for i in casesInfo.altsRange do
    let alt := args[i]!
    let jp ← isJpCtor? alt
    if let some jpFirst := jpFirst? then
       guard <| jp == jpFirst
    else
       let some localDecl ← findDecl? jp | failure
       let .lam _ _ jpBody _ := localDecl.value | failure
       guard (← isCasesApp? jpBody).isSome
       jpFirst? := jp
  let some jpFVarId := jpFirst? | failure
  let some localDecl ← findDecl? jpFVarId | failure
  let .lam _ _ jpBody _ := localDecl.value | failure
  let mut args := args
  for i in casesInfo.altsRange do
    args := args.modify i (inlineJp · jpBody)
  return mkAppN casesFn args
where
  isJpCtor? (alt : Expr) : OptionT SimpM FVarId := do
    match alt with
    | .lam _ _ b _ => isJpCtor? b
    | .letE _ _ v b _ => match b with
      | .letE .. => isJpCtor? b
      | .app (.fvar fvarId) (.bvar 0) =>
        let some localDecl ← findDecl? fvarId | failure
        guard localDecl.isJp
        guard <| v.isConstructorApp (← getEnv)
        return fvarId
      | _ => failure
    | _ => failure

  inlineJp (alt : Expr) (jpBody : Expr) : Expr :=
    match alt with
    | .lam n d b bi => .lam n d (inlineJp b jpBody) bi
    | .letE n t v b nd => .letE n t v (inlineJp b jpBody) nd
    | _ => jpBody

mutual
/--
Simplify the given lambda expression.
If `checkEmptyTypes := true`, then return `fun a_i : t_i => lcUnreachable` if
`t_i` is the `Empty` type.
-/
partial def visitLambda (e : Expr) (checkEmptyTypes := false): SimpM Expr :=
  withNewScope do
    let (as, e) ← Compiler.visitLambdaCore e
    if checkEmptyTypes then
      for a in as do
        if (← isEmptyType (← inferType a)) then
          let e := e.instantiateRev as
          let unreach ← mkLcUnreachable (← inferType e)
          let r ← mkLambda as unreach
          return r
    let e ← mkLetUsingScope (← visitLet e as)
    mkLambda as e

partial def visitCases (casesInfo : CasesInfo) (e : Expr) : SimpM Expr := do
  let f := e.getAppFn
  let mut args  := e.getAppArgs
  let major := args[casesInfo.discrsRange.stop - 1]!
  let major ← findExpr major
  if let some (ctorVal, ctorArgs) := major.constructorApp? (← getEnv) then
    /- Simplify `casesOn` constructor -/
    let ctorIdx := ctorVal.cidx
    let alt := args[casesInfo.altsRange.start + ctorIdx]!
    let ctorFields := ctorArgs[ctorVal.numParams:]
    let alt := alt.beta ctorFields
    assert! !alt.isLambda
    markSimplified
    visitLet alt
  else if let some e ← simpCasesOnCases? casesInfo f args then
    visitCases casesInfo e
  else
    for i in casesInfo.altsRange do
      args ← args.modifyM i (visitLambda · (checkEmptyTypes := true))
    return mkAppN f args


/-- Try to apply simple simplifications. -/
partial def simpValue? (e : Expr) : SimpM (Option Expr) :=
  simpProj? e <|> simpAppApp? e <|> inlineProjInst? e

/--
Let-declaration basic block visitor. `e` may contain loose bound variables that
still have to be instantiated with `xs`.
-/
partial def visitLet (e : Expr) (xs : Array Expr := #[]): SimpM Expr := do
  modify fun s => { s with visited := s.visited + 1 }
  match e with
  | .letE binderName type value body nonDep =>
    let type := type.instantiateRev xs
    let mut value := value.instantiateRev xs
    if value.isLambda then
      unless (← isOnceOrMustInline binderName) do
        /-
        If the local function will be inlined anyway, we don't simplify it here,
        we do it after its is inlined and we have information about the actual arguments.
        -/
        value ← visitLambda value
        unless isJpBinderName binderName || (← isSmallValue value) do
          /-
          This lambda is not going to be inlined. So, we eta-expand it IF it is not a join point.
          Recall that local function declarations that are not join points will be lambda lifted
          anyway. Eta-expanding here also creates new simplification opportunities for
          monadic local functions before we perform the lambda-lifting.
          For example, consider the local function
          ```
          let _x.23 := fun xs body =>
            ...
            let _x.29 := StateRefT'.lift _x.24
            let _x.30 := _x.25 _x.29
            let _x.31 := fun a => ...
            ReaderT.bind _x.30 _x.31
          ```
          The function applications `StateRefT'.lift` and `ReaderT.bind` are not inlined because
          they are partially applied. After, we eta-expand this code, it will be reduced at this stage.
          -/
          value ← etaExpand type value
    else if let some value' ← simpValue? value then
      if value'.isLet then
        let e := mkFlatLet binderName type value' body nonDep
        let e ← visitLet e xs
        return e
      value := value'
    if value.isFVar then
      /- Eliminate `let _x_i := _x_j;` -/
      markSimplified
      visitLet body (xs.push value)
    else if let some e ← inlineApp? value xs body then
      return e
    else
      let x ← mkLetDecl binderName type value nonDep
      visitLet body (xs.push x)
  | _ =>
    let e := e.instantiateRev xs
    if let some value ← simpValue? e then
      visitLet value
    else if let some casesInfo ← isCasesApp? e then
      visitCases casesInfo e
    else if let some e ← inlineApp? e #[] none then
      return e
    else
      expandTrivialExpr e
end

end Simp

end Lean.Compiler
