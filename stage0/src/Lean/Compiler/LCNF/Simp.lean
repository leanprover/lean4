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

def betaReduce (params : Array Param) (code : Code) (args : Array Expr) (mustInline := false) : SimpM Code := do
  -- TODO: add necessary casts to `args`
  let mut subst := {}
  for param in params, arg in args do
    subst := subst.insert param.fvarId arg
  let code ← code.internalize subst
  updateFunDeclInfo code mustInline
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

def markUsedFVar (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with used := s.used.insert fvarId }

def markUsedExpr (e : Expr) : SimpM Unit :=
  modify fun s => { s with used := collectLocalDecls s.used e }

def markUsedLetDecl (letDecl : LetDecl) : SimpM Unit :=
  markUsedExpr letDecl.value

mutual
partial def markUsedCode (code : Code) : SimpM Unit := do
  match code with
  | .let decl k => markUsedLetDecl decl; markUsedCode k
  | .jp decl k | .fun decl k => markUsedFunDecl decl; markUsedCode k
  | .return fvarId => markUsedFVar fvarId
  | .unreach .. => return ()
  | .jmp fvarId args => markUsedFVar fvarId; args.forM markUsedExpr
  | .cases c => markUsedFVar c.discr; c.alts.forM fun alt => markUsedCode alt.getCode

partial def markUsedFunDecl (funDecl : FunDecl) : SimpM Unit :=
  markUsedCode funDecl.value
end

def isUsed (fvarId : FVarId) : SimpM Bool :=
  return (← get).used.contains fvarId

def attachCodeDecls (decls : Array CodeDecl) (code : Code) : SimpM Code := do
  go decls.size code
where
  go (i : Nat) (code : Code) : SimpM Code := do
    if i > 0 then
      let decl := decls[i-1]!
      if decl.isPure || (← isUsed decl.fvarId) then
        match decl with
        | .let decl => markUsedLetDecl decl; go (i-1) (.let decl code)
        | .fun decl => markUsedFunDecl decl; go (i-1) (.fun decl code)
        | .jp decl => markUsedFunDecl decl; go (i-1) (.jp decl code)
      else
        eraseFVar decl.fvarId
        go (i-1) code
    else
      return code

def eraseCodeDecls (decls : Array CodeDecl) : SimpM Unit := do
  decls.forM fun decl => eraseFVar decl.fvarId

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

TODO: explain result
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
  -- TODO: more simplifications
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
    else if let some (decls, fvarId) ← inlineProjInst? decl.value then
      addSubst decl.fvarId (.fvar fvarId)
      eraseLocalDecl decl.fvarId
      let k ← simp k
      attachCodeDecls decls k
    else
      if let some value ← simpValue? decl.value then
        decl ← decl.updateValue value
      let k ← simp k
      if !decl.pure || (← isUsed decl.fvarId) then
        markUsedLetDecl decl
        return code.updateLet! decl k
      else
        /- Dead variable elimination -/
        eraseLocalDecl decl.fvarId
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

end Simp

end Lean.Compiler
