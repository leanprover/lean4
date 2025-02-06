/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.Simp
import Lean.Compiler.LCNF.SpecInfo
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.ToExpr
import Lean.Compiler.LCNF.Level
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.MonadScope
import Lean.Compiler.LCNF.Closure
import Lean.Compiler.LCNF.FVarUtil

namespace Lean.Compiler.LCNF
namespace Specialize

abbrev Cache := SMap Expr Name

structure CacheEntry where
  key : Expr
  declName : Name
  deriving Inhabited

def addEntry (cache : Cache) (e : CacheEntry) : Cache :=
  cache.insert e.key e.declName

builtin_initialize specCacheExt : SimplePersistentEnvExtension CacheEntry Cache ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries addEntry {} es).switch
  }

def cacheSpec (key : Expr) (declName : Name) : CoreM Unit :=
  modifyEnv fun env => specCacheExt.addEntry env { key, declName }

def findSpecCache? (key : Expr) : CoreM (Option Name) :=
  return specCacheExt.getState (← getEnv) |>.find? key

structure Context where
  /--
  Set of free variables in scope. The "collector" uses this information when collecting
  dependencies for code specialization.
  -/
  scope  : FVarIdSet := {}
  /--
  Set of let-declarations in scope that do not depend on parameters.
  -/
  ground : FVarIdSet := {}
  /--
  Name of the declaration being processed
  -/
  declName : Name

structure State where
  decls : Array Decl := #[]

abbrev SpecializeM := ReaderT Context $ StateRefT State CompilerM

instance : MonadScope SpecializeM where
  getScope := return (← read).scope
  withScope f := withReader (fun ctx => { ctx with scope := f ctx.scope })

/--
Return `true` if `e` is a ground term. That is,
it contains only free variables tagged as ground
-/
def isGround [TraverseFVar α] (e : α) : SpecializeM Bool := do
  let s := (← read).ground
  return allFVar (s.contains ·) e

@[inline] def withLetDecl (decl : LetDecl) (x : SpecializeM α) : SpecializeM α := do
  let grd ← isGround decl.value
  let fvarId := decl.fvarId
  withReader (fun { scope, ground, declName } => { declName, scope := scope.insert fvarId, ground := if grd then ground.insert fvarId else ground }) x

namespace Collector
/-!
# Dependency collector for the code specialization function.

During code specialization, we select which arguments are going to be used during the specialization.
Then, we have to collect their dependencies. For example, suppose are trying to specialize the following `IO.println`
and `List.forM` applications in the following example:
```
    def f xs a.1 :=
      let _x.2 := @instMonadEIO IO.Error
      let _x.5 := instToStringString
      let _x.9 := instToStringNat
      let _x.6 := "hello"
      let _x.61 := @IO.println String _x.5 _x.6 a.1 -- (*)
      cases _x.61
      | EStateM.Result.ok a.6 a.7 =>
        fun _f.72 _y.69 _y.70 :=
          let _x.71 := @IO.println Nat _x.9 _y.69 _y.70 -- (*)
          _x.71
        let _x.65 := @List.forM (fun α => PUnit → EStateM.Result IO.Error PUnit α) _x.2 Nat xs _f.72 a.7 -- (*)
        ...
      ...
```
For `IO.println` the `SpecArgInfo` is `[N, I, O, O]`, i.e., only the first two arguments are considered
for code specialization. The first one is computationally neutral, and the second one is an instance.
For `List.forM`, we have `[N, I, N, O, H]`. In this case, the fifth argument (tagged as `H`) is a function.
Note that the actual `List.forM` application has 6 arguments, the extra argument comes from the `IO` monad.

For the first `IO.println` application, the collector collects `_x.5`.
For the `List.forM`, it collects `_x.2`, `_x.9`, and `_f.72`.
The collected values are used to construct a key to identify the specialization. Arguments that were not considered are
replaced with `lcErased`. The key is used to make sure we don't keep generating the same specialization over and over again.
This is not an optimization, it is essential to prevent the code specializer from looping while specializing recursive functions.
The keys for these two applications are the terms.
```
@IO.println Nat instToStringNat lcErased lcErased
```
and
```
@List.forM
  (fun α => PUnit → EStateM.Result IO.Error PUnit α)
  (@instMonadEIO IO.Error) Nat lcErased
  (fun _y.69 _y.70 =>
   let _x.71 := @IO.println Nat instToStringNat _y.69 _y.70;
  _x.71)
```
The keys never contain free variables or loose bound variables.
-/

/--
Given the specialization mask `paramsInfo` and the arguments `args`,
collect their dependencies, and return an array `mask` of size `paramsInfo.size` s.t.
- `mask[i] = some args[i]` if `paramsInfo[i] != .other`
- `mask[i] = none`, otherwise.
That is, `mask` contains only the arguments that are contributing to the code specialization.
We use this information to compute a "key" to uniquely identify the code specialization, and
creating the specialized code.
-/
def collect (paramsInfo : Array SpecParamInfo) (args : Array Arg) : SpecializeM (Array (Option Arg) × Array Param × Array CodeDecl) := do
  let ctx ← read
  let lctx := (← getThe CompilerM.State).lctx
  let abstract (fvarId : FVarId) : Bool :=
    -- We convert let-declarations that are not ground into parameters
    !lctx.funDecls.contains fvarId && !ctx.ground.contains fvarId
  Closure.run (inScope := ctx.scope.contains) (abstract := abstract) do
    let mut argMask := #[]
    for paramInfo in paramsInfo, arg in args do
      match paramInfo with
      | .other =>
        argMask := argMask.push none
      | .fixedNeutral | .user | .fixedInst | .fixedHO =>
        argMask := argMask.push (some arg)
        Closure.collectArg arg
    return argMask

end Collector

/--
Return `true` if it is worth using arguments `args` for specialization given the parameter specialization information.
-/
def shouldSpecialize (paramsInfo : Array SpecParamInfo) (args : Array Arg) : SpecializeM Bool := do
  for paramInfo in paramsInfo, arg in args do
    match paramInfo with
    | .other => pure ()
    | .fixedNeutral => pure () -- If we want to monomorphize types such as `Array`, we need to change here
    | .fixedInst | .user => if (← isGround arg) then return true
    | .fixedHO => return true -- TODO: check whether this is too aggressive
  return false

/--
Convert the given declarations into `Expr`, and "zeta-reduce" them into body.
This function is used to compute the key that uniquely identifies an code specialization.
-/
def expandCodeDecls (decls : Array CodeDecl) (body : LetValue) : CompilerM Expr := do
  let xs := decls.map (mkFVar ·.fvarId)
  let values := decls.map fun
    | .let decl => decl.value.toExpr
    | .fun decl | .jp decl => decl.toExpr
  let rec go (i : Nat) (subst : Array Expr) : Expr :=
    if h : i < values.size then
      let value := values[i].abstractRange i xs
      let value := value.instantiateRev subst
      go (i+1) (subst.push value)
    else
      (body.toExpr.abstract xs).instantiateRev subst
    termination_by values.size - i
  return go 0 #[]

/--
Create the "key" that uniquely identifies a code specialization.
`params` and `decls` are the declarations collected by the `collect` function above.
The result contains the list of universe level parameter names the key that `params`, `decls`, and `body` depends on.
We use this information to create the new auxiliary declaration and resulting application.
-/
def mkKey (params : Array Param) (decls : Array CodeDecl) (body : LetValue) : CompilerM (Expr × List Name) := do
  let body ← expandCodeDecls decls body
  let key := ToExpr.run do
    ToExpr.withParams params do
      ToExpr.mkLambdaM params (← ToExpr.abstractM body)
  return normLevelParams key

open Internalize in
/--
Specialize `decl` using
- `us`: the universe level used to instantiate `decl.name`
- `argMask`: arguments that are being used to specialize the declaration.
- `params`: new parameters that arguments in `argMask` depend on.
- `decls`: local declarations that arguments in `argMask` depend on.
- `levelParamsNew`: the universe level parameters for the new declaration.
-/
def mkSpecDecl (decl : Decl) (us : List Level) (argMask : Array (Option Arg)) (params : Array Param) (decls : Array CodeDecl) (levelParamsNew : List Name) : SpecializeM Decl := do
  let nameNew := decl.name.appendCore `_at_ |>.appendCore (← read).declName |>.appendCore `spec |>.appendIndexAfter (← get).decls.size
  /-
  Recall that we have just retrieved `decl` using `getDecl?`, and it may have free variable identifiers that overlap with the free-variables
  in `params` and `decls` (i.e., the "closure").
  Recall that `params` and `decls` are internalized, but `decl` is not.
  Thus, we internalize `decl` before glueing these "pieces" together. We erase the internalized information after we are done.
  -/
  let decl ← decl.internalize
  try
    go decl nameNew |>.run' {}
  finally
    eraseDecl decl
where
  go (decl : Decl) (nameNew : Name) : InternalizeM Decl := do
    let .code code := decl.value | panic! "can only specialize decls with code"
    let mut params ← params.mapM internalizeParam
    let decls ← decls.mapM internalizeCodeDecl
    for param in decl.params, arg in argMask do
      if let some arg := arg then
        let arg ← normArg arg
        modify fun s => s.insert param.fvarId arg.toExpr
      else
        -- Keep the parameter
        let param := { param with type := param.type.instantiateLevelParamsNoCache decl.levelParams us }
        params := params.push (← internalizeParam param)
    for param in decl.params[argMask.size:] do
      let param := { param with type := param.type.instantiateLevelParamsNoCache decl.levelParams us }
      params := params.push (← internalizeParam param)
    let code := code.instantiateValueLevelParams decl.levelParams us
    let code ← internalizeCode code
    let code := attachCodeDecls decls code
    let type ← code.inferType
    let type ← mkForallParams params type
    let value := .code code
    let safe := decl.safe
    let recursive := decl.recursive
    let decl := { name := nameNew, levelParams := levelParamsNew, params, type, value, safe, recursive, inlineAttr? := none : Decl }
    return decl.setLevelParams

/--
Given the specialization mask `paramsInfo` and the arguments `args`,
return the arguments that have not been considered for specialization.
-/
def getRemainingArgs (paramsInfo : Array SpecParamInfo) (args : Array Arg) : Array Arg := Id.run do
  let mut result := #[]
  for info in paramsInfo, arg in args do
    if info matches .other then
      result := result.push arg
  return result ++ args[paramsInfo.size:]

mutual
  /--
  Try to specialize the function application in the given let-declaration.
  `k` is the continuation for the let-declaration.
  -/
  partial def specializeApp? (e : LetValue) : SpecializeM (Option LetValue) := do
    let .const declName us args := e | return none
    if args.isEmpty then return none
    if (← Meta.isInstance declName) then return none
    let some paramsInfo ← getSpecParamInfo? declName | return none
    unless (← shouldSpecialize paramsInfo args) do return none
    let some decl ← getDecl? declName | return none
    let .code _ := decl.value | return none
    trace[Compiler.specialize.candidate] "{e.toExpr}, {paramsInfo}"
    let (argMask, params, decls) ← Collector.collect paramsInfo args
    let keyBody := .const declName us (argMask.filterMap id)
    let (key, levelParamsNew) ← mkKey params decls keyBody
    trace[Compiler.specialize.candidate] "key: {key}"
    assert! !key.hasLooseBVars
    assert! !key.hasFVar
    let usNew := levelParamsNew.map mkLevelParam
    let argsNew := params.map (.fvar ·.fvarId) ++ getRemainingArgs paramsInfo args
    if let some declName ← findSpecCache? key then
      trace[Compiler.specialize.step] "cached: {declName}"
      return some (.const declName usNew argsNew)
    else
      let specDecl ← mkSpecDecl decl us argMask params decls levelParamsNew
      trace[Compiler.specialize.step] "new: {specDecl.name}"
      cacheSpec key specDecl.name
      specDecl.saveBase
      let specDecl ← specDecl.etaExpand
      specDecl.saveBase
      let specDecl ← specDecl.simp {}
      let specDecl ← specDecl.simp { etaPoly := true, inlinePartial := true, implementedBy := true }
      let value ← withReader (fun _ => { declName := specDecl.name }) do
         withParams specDecl.params <| specDecl.value.mapCodeM visitCode
      let specDecl := { specDecl with value }
      modify fun s => { s with decls := s.decls.push specDecl }
      return some (.const specDecl.name usNew argsNew)

  partial def visitFunDecl (funDecl : FunDecl) : SpecializeM FunDecl := do
    let value ← withParams funDecl.params <| visitCode funDecl.value
    funDecl.update' funDecl.type value

  partial def visitCode (code : Code) : SpecializeM Code := do
    match code with
    | .let decl k =>
      let mut decl := decl
      if let some value ← specializeApp? decl.value then
        decl ← decl.updateValue value
      let k ← withLetDecl decl <| visitCode k
      return code.updateLet! decl k
    | .fun decl k | .jp decl k =>
      let decl ← visitFunDecl decl
      let k ← withFVar decl.fvarId <| visitCode k
      return code.updateFun! decl k
    | .cases c =>
      let alts ← c.alts.mapMonoM fun alt =>
        match alt with
        | .default k => return alt.updateCode (← visitCode k)
        | .alt _ ps k => withParams ps do return alt.updateCode (← visitCode k)
      return code.updateAlts! alts
    | .unreach .. | .jmp .. | .return .. => return code

end

def main (decl : Decl) : SpecializeM Decl := do
  if (← decl.isTemplateLike) then
    return decl
  else
    let value ← withParams decl.params <| decl.value.mapCodeM visitCode
    return { decl with value }

end Specialize

partial def Decl.specialize (decl : Decl) : CompilerM (Array Decl) := do
  let (decl, s) ← Specialize.main decl |>.run { declName := decl.name } |>.run {}
  return s.decls.push decl

def specialize : Pass where
  phase := .base
  name  := `specialize
  run   := fun decls => do
    saveSpecParamInfo decls
    decls.foldlM (init := #[]) fun decls decl => return decls ++ (← decl.specialize)

builtin_initialize
  registerTraceClass `Compiler.specialize (inherited := true)
  registerTraceClass `Compiler.specialize.candidate
  registerTraceClass `Compiler.specialize.step

end Lean.Compiler.LCNF
