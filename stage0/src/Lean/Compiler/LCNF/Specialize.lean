/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.Simp
import Lean.Compiler.LCNF.SpecInfo
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.ToExpr
import Lean.Compiler.LCNF.Level

namespace Lean.Compiler.LCNF
namespace Specialize

abbrev Cache := Std.PHashMap Expr Name

builtin_initialize specCacheExt : EnvExtension Cache ←
  registerEnvExtension (pure {})

def cacheSpec (key : Expr) (declName : Name) : CoreM Unit :=
  modifyEnv fun env => specCacheExt.modifyState env (·.insert key declName)

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

@[inline] def withParams (ps : Array Param) (x : SpecializeM α) : SpecializeM α :=
  withReader (fun ctx => { ctx with scope := ps.foldl (init := ctx.scope) fun s p => s.insert p.fvarId }) x

@[inline] def withFVar (fvarId : FVarId) (x : SpecializeM α) : SpecializeM α :=
  withReader (fun ctx => { ctx with scope := ctx.scope.insert fvarId }) x

/--
Return `true` if `e` is a ground term. That is,
it contains only free variables t
-/
def isGround (e : Expr) : SpecializeM Bool := do
  let s := (← read).ground
  return !e.hasAnyFVar (!s.contains ·)

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
State for the `CollectorM` monad.
-/
structure State where
  /--
  Set of already visited free variables.
  -/
  visited : FVarIdSet := {}
  /--
  Free variables that must become new parameters of the code being specialized.
  -/
  params  : Array Param := #[]
  /--
  Let-declarations and local function declarations that are going to be "copied" to the code
  being specialized. For example, the let-declarations often contain the instance values.
  In the current specialization heuristic all let-declarations are ground values (i.e., they do not contain free-variables).
  However, local function declarations may contain free variables.

  The current heuristic tries to avoid work duplication. If a let-declaration is a ground value,
  it most likely will be computed during compilation time, and work duplication is not an issue.
  -/
  decls   : Array CodeDecl := #[]

/--
Monad for implementing the code specializer dependency collector.
See `collect`
-/
abbrev CollectorM := StateRefT State SpecializeM

/--
Mark a free variable as already visited.
We perform a topological sort over the dependencies.
-/
def markVisited (fvarId : FVarId) : CollectorM Unit :=
  modify fun s => { s with visited := s.visited.insert fvarId }

mutual
  /--
  Collect dependencies in parameters. We need this because parameters may
  contain other type parameters.
  -/
  partial def collectParams (params : Array Param) : CollectorM Unit :=
    params.forM (collectExpr ·.type)

  /--
  Collect dependencies in the given code. We need this function to be able
  to collect dependencies in a local function declaration.
  -/
  partial def collectCode (c : Code) : CollectorM Unit := do
    match c with
    | .let decl k => collectExpr decl.type; collectExpr decl.value; collectCode k
    | .fun decl k | .jp decl k => collectFunDecl decl; collectCode k
    | .cases c =>
      collectExpr c.resultType
      collectFVar c.discr
      c.alts.forM fun alt => do
        match alt with
        | .default k => collectCode k
        | .alt _ ps k => collectParams ps; collectCode k
    | .jmp _ args => args.forM collectExpr
    | .unreach type => collectExpr type
    | .return fvarId => collectFVar fvarId

  /-- Collect dependencies of a local function declaration. -/
  partial def collectFunDecl (decl : FunDecl) : CollectorM Unit := do
    collectExpr decl.type
    collectParams decl.params
    collectCode decl.value

  /--
  Process the given free variable.
  If it has not already been visited and is in scope, we collect its dependencies.
  -/
  partial def collectFVar (fvarId : FVarId) : CollectorM Unit := do
    unless (← get).visited.contains fvarId do
      markVisited fvarId
      if (← read).scope.contains fvarId then
        /- We only collect the variables in the scope of the function application being specialized. -/
        if let some funDecl ← findFunDecl? fvarId then
          collectFunDecl funDecl
          modify fun s => { s with decls := s.decls.push <| .fun funDecl }
        else if let some param ← findParam? fvarId then
          collectExpr param.type
          modify fun s => { s with params := s.params.push param }
        else if let some letDecl ← findLetDecl? fvarId then
          collectExpr letDecl.type
          if (← isGround letDecl.value) then
            -- It is a ground value, thus we keep collecting dependencies
            collectExpr letDecl.value
            modify fun s => { s with decls := s.decls.push <| .let letDecl }
          else
            -- It is not a ground value, we convert declaration into a parameter
            modify fun s => { s with params := s.params.push <| { letDecl with borrow := false } }
        else
          unreachable!

  /-- Collect dependencies of the given expression. -/
  partial def collectExpr (e : Expr) : CollectorM Unit := do
    e.forEach fun e => do
      match e with
      | .fvar fvarId => collectFVar fvarId
      | _ => pure ()
end

/--
Given the specialization mask `paramsInfo` and the arguments `args`,
collect their dependencies, and return an array `mask` of size `paramsInfo.size` s.t.
- `mask[i] = some args[i]` if `paramsInfo[i] != .other`
- `mask[i] = none`, otherwise.
That is, `mask` contains only the arguments that are contributing to the code specialization.
We use this information to compute a "key" to uniquely identify the code specialization, and
creating the specialized code.
-/
def collect (paramsInfo : Array SpecParamInfo) (args : Array Expr) : CollectorM (Array (Option Expr)) := do
  let mut argMask := #[]
  for paramInfo in paramsInfo, arg in args do
    match paramInfo with
    | .other =>
      argMask := argMask.push none
    | .fixedNeutral | .user | .fixedInst | .fixedHO =>
      argMask := argMask.push (some arg)
      collectExpr arg
  return argMask

end Collector

/--
Return `true` if it is worth using arguments `args` for specialization given the parameter specialization information.
-/
def shouldSpecialize (paramsInfo : Array SpecParamInfo) (args : Array Expr) : SpecializeM Bool := do
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
def expandCodeDecls (decls : Array CodeDecl) (body : Expr) : CompilerM Expr := do
  let xs := decls.map (mkFVar ·.fvarId)
  let values := decls.map fun
    | .let decl => decl.value
    | .fun decl | .jp decl => decl.toExpr
  let rec go (i : Nat) (subst : Array Expr) : Expr :=
    if h : i < values.size then
      let value := values[i].abstractRange i xs
      let value := value.instantiateRev subst
      go (i+1) (subst.push value)
    else
      (body.abstract xs).instantiateRev subst
  return go 0 #[]
termination_by go => values.size - i

/--
Create the "key" that uniquely identifies a code specialization.
`params` and `decls` are the declarations collected by the `collect` function above.
The result contains the list of universe level parameter names the key that `params`, `decls`, and `body` depends on.
We use this information to create the new auxiliary declaration and resulting application.
-/
def mkKey (params : Array Param) (decls : Array CodeDecl) (body : Expr) : CompilerM (Expr × List Name) := do
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
def mkSpecDecl (decl : Decl) (us : List Level) (argMask : Array (Option Expr)) (params : Array Param) (decls : Array CodeDecl) (levelParamsNew : List Name) : SpecializeM Decl := do
  let nameNew := decl.name ++ `_at_ ++ (← read).declName ++ (`spec).appendIndexAfter (← get).decls.size
  go nameNew |>.run' {}
where
  go (nameNew : Name) : InternalizeM Decl := do
    let mut params ← params.mapM internalizeParam
    let decls ← decls.mapM internalizeCodeDecl
    for param in decl.params, arg in argMask do
      if let some arg := arg then
        let arg ← normExpr arg
        modify fun s => s.insert param.fvarId arg
      else
        -- Keep the parameter
        let param := { param with type := param.type.instantiateLevelParams decl.levelParams us }
        params := params.push (← internalizeParam param)
    for param in decl.params[argMask.size:] do
      let param := { param with type := param.type.instantiateLevelParams decl.levelParams us }
      params := params.push (← internalizeParam param)
    let value := decl.instantiateValueLevelParams us
    let value ← internalizeCode value
    let value := attachCodeDecls decls value
    let type ← value.inferType
    let type ← mkForallParams params type
    let decl := { name := nameNew, levelParams := levelParamsNew, params, type, value : Decl }
    return decl.setLevelParams

/--
Given the specialization mask `paramsInfo` and the arguments `args`,
return the arguments that have not been considered for specialization.
-/
def getRemainingArgs (paramsInfo : Array SpecParamInfo) (args : Array Expr) : Array Expr := Id.run do
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
  partial def specializeApp? (e : Expr) : SpecializeM (Option Expr) := do
    unless e.isApp do return none
    let f := e.getAppFn
    let .const declName us := f | return none
    if (← Meta.isInstance declName) then return none
    let some paramsInfo ← getSpecParamInfo? declName | return none
    let args := e.getAppArgs
    unless (← shouldSpecialize paramsInfo args) do return none
    let some decl ← getStage1Decl? declName | return none
    trace[Compiler.specialize.candidate] "{e}, {paramsInfo}"
    let (argMask, { params, decls, .. }) ← Collector.collect paramsInfo args |>.run {}
    let keyBody := mkAppN f (argMask.filterMap id)
    let (key, levelParamsNew) ← mkKey params decls keyBody
    trace[Compiler.specialize.candidate] "key: {key}"
    assert! !key.hasLooseBVars
    assert! !key.hasFVar
    let usNew := levelParamsNew.map mkLevelParam
    let argsNew := params.map (mkFVar ·.fvarId) ++ getRemainingArgs paramsInfo args
    if let some declName ← findSpecCache? key then
      trace[Compiler.specialize.step] "cached: {declName}"
      return mkAppN (.const declName usNew) argsNew
    else
      let specDecl ← mkSpecDecl decl us argMask params decls levelParamsNew
      trace[Compiler.specialize.step] "new: {specDecl.name}"
      cacheSpec key specDecl.name
      let specDecl ← specDecl.etaExpand
      saveLCNFType specDecl.name specDecl.type
      let specDecl ← specDecl.simp {} -- TODO: `simp` config
      let specDecl ← specDecl.simp { etaPoly := true, inlinePartial := true, implementedBy := true }
      let value ← withReader (fun _ => { declName := specDecl.name }) do
         withParams specDecl.params <| visitCode specDecl.value
      let specDecl := { specDecl with value }
      modify fun s => { s with decls := s.decls.push specDecl }
      return mkAppN (.const specDecl.name usNew) argsNew

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
  if (← isTemplateLike decl) then
    return decl
  else
    let value ← withParams decl.params <| visitCode decl.value
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
