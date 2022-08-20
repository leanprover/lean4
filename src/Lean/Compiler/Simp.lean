/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM
import Lean.Compiler.Decl
import Lean.Compiler.Stage1
import Lean.Compiler.InlineAttrs

namespace Lean.Compiler
namespace Simp

partial def findLambda? (e : Expr) : CompilerM (Option LocalDecl) := do
  match e with
  | .fvar fvarId =>
    let some d@(.ldecl (value := v) ..) ← findDecl? fvarId | return none
    if v.isLambda then return some d else findLambda? v
  | .mdata _ e => findLambda? e
  | _ => return none

partial def findExpr (e : Expr) (skipMData := true): CompilerM Expr := do
  match e with
  | .fvar fvarId =>
    let some (.ldecl (value := v) ..) ← findDecl? fvarId | return e
    findExpr v
  | .mdata _ e' => if skipMData then findExpr e' else return e
  | _ => return e

inductive Occ where
  | once
  | many
  deriving Repr, Inhabited

/--
Local function declaration statistics.

Remark: we use the `userName` as the key. Thus, `ensureUniqueLetVarNames`
must be used before collectin stastistics.
-/
structure OccInfo where
  /--
  Mapping from local function name to occurrence information.
  -/
  map : Std.HashMap Name Occ := {}
  deriving Inhabited

def OccInfo.format (s : OccInfo) : Format := Id.run do
  let mut result := Format.nil
  for (k, n) in s.map.toList do
    result := result ++ "\n" ++ f!"{k} ↦ {repr n}"
  return result

instance : ToFormat OccInfo where
  format := OccInfo.format

def OccInfo.add (s : OccInfo) (key : Name) : OccInfo :=
  match s with
  | { map } =>
    match map.find? key with
    | some .once => { map := map.insert key .many }
    | none       => { map := map.insert key .once }
    | _          => { map }

structure Config where
  smallThreshold : Nat := 1

structure Context where
  config : Config := {}

structure State where
  /--
  (Approximate) occurence information for local function declarations.
  -/
  occInfo : OccInfo := {}
  simplified : Bool := false
  deriving Inhabited

abbrev SimpM := ReaderT Context $ StateRefT State CompilerM

/-- Ensure binder names are unique, and update occurrence information -/
partial def internalize (e : Expr) : SimpM Expr := do
  visitLambda e
where
  visitLambda (e : Expr) : SimpM Expr := do
    withNewScope do
      let (as, e) ← Compiler.visitLambda e
      let e ← mkLetUsingScope (← visitLet e #[])
      mkLambda as e

  visitCases (casesInfo : CasesInfo) (cases : Expr) : SimpM Expr := do
    let mut args := cases.getAppArgs
    for i in casesInfo.altsRange do
      args ← args.modifyM i visitLambda
    return mkAppN cases.getAppFn args

  visitValue (e : Expr) : SimpM Unit := do
    if e.isApp then
      match (← findLambda? e.getAppFn) with
      | some localDecl =>
        if localDecl.value.isLambda then
          let key := localDecl.userName
          modify fun s => { s with occInfo := s.occInfo.add key  }
      | _ => pure ()

  visitLet (e : Expr) (xs : Array Expr) : SimpM Expr := do
    match e with
    | .letE binderName type value body nonDep =>
      let idx ← mkFreshLetVarIdx
      let binderName' := match binderName with
        | .num p _ => .num p idx
        | _ => .num binderName idx
      let type  := type.instantiateRev xs
      let mut value := value.instantiateRev xs
      if value.isLambda then
        value ← visitLambda value
      else
        visitValue value
      let x ← mkLetDecl binderName' type value nonDep
      visitLet body (xs.push x)
    | _  =>
      let e := e.instantiateRev xs
      if let some casesInfo ← isCasesApp? e then
        visitCases casesInfo e
      else
        visitValue e
        return e

def markSimplified : SimpM Unit :=
  modify fun s => { s with simplified := true }

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

def shouldInlineLocal (localDecl : LocalDecl) : SimpM Bool := do
  match (← get).occInfo.map.find? localDecl.userName with
  | some .once => return true
  | _ => lcnfSizeLe localDecl.value (← read).config.smallThreshold

structure InlineCandidateInfo where
  isLocal : Bool
  arity : Nat
  /-- Value (lambda expression) of the function to be inlined. -/
  value : Expr

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
    /-
    Recall that we use binder names to build `InlineStats`.
    Thus, we use `ensureUniqueLetVarNames` to make sure there is no name collision.
    -/
    let value ← ensureUniqueLetVarNames (decl.value.instantiateLevelParams decl.levelParams us)
    return some {
      arity, value
      isLocal := false
    }
  else if let some localDecl ← findLambda? f then
    unless (← shouldInlineLocal localDecl) do return none
    let numArgs := e.getAppNumArgs
    let arity := getLambdaArity localDecl.value
    if numArgs < arity then return none
    let value ← ensureUniqueLetVarNames localDecl.value
    return some {
      arity, value
      isLocal := true
    }
  else
    return none

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
def mkFlatLet (y : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool := false) : Expr :=
  go value 0
where
  go (value : Expr) (i : Nat) : Expr :=
    match value with
    | .letE n t v b d => .letE n t v (go b (i+1)) d
    | _ => .letE y type value (body.liftLooseBVars 1 i) nonDep

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
  internalize value
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
  -- TODO: add necessary casts
  internalize (e.beta args)

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
    let (as, e) ← Compiler.visitLambda e
    if checkEmptyTypes then
      for a in as do
        if (← isEmptyType (← inferType a)) then
          let unreach ← mkLcUnreachable (← inferType e)
          let r ← mkLambda as unreach
          return r
    let e ← mkLetUsingScope (← visitLet e)
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

/--
If `e` is an application that can be inlined, inline it.

`k?` is the optional "continuation" for `e`, and it may contain loose bound variables
that need to instantiated with `xs`. That is, if `k? = some k`, then `k.instantiateRev xs`
is an expression without loose bound variables.
-/
partial def inlineApp? (e : Expr) (xs : Array Expr) (k? : Option Expr) : SimpM (Option Expr) := do
  let some info ← inlineCandidate? e | return none
  let args := e.getAppArgs
  let numArgs := args.size
  trace[Compiler.simp.inline] "inlining {e}"
  markSimplified
  if k?.isNone && numArgs == info.arity then
    /- Easy case, there is no continuation and `e` is not over applied -/
    visitLet (← betaReduce info.value args)
  else if (← onlyOneExitPoint info.value) then
    /- If `info.value` has only one exit point, we don't need to create a new auxiliary join point -/
    let mut value ← betaReduce info.value args[:info.arity]
    if numArgs > info.arity then
      let type ← inferType (mkAppN e.getAppFn args[:info.arity])
      value := mkFlatLet (← mkAuxLetDeclName) type value (mkAppN (.bvar 0) args[info.arity:])
    if let some k := k? then
      let type ← inferType e
      value := mkFlatLet (← mkAuxLetDeclName) type value k
    visitLet value xs
  else
    /-
    There is a continuation `k` or `e` is over applied.
    If `e` is over applied, the extra arguments act as a continuation.

    We create a new join point
    ```
    let jp := fun y =>
      let x := y <extra-arguments> -- if `e` is over applied
      k
    ```
    Recall that `visitLet` incorporates the current continuation
    to the new join point `jp`.
    -/
    let jpDomain ← inferType (mkAppN e.getAppFn args[:info.arity])
    let binderName ← mkFreshUserName `_y
    let jp ← withNewScope do
      let y ← mkLocalDecl binderName jpDomain
      let body ← if numArgs == info.arity then
        visitLet k?.get! (xs.push y)
      else
        let x ← mkAuxLetDecl (mkAppN y args[info.arity:])
        if let some k := k? then
          visitLet k (xs.push x)
        else
          visitLet x (xs.push x)
      let body ← mkLetUsingScope body
      mkLambda #[y] body
    let jp ← mkJpDeclIfNotSimple jp
    let value ← betaReduce info.value args[:info.arity]
    let value ← attachJp value jp
    visitLet value

/-- Try to apply simple simplifications. -/
partial def simpValue? (e : Expr) : SimpM (Option Expr) :=
  simpProj? e <|> simpAppApp? e <|> inlineProjInst? e

/--
Let-declaration basic block visitor. `e` may contain loose bound variables that
still have to be instantiated with `xs`.
-/
partial def visitLet (e : Expr) (xs : Array Expr := #[]): SimpM Expr := do
  match e with
  | .letE binderName type value body nonDep =>
    let mut value := value.instantiateRev xs
    if value.isLambda then
      value ← visitLambda value
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
      let type := type.instantiateRev xs
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

def Decl.simp? (decl : Decl) : Simp.SimpM (Option Decl) := do
  let value ← Simp.internalize decl.value
  trace[Compiler.simp.inline.occs] "{decl.name}:{Format.nest 2 (format (← get).occInfo)}"
  trace[Compiler.simp.step] "{decl.name} :=\n{decl.value}"
  let value ← Simp.visitLambda value
  trace[Compiler.simp.step.new] "{decl.name} :=\n{value}"
  trace[Compiler.simp.stat] "{decl.name}: {← getLCNFSize decl.value}"
  if (← get).simplified then
    return some { decl with value }
  else
    return none

partial def Decl.simp (decl : Decl) : CoreM Decl := do
  if let some decl ← decl.simp? |>.run {} |>.run' {} |>.run' {} then
    -- TODO: bound number of steps?
    decl.simp
  else
    return decl

builtin_initialize
  registerTraceClass `Compiler.simp.inline
  registerTraceClass `Compiler.simp.stat
  registerTraceClass `Compiler.simp.step
  registerTraceClass `Compiler.simp.step.new
  registerTraceClass `Compiler.simp.inline.occs

end Lean.Compiler
