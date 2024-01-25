/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ProjFns
import Lean.Compiler.BorrowedAnnotation
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.Bind
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.Util

namespace Lean.Compiler.LCNF
namespace ToLCNF

/--
Return `true` if `e` is a `lcProof` application.
Recall that we use `lcProof` to erase all nested proofs.
-/
def isLCProof (e : Expr) : Bool :=
  e.isAppOfArity ``lcProof 1

/-- Create the temporary `lcProof` -/
def mkLcProof (p : Expr) :=
  mkApp (mkConst ``lcProof []) p

/--
Auxiliary inductive datatype for constructing LCNF `Code` objects.
The `toLCNF` function maintains a sequence of elements that is eventually
converted into `Code`.
-/
inductive Element where
  | jp  (decl : FunDecl)
  | fun (decl : FunDecl)
  | let (decl : LetDecl)
  | cases (p : Param) (cases : Cases)
  | unreach (p : Param)
  deriving Inhabited

/--
State for `BindCasesM` monad
Mapping from `_alt.<idx>` variables to new join points
-/
abbrev BindCasesM.State := FVarIdMap FunDecl

/-- Auxiliary monad for implementing `bindCases` -/
abbrev BindCasesM := StateRefT BindCasesM.State CompilerM

/--
This method returns code that at each exit point of `cases`, it jumps to `jpDecl`.
It is similar to `Code.bind`, but we add special support for `inlineMatcher`.
The `inlineMatcher` function inlines the auxiliary `_match_<idx>` declarations.
To make sure there is no code duplication, `inlineMatcher` creates auxiliary declarations `_alt.<idx>`.
We can say the `_alt.<idx>` declarations are pre join points. For each auxiliary declaration used at
an exit point of `cases`, this method creates an new auxiliary join point that invokes `_alt.<idx>`,
and then jumps to `jpDecl`. The goal is to make sure the auxiliary join point is the only occurrence
of `_alt.<idx>`, then `simp` will inline it.
That is, our goal is to try to promote the pre join points `_alt.<idx>` into a proper join point.
-/
partial def bindCases (jpDecl : FunDecl) (cases : Cases) : CompilerM Code := do
  let (alts, s) ← visitAlts cases.alts |>.run {}
  let resultType ← mkCasesResultType alts
  let result := .cases { cases with alts, resultType }
  let result := s.fold (init := result) fun result _ altJp => .jp altJp result
  return .jp jpDecl result
where
  visitAlts (alts : Array Alt) : BindCasesM (Array Alt) :=
    alts.mapM fun alt => return alt.updateCode (← go alt.getCode)

  findFun? (f : FVarId) : CompilerM (Option FunDecl) := do
    if let some funDecl ← findFunDecl? f then
      return funDecl
    else if let some (.fvar f' #[]) ← findLetValue? f then
      findFun? f'
    else
      return none

  go (code : Code) : BindCasesM Code := do
    match code with
    | .let decl k =>
      if let .return fvarId := k then
        /-
        Check whether the current let-declaration is of the form
        ```
        let _x := _alt.<idx> args
        return _x
        ```
        where `_alt.<idx>` is an auxiliary declaration created by `inlineMatcher`
        -/
        if decl.fvarId == fvarId then
          match decl.value with
          | .fvar f args =>
            let binderName ← getBinderName f
            if binderName.getPrefix == `_alt then
              if let some funDecl ← findFun? f then
                eraseLetDecl decl
                if let some altJp := (← get).find? f then
                  /- We already have an auxiliary join point for `f`, then, we just use it. -/
                  return .jmp altJp.fvarId args
                else
                  /-
                  We have not created a join point for `f` yet.
                  The join point has the form
                  ```
                  jp altJp jpParams :=
                    let _x := f jpParams
                    jmp jpDecl _x
                  ```
                  Then, we replace the current `let`-declaration with `jmp altJp args`
                  -/
                  let mut jpParams := #[]
                  let mut subst := {}
                  let mut jpArgs := #[]
                  /- Remark: `funDecl.params.size` may be greater than `args.size`. -/
                  for param in funDecl.params[:args.size] do
                    let type ← replaceExprFVars param.type subst (translator := true)
                    let paramNew ← mkAuxParam type
                    jpParams := jpParams.push paramNew
                    subst := subst.insert param.fvarId (Expr.fvar paramNew.fvarId)
                    jpArgs := jpArgs.push (Arg.fvar paramNew.fvarId)
                  let letDecl ← mkAuxLetDecl (.fvar f jpArgs)
                  let jpValue := .let letDecl (.jmp jpDecl.fvarId #[.fvar letDecl.fvarId])
                  let altJp ← mkAuxJpDecl jpParams jpValue
                  modify fun map => map.insert f altJp
                  return .jmp altJp.fvarId args
          | _ => pure ()
      let k ← go k
      if let some altJp := (← get).find? decl.fvarId then
        -- The new join point depends on this variable. Thus, we must insert it here
        modify fun s => s.erase decl.fvarId
        return .let decl (.jp altJp k)
      else
        return .let decl k
    | .fun decl k => return .fun decl (← go k)
    | .jp decl k =>
      let value ← go decl.value
      let type ← value.inferParamType decl.params
      let decl ← decl.update' type value
      return .jp decl (← go k)
    | .cases c =>
      let alts ← c.alts.mapM fun
        | .alt ctorName params k => return .alt ctorName params (← go k)
        | .default k => return .default (← go k)
      if alts.isEmpty then
        throwError "`Code.bind` failed, empty `cases` found"
      let resultType ← mkCasesResultType alts
      return .cases { c with alts, resultType }
    | .return fvarId => return .jmp jpDecl.fvarId #[.fvar fvarId]
    | .jmp .. | .unreach .. => return code

def seqToCode (seq : Array Element) (k : Code) : CompilerM Code := do
  go seq seq.size k
where
  go (seq : Array Element) (i : Nat) (c : Code) : CompilerM Code := do
    if i > 0 then
      match seq[i-1]! with
      | .jp decl => go seq (i - 1) (.jp decl c)
      | .fun decl => go seq (i - 1) (.fun decl c)
      | .let decl => go seq (i - 1) (.let decl c)
      | .unreach _ =>
        let type ← c.inferType
        eraseCode c
        seq[:i].forM fun
          | .let decl => eraseLetDecl decl
          | .jp decl | .fun decl => eraseFunDecl decl
          | .cases _ cs => eraseCode (.cases cs)
          | .unreach auxParam => eraseParam auxParam
        return .unreach type
      | .cases auxParam cases =>
        if let .return fvarId := c then
          if auxParam.fvarId == fvarId then
            eraseParam auxParam
            go seq (i - 1) (.cases cases)
          else
            -- `cases` is dead code
            go seq (i - 1) c
        else if auxParam.type.headBeta.isForall then
          /-
          `cases` produces a function. Thus, we create a local function to store
          result instead of a joinpoint that takes a closure.
          -/
          eraseParam auxParam
          let auxFunDecl := { auxParam with params := #[], value := .cases cases : FunDecl }
          modifyLCtx fun lctx => lctx.addFunDecl auxFunDecl
          let auxFunDecl ← auxFunDecl.etaExpand
          go seq (i - 1) (.fun auxFunDecl c)
        else
          /- Create a join point for `c` and jump to it from `cases` -/
          let jpDecl ← mkAuxJpDecl' auxParam c
          go seq (i - 1) (← bindCases jpDecl cases)
    else
      return c

structure State where
  /-- Local context containing the original Lean types (not LCNF ones). -/
  lctx : LocalContext := {}
  /-- Cache from Lean regular expression to LCNF argument. -/
  cache : PHashMap Expr Arg := {}
  /-- `toLCNFType` cache -/
  typeCache : HashMap Expr Expr := {}
  /-- isTypeFormerType cache -/
  isTypeFormerTypeCache : HashMap Expr Bool := {}
  /-- LCNF sequence, we chain it to create a LCNF `Code` object. -/
  seq : Array Element := #[]
  /--
  Fields that are type formers must be replaced with `◾`
  in the resulting code. Otherwise, we have data occurring in
  types.
  When converting a `casesOn` into LCNF, we add constructor fields
  that are types and type formers into this set. See `visitCases`.
  -/
  toAny : FVarIdSet := {}

abbrev M := StateRefT State CompilerM

@[inline] def liftMetaM (x : MetaM α) : M α := do
  x.run' { lctx := (← get).lctx }

/-- Add LCNF element to the current sequence -/
def pushElement (elem : Element) : M Unit := do
  modify fun s => { s with seq := s.seq.push elem }

def mkUnreachable (type : Expr) : M Arg := do
  let p ← mkAuxParam type
  pushElement (.unreach p)
  return .fvar p.fvarId

def mkAuxLetDecl (e : LetValue) (prefixName := `_x) : M FVarId := do
  match e with
  | .fvar fvarId #[] => return fvarId
  | _ =>
    let letDecl ← mkLetDecl (← mkFreshBinderName prefixName) (← e.inferType) e
    pushElement (.let letDecl)
    return letDecl.fvarId

def letValueToArg (e : LetValue) (prefixName := `_x) : M Arg :=
  return .fvar (← mkAuxLetDecl e prefixName)

/-- Create `Code` that executes the current `seq` and then returns `result` -/
def toCode (result : Arg) : M Code := do
  match result with
  | .fvar fvarId => seqToCode (← get).seq (.return fvarId)
  | .erased | .type .. =>
    let fvarId ← mkAuxLetDecl .erased
    seqToCode (← get).seq (.return fvarId)

def run (x : M α) : CompilerM α :=
  x |>.run' {}

/--
Return true iff `type` is `Sort _` or `As → Sort _`.
-/
private partial def isTypeFormerType (type : Expr) : M Bool := do
  match quick (← getEnv) type with
  | .true => return true
  | .false => return false
  | .undef =>
    if let some result := (← get).isTypeFormerTypeCache.find? type then
      return result
    let result ← liftMetaM <| Meta.isTypeFormerType type
    modify fun s => { s with isTypeFormerTypeCache := s.isTypeFormerTypeCache.insert type result }
    return result
where
  quick (env : Environment) : Expr → LBool
  | .forallE _ _ b _ => quick env b
  | .mdata _ b => quick env b
  | .letE .. => .undef
  | .sort _ => .true
  | .bvar .. => .false
  | type =>
    match type.getAppFn with
    | .bvar .. => .false
    | .const declName _ =>
      if let some (.inductInfo ..) := env.find? declName then
        .false
      else
        .undef
    | _ => .undef

def withNewScope (x : M α) : M α := do
  let saved ← get
  -- typeCache and isTypeFormerTypeCache are not backtrackable
  let saved := { saved with typeCache := {}, isTypeFormerTypeCache := {} }
  modify fun s => { s with seq := #[] }
  try
    x
  finally
    let saved := { saved with
      typeCache := (← get).typeCache
      isTypeFormerTypeCache := (← get).isTypeFormerTypeCache
    }
    set saved

/-
Replace free variables in `type'` that occur in `toAny` into `◾`.
Recall that we populate `toAny` with the free variable ids of fields that
are type formers. This can happen when we have a field whose type is, for example, `Type u`.
-/
def applyToAny (type : Expr) : M Expr := do
  let toAny := (← get).toAny
  return type.replace fun
    | .fvar fvarId => if toAny.contains fvarId then some erasedExpr else none
    | _ => none

def toLCNFType (type : Expr) : M Expr := do
  match (← get).typeCache.find? type with
  | some type' => return type'
  | none =>
    let type' ← liftMetaM <| LCNF.toLCNFType type
    let type' ← applyToAny type'
    modify fun s => { s with typeCache := s.typeCache.insert type type' }
    return type'

def cleanupBinderName (binderName : Name) : CompilerM Name :=
  if binderName.hasMacroScopes then
    let binderName := binderName.eraseMacroScopes
    mkFreshBinderName binderName
  else
    return binderName

/-- Create a new local declaration using a Lean regular type. -/
def mkParam (binderName : Name) (type : Expr) : M Param := do
  let binderName ← cleanupBinderName binderName
  let borrow := isMarkedBorrowed type
  let type' ← toLCNFType type
  let param ← LCNF.mkParam binderName type' borrow
  modify fun s => { s with lctx  := s.lctx.mkLocalDecl param.fvarId binderName type .default }
  return param

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (type' : Expr) (arg : Arg) : M LetDecl := do
  let binderName ← cleanupBinderName binderName
  let value' ← match arg with
    | .fvar fvarId => pure <| .fvar fvarId #[]
    | .erased | .type .. => pure .erased
  let letDecl ← LCNF.mkLetDecl binderName type' value'
  modify fun s => { s with
    lctx := s.lctx.mkLetDecl letDecl.fvarId binderName type value false
    seq := s.seq.push <| .let letDecl
  }
  return letDecl

def visitLambda (e : Expr) : M (Array Param × Expr) :=
  go e #[] #[]
where
  go (e : Expr) (xs : Array Expr) (ps : Array Param) := do
    if let .lam binderName type body _ := e then
      let type := type.instantiateRev xs
      let p ← mkParam binderName type
      go body (xs.push p.toExpr) (ps.push p)
    else
      return (ps, e.instantiateRev xs)

def visitBoundedLambda (e : Expr) (n : Nat) : M (Array Param × Expr) :=
  go e n #[] #[]
where
  go (e : Expr) (n : Nat) (xs : Array Expr) (ps : Array Param) := do
    if n == 0 then
      return (ps, e.instantiateRev xs)
    else if let .lam binderName type body _ := e then
      let type := type.instantiateRev xs
      let p ← mkParam binderName type
      go body (n-1) (xs.push p.toExpr) (ps.push p)
    else
      return (ps, e.instantiateRev xs)

def mustEtaExpand (env : Environment) (e : Expr) : Bool :=
  if let .const declName _ := e.getAppFn then
    match env.find? declName with
    | some (.recInfo ..) | some (.ctorInfo ..) | some (.quotInfo ..) => true
    | _ => isCasesOnRecursor env declName || isNoConfusion env declName || env.isProjectionFn declName || declName == ``Eq.ndrec
  else
    false

/--
Eta-expand with `n` lambdas.
-/
def etaExpandN (e : Expr) (n : Nat) : M Expr := do
  if n == 0 then
    return e
  else liftMetaM do
    Meta.forallBoundedTelescope (← Meta.inferType e) n fun xs _ =>
      Meta.mkLambdaFVars xs (mkAppN e xs)

/--
Eta reduce implicits. We use this function to eliminate introduced by the implicit lambda feature,
where it generates terms such as `fun {α} => ReaderT.pure`
-/
partial def etaReduceImplicit (e : Expr) : Expr :=
  match e with
  | .lam _ d b bi =>
    if bi.isImplicit then
      let b' := etaReduceImplicit b
      match b' with
      | .app f (.bvar 0) =>
        if !f.hasLooseBVar 0 then
          f.lowerLooseBVars 1 1
        else
          e.updateLambdaE! d b'
      | _ => e.updateLambdaE! d b'
    else
      e
  | _ => e

def litToValue (lit : Literal) : LitValue :=
  match lit with
  | .natVal val => .natVal val
  | .strVal val => .strVal val

/--
Put the given expression in `LCNF`.

- Nested proofs are replaced with `lcProof`-applications.
- Eta-expand applications of declarations that satisfy `shouldEtaExpand`.
- Put computationally relevant expressions in A-normal form.
-/
partial def toLCNF (e : Expr) : CompilerM Code := do
  run do toCode (← visit e)
where
  visitCore (e : Expr) : M Arg := withIncRecDepth do
    if let some arg := (← get).cache.find? e then
      return arg
    let r : Arg ← match e with
      | .app ..      => visitApp e
      | .const ..    => visitApp e
      | .proj s i e  => visitProj s i e
      | .mdata d e   => visitMData d e
      | .lam ..      => visitLambda e
      | .letE ..     => visitLet e #[]
      | .lit lit     => visitLit lit
      | .fvar fvarId => if (← get).toAny.contains fvarId then pure .erased else pure (.fvar fvarId)
      | .forallE .. | .mvar .. | .bvar .. | .sort ..  => unreachable!
    modify fun s => { s with cache := s.cache.insert e r }
    return r

  visit (e : Expr) : M Arg := withIncRecDepth do
    if isLCProof e then
      return .erased
    let type ← liftMetaM <| Meta.inferType e
    if (← liftMetaM <| Meta.isProp type) then
      /- We erase proofs. -/
      return .erased
    if (← isTypeFormerType type) then
      /-
      We erase type formers unless they occur as application arguments.
      Recall that we usually do not generate code for functions that return type,
      by this branch can be reachable if we cannot establish whether the function produces a type or not.
      -/
      return .erased
    visitCore e

  visitLit (lit : Literal) : M Arg :=
    letValueToArg (.value (litToValue lit))

  visitAppArg (e : Expr) : M Arg := do
    if isLCProof e then
      return .erased
    let type ← liftMetaM <| Meta.inferType e
    if (← liftMetaM <| Meta.isProp type) then
      /- We erase proofs. -/
      return .erased
    if (← isTypeFormerType type) then
      /- Predicates are erased (e.g., `Eq`) -/
      if isPredicateType (← toLCNFType type) then
        return .erased
      else
        /- Types and Type formers are not put into A-normal form -/
        return .type (← toLCNFType e)
    else
      visitCore e

  /-- Giving `f` a constant `.const declName us`, convert `args` into `args'`, and return `.const declName us args'` -/
  visitAppDefaultConst (f : Expr) (args : Array Expr) : M Arg := do
    let .const declName us := f | unreachable!
    let args ← args.mapM visitAppArg
    letValueToArg <| .const declName us args

  /-- Eta expand if under applied, otherwise apply k -/
  etaIfUnderApplied (e : Expr) (arity : Nat) (k : M Arg) : M Arg := do
    let numArgs := e.getAppNumArgs
    if numArgs < arity then
      visit (← etaExpandN e (arity - numArgs))
    else
      k

  /--
  If `args.size == arity`, then just return `app`.
  Otherwise return
  ```
  let k := app
  k args[arity:]
  ```
  -/
  mkOverApplication (app : Arg) (args : Array Expr) (arity : Nat) : M Arg := do
    if args.size == arity then
      return app
    else
      match app with
      | .fvar f =>
        let mut argsNew := #[]
        for i in [arity : args.size] do
          argsNew := argsNew.push (← visitAppArg args[i]!)
        letValueToArg <| .fvar f argsNew
      | .erased | .type .. => return .erased

  /--
  Visit a `matcher`/`casesOn` alternative.
  -/
  visitAlt (ctorName : Name) (numParams : Nat) (e : Expr) : M (Expr × Alt) := do
    withNewScope do
      let mut (ps, e) ← visitBoundedLambda e numParams
      if ps.size < numParams then
        e ← etaExpandN e (numParams - ps.size)
        let (ps', e') ← ToLCNF.visitLambda e
        ps := ps ++ ps'
        e := e'
      /-
      Insert the free variable ids of fields that are type formers into `toAny`.
      Recall that we do not want to have "data" occurring in types.
      -/
      ps ← ps.mapM fun p => do
        let type ← inferType p.toExpr
        if (← isTypeFormerType type) then
          modify fun s => { s with toAny := s.toAny.insert p.fvarId }
        /-
        Recall that we may have dependent fields. Example:
        ```
        | ctor (α : Type u) (as : List α) => ...
        ```
        and we must use `applyToAny` to make sure the field `α` (which is data) does
        not occur in the type of `as : List α`.
        -/
        p.update (← applyToAny p.type)
      let c ← toCode (← visit e)
      let altType ← c.inferType
      return (altType, .alt ctorName ps c)

  visitCases (casesInfo : CasesInfo) (e : Expr) : M Arg :=
    etaIfUnderApplied e casesInfo.arity do
      let args := e.getAppArgs
      let mut resultType ← toLCNFType (← liftMetaM do Meta.inferType (mkAppN e.getAppFn args[:casesInfo.arity]))
      if casesInfo.numAlts == 0 then
        /- `casesOn` of an empty type. -/
        mkUnreachable resultType
      else
        let mut alts := #[]
        let typeName := casesInfo.declName.getPrefix
        let discr ← visitAppArg args[casesInfo.discrPos]!
        let .inductInfo indVal ← getConstInfo typeName | unreachable!
        match discr with
        | .erased | .type .. =>
          /-
          This can happen for inductive predicates that can eliminate into type (e.g., `And`, `Iff`).
          TODO: add support for them. Right now, we have hard-coded support for the ones defined at `Init`.
          -/
          throwError "unsupported `{casesInfo.declName}` application during code generation"
        | .fvar discrFVarId =>
          for i in casesInfo.altsRange, numParams in casesInfo.altNumParams, ctorName in indVal.ctors do
            let (altType, alt) ← visitAlt ctorName numParams args[i]!
            resultType := joinTypes altType resultType
            alts := alts.push alt
          let cases : Cases := { typeName, discr := discrFVarId, resultType, alts }
          let auxDecl ← mkAuxParam resultType
          pushElement (.cases auxDecl cases)
          let result := .fvar auxDecl.fvarId
          mkOverApplication result args casesInfo.arity

  visitCtor (arity : Nat) (e : Expr) : M Arg :=
    etaIfUnderApplied e arity do
      visitAppDefaultConst e.getAppFn e.getAppArgs

  visitQuotLift (e : Expr) : M Arg := do
    let arity := 6
    etaIfUnderApplied e arity do
      let mut args := e.getAppArgs
      let α := args[0]!
      let r := args[1]!
      let f ← visitAppArg args[3]!
      let q ← visitAppArg args[5]!
      let .const _ [u, _] := e.getAppFn | unreachable!
      let invq ← mkAuxLetDecl (.const ``Quot.lcInv [u] #[.type α, .type r, q])
      match f with
      | .erased => return .erased
      | .type _ => unreachable!
      | .fvar fvarId => mkOverApplication (← letValueToArg <| .fvar fvarId #[.fvar invq]) args arity

  visitEqRec (e : Expr) : M Arg :=
    let arity := 6
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let minor := if e.isAppOf ``Eq.rec || e.isAppOf ``Eq.ndrec then args[3]! else args[5]!
      let minor ← visit minor
      mkOverApplication minor args arity

  visitFalseRec (e : Expr) : M Arg :=
    let arity := 2
    etaIfUnderApplied e arity do
      let type ← toLCNFType (← liftMetaM do Meta.inferType e)
      mkUnreachable type

  visitAndIffRecCore (e : Expr) (minorPos : Nat) : M Arg :=
    let arity := 5
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let ha := mkLcProof args[0]! -- We should not use `lcErased` here since we use it to create a pre-LCNF Expr.
      let hb := mkLcProof args[1]!
      let minor := args[minorPos]!
      let minor := minor.beta #[ha, hb]
      visit (mkAppN minor args[arity:])

  visitNoConfusion (e : Expr) : M Arg := do
    let .const declName _ := e.getAppFn | unreachable!
    let typeName := declName.getPrefix
    let .inductInfo inductVal ← getConstInfo typeName | unreachable!
    let arity := inductVal.numParams + inductVal.numIndices + 1 /- motive -/ + 2 /- lhs/rhs-/ + 1 /- equality -/
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let lhs ← liftMetaM do Meta.whnf args[inductVal.numParams + inductVal.numIndices + 1]!
      let rhs ← liftMetaM do Meta.whnf args[inductVal.numParams + inductVal.numIndices + 2]!
      let lhs := lhs.toCtorIfLit
      let rhs := rhs.toCtorIfLit
      match lhs.isConstructorApp? (← getEnv), rhs.isConstructorApp? (← getEnv) with
      | some lhsCtorVal, some rhsCtorVal =>
        if lhsCtorVal.name == rhsCtorVal.name then
          etaIfUnderApplied e (arity+1) do
            let major := args[arity]!
            let major ← expandNoConfusionMajor major lhsCtorVal.numFields
            let major := mkAppN major args[arity+1:]
            visit major
        else
          let type ← toLCNFType (← liftMetaM <| Meta.inferType e)
          mkUnreachable type
      | _, _ =>
        throwError "code generator failed, unsupported occurrence of `{declName}`"

  expandNoConfusionMajor (major : Expr) (numFields : Nat) : M Expr := do
    match numFields with
    | 0 => return major
    | n+1 =>
      if let .lam _ d b _ := major then
        let proof := mkLcProof d
        expandNoConfusionMajor (b.instantiate1 proof) n
      else
        expandNoConfusionMajor (← etaExpandN major (n+1)) (n+1)

  visitProjFn (projInfo : ProjectionFunctionInfo) (e : Expr) : M Arg := do
    let typeName := projInfo.ctorName.getPrefix
    if isRuntimeBultinType typeName then
      let numArgs := e.getAppNumArgs
      let arity := projInfo.numParams + 1
      if numArgs < arity then
        visit (← etaExpandN e (arity - numArgs))
      else
        visitAppDefaultConst e.getAppFn e.getAppArgs
    else
      let .const declName us := e.getAppFn | unreachable!
      let info ← getConstInfo declName
      let f ← Core.instantiateValueLevelParams info us
      visit (f.beta e.getAppArgs)

  visitApp (e : Expr) : M Arg := do
    if let some (args, n, t, v, b) := e.letFunAppArgs? then
      visitCore <| mkAppN (.letE n t v b (nonDep := true)) args
    else if let .const declName _ := e.getAppFn then
      if declName == ``Quot.lift then
        visitQuotLift e
      else if declName == ``Quot.mk then
        visitCtor 3 e
      else if declName == ``Eq.casesOn || declName == ``Eq.rec || declName == ``Eq.ndrec then
        visitEqRec e
      else if declName == ``And.rec || declName == ``Iff.rec then
        visitAndIffRecCore e (minorPos := 3)
      else if declName == ``And.casesOn || declName == ``Iff.casesOn then
        visitAndIffRecCore e (minorPos := 4)
      else if declName == ``False.rec || declName == ``Empty.rec || declName == ``False.casesOn || declName == ``Empty.casesOn then
        visitFalseRec e
      else if let some casesInfo ← getCasesInfo? declName then
        visitCases casesInfo e
      else if let some arity ← getCtorArity? declName then
        visitCtor arity e
      else if isNoConfusion (← getEnv) declName then
        visitNoConfusion e
      else if let some projInfo ← getProjectionFnInfo? declName then
        visitProjFn projInfo e
      else
        e.withApp visitAppDefaultConst
    else
      e.withApp fun f args => do
        match (← visit f) with
        | .erased | .type .. => return .erased
        | .fvar fvarId =>
          let args ← args.mapM visitAppArg
          letValueToArg <| .fvar fvarId args

  visitLambda (e : Expr) : M Arg := do
    let b := etaReduceImplicit e
    /-
    Note: we don't want to eta-reduce arbitrary lambda expressions since it can
    affect the current inline heuristics. For example, suppose that `foo` is marked
    as `[inline]`. If we eta-reduce
    ```
    let f := fun b => foo a b
    ```
    we obtain the LCNF
    ```
    let f := foo a
    ```
    which will be inlined everywhere in the current implementation, if we don't eta-reduce,
    we obtain
    ```
    fun f b := foo a
    ```
    which will inline foo in the body of `f`, but will only inline `f` if it is small.
    -/
    if !b.isLambda && !mustEtaExpand (← getEnv) b then
      /-
      We use eta-reduction to make sure we avoid the overhead introduced by
      the implicit lambda feature when declaring instances.
      Example: `fun {α} => ReaderT.pure
      -/
      visit b
    else
      let funDecl ← withNewScope do
        let (ps, e) ← ToLCNF.visitLambda e
        let e ← visit e
        let c ← toCode e
        mkAuxFunDecl ps c
      pushElement (.fun funDecl)
      return .fvar funDecl.fvarId

  visitMData (_mdata : MData) (e : Expr) : M Arg := do
    visit e

  visitProj (s : Name) (i : Nat) (e : Expr) : M Arg := do
    match (← visit e) with
    | .erased | .type .. => return .erased
    | .fvar fvarId => letValueToArg <| .proj s i fvarId

  visitLet (e : Expr) (xs : Array Expr) : M Arg := do
    match e with
    | .letE binderName type value body _ =>
      let type := type.instantiateRev xs
      let value := value.instantiateRev xs
      if (← (liftMetaM <| Meta.isProp type) <||> isTypeFormerType type) then
        visitLet body (xs.push value)
      else
        let type' ← toLCNFType type
        let letDecl ← mkLetDecl binderName type value type' (← visit value)
        visitLet body (xs.push (.fvar letDecl.fvarId))
    | _ =>
      let e := e.instantiateRev xs
      visit e

end ToLCNF

export ToLCNF (toLCNF)

end Lean.Compiler.LCNF
