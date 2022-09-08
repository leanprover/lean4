/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ProjFns
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
  | cases (fvarId : FVarId) (cases : Cases)
  | unreach (fvarId : FVarId)
  deriving Inhabited

/-- State for `BindCasesM` monad -/
structure BindCasesM.State where
  /-- New auxiliary join points. -/
  jps : Array FunDecl := #[]
  /-- Mapping from `_alt.<idx>` variables to new join points -/
  map : FVarIdMap FVarId := {}

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
  let mut result := .cases { cases with alts, resultType }
  for decl in s.jps do
    result := .jp decl result
  return .jp jpDecl result
where
  visitAlts (alts : Array Alt) : BindCasesM (Array Alt) :=
    alts.mapM fun alt => return alt.updateCode (← go alt.getCode)

  findFun? (f : FVarId) : CompilerM (Option FunDecl) := do
    if let some funDecl ← findFunDecl? f then
      return funDecl
    else if let .ldecl (value := .fvar f') .. ← getLocalDecl f then
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
        if decl.fvarId == fvarId && decl.value.isApp && decl.value.getAppFn.isFVar then
          let f := decl.value.getAppFn.fvarId!
          let localDecl ← getLocalDecl f
          if localDecl.userName.getPrefix == `_alt then
            if let some funDecl ← findFun? f then
              let args := decl.value.getAppArgs
              eraseFVar decl.fvarId
              if let some altJp := (← get).map.find? f then
                /- We already have an auxiliary join point for `f`, then, we just use it. -/
                return .jmp altJp args
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
                  let type ← replaceExprFVars param.type subst
                  let paramNew ← mkAuxParam type
                  jpParams := jpParams.push paramNew
                  let arg := .fvar paramNew.fvarId
                  subst := subst.insert param.fvarId arg
                  jpArgs := jpArgs.push arg
                let letDecl ← mkAuxLetDecl (mkAppN decl.value.getAppFn jpArgs)
                let jpValue := .let letDecl (.jmp jpDecl.fvarId #[.fvar letDecl.fvarId])
                let altJp ← mkAuxJpDecl jpParams jpValue
                modify fun { jps, map } => {
                  jps := jps.push altJp
                  map := map.insert f altJp.fvarId
                }
                return .jmp altJp.fvarId args
      return .let decl (← go k)
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

def seqToCode (seq : Array Element) (e : Expr) : CompilerM Code := do
  if let .fvar fvarId := e then
    go seq seq.size (.return fvarId)
  else
    let decl ← mkAuxLetDecl e
    let seq := seq.push (.let decl)
    go seq seq.size (.return decl.fvarId)
where
  go (seq : Array Element) (i : Nat) (c : Code) : CompilerM Code := do
    if i > 0 then
      match seq[i-1]! with
      | .jp decl => go seq (i - 1) (.jp decl c)
      | .fun decl => go seq (i - 1) (.fun decl c)
      | .let decl => go seq (i - 1) (.let decl c)
      | .unreach _ =>
        let type ← c.inferType
        eraseFVarsAt c
        seq[:i].forM fun
          | .let decl | .jp decl | .fun decl => eraseFVar decl.fvarId
          | .cases _ cs => eraseFVarsAt (.cases cs)
          | .unreach fvarId => eraseFVar fvarId
        return .unreach type
      | .cases fvarId cases =>
        if let .return fvarId' := c then
          if fvarId == fvarId' then
            eraseFVar fvarId
            go seq (i - 1) (.cases cases)
          else
            -- `cases` is dead code
            go seq (i - 1) c
        else
          /- Create a join point for `c` and jump to it from `cases` -/
          let jpDecl ← mkAuxJpDecl' fvarId c
          go seq (i - 1) (← bindCases jpDecl cases)
    else
      return c

structure State where
  /-- Local context containing the original Lean types (not LCNF ones). -/
  lctx : LocalContext := {}
  /-- Cache from Lean regular expression to LCNF expression. -/
  cache : Std.PHashMap Expr Expr := {}
  /-- `toLCNFType` cache -/
  typeCache : Std.HashMap Expr Expr := {}
  /-- isTypeFormerType cache -/
  isTypeFormerTypeCache : Std.HashMap Expr Bool := {}
  /-- LCNF sequence, we chain it to create a LCNF `Code` object. -/
  seq : Array Element := #[]

abbrev M := StateRefT State CompilerM

@[inline] def liftMetaM (x : MetaM α) : M α := do
  x.run' { lctx := (← get).lctx }

/-- Create `Code` that executes the current `seq` and then returns `e` -/
def toCode (e : Expr) : M Code := do
  seqToCode (← get).seq e

/-- Add LCNF element to the current sequence -/
def pushElement (elem : Element) : M Unit := do
  modify fun s => { s with seq := s.seq.push elem }

def mkUnreachable (type : Expr) : M Expr := do
  let p ← mkAuxParam type
  pushElement (.unreach p.fvarId)
  return .fvar p.fvarId

def mkAuxLetDecl (e : Expr) (prefixName := `_x) : M Expr := do
  if e.isFVar then
    return e
  else
    let letDecl ← mkLetDecl (← mkFreshBinderName prefixName) (← inferType e) e
    pushElement (.let letDecl)
    return .fvar letDecl.fvarId

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

def toLCNFType (type : Expr) : M Expr := do
  match (← get).typeCache.find? type with
  | some type' => return type'
  | none =>
    let type' ← liftMetaM <| LCNF.toLCNFType type
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
  let type' ← toLCNFType type
  let param ← LCNF.mkParam binderName type'
  modify fun s => { s with lctx  := s.lctx.mkLocalDecl param.fvarId binderName type .default }
  return param

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (type' : Expr) (value' : Expr) : M LetDecl := do
  let binderName ← cleanupBinderName binderName
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
    | _ => isCasesOnRecursor env declName || isNoConfusion env declName || env.isProjectionFn declName
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
Put the given expression in `LCNF`.

- Nested proofs are replaced with `lcProof`-applications.
- Eta-expand applications of declarations that satisfy `shouldEtaExpand`.
- Put computationally relevant expressions in A-normal form.
-/
partial def toLCNF (e : Expr) : CompilerM Code := do
  run do
    let e ← visit e
    toCode e
where
  visitCore (e : Expr) : M Expr := withIncRecDepth do
    if let some e := (← get).cache.find? e then
      return e
    let r ← match e with
      | .app ..     => visitApp e
      | .const ..   => visitApp e
      | .proj s i e => visitProj s i e
      | .mdata d e  => visitMData d e
      | .lam ..     => visitLambda e
      | .letE ..    => visitLet e #[]
      | .lit ..     => mkAuxLetDecl e
      | .forallE .. => unreachable!
      | .mvar ..    => throwError "unexpected occurrence of metavariable in code generator{indentExpr e}"
      | .bvar ..    => unreachable!
      | _           => pure e
    modify fun s => { s with cache := s.cache.insert e r }
    return r

  visit (e : Expr) : M Expr := withIncRecDepth do
    if isLCProof e then
      return mkConst ``lcErased
    let type ← liftMetaM <| Meta.inferType e
    if (← liftMetaM <| Meta.isProp type) then
      /- We erase proofs. -/
      return mkConst ``lcErased
    if (← isTypeFormerType type) then
      /-
      We erase type formers unless they occur as application arguments.
      Recall that we usually do not generate code for functions that return type,
      by this branch can be reachable if we cannot establish whether the function produces a type or not.

      See `visitAppArg`
      -/
      return mkConst ``lcErased
    visitCore e

  visitAppArg (e : Expr) : M Expr := do
    if isLCProof e then
      return mkConst ``lcErased
    let type ← liftMetaM <| Meta.inferType e
    if (← liftMetaM <| Meta.isProp type) then
      /- We erase proofs. -/
      return mkConst ``lcErased
    if (← isTypeFormerType type) then
      /- Types and Type formers are not put into A-normal form -/
      toLCNFType e
    else
      visitCore e

  /-- Visit args, and return `f args` -/
  visitAppDefault (f : Expr) (args : Array Expr) : M Expr := do
    if f.isConstOf ``lcErased then
      return f
    else
      let args ← args.mapM visitAppArg
      mkAuxLetDecl <| mkAppN f args

  /-- Eta expand if under applied, otherwise apply k -/
  etaIfUnderApplied (e : Expr) (arity : Nat) (k : M Expr) : M Expr := do
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
  mkOverApplication (app : Expr) (args : Array Expr) (arity : Nat) : M Expr := do
    if args.size == arity then
      mkAuxLetDecl app
    else
    let k ← mkAuxLetDecl app
    let mut args := args
    for i in [arity : args.size] do
      args ← args.modifyM i visitAppArg
    mkAuxLetDecl (mkAppN k args[arity:])

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
      let c ← toCode (← visit e)
      let eType ← inferType e
      return (eType, .alt ctorName ps c)

  visitCases (casesInfo : CasesInfo) (e : Expr) : M Expr :=
    etaIfUnderApplied e casesInfo.arity do
      let args := e.getAppArgs
      let mut alts := #[]
      let typeName := casesInfo.declName.getPrefix
      let mut resultType ← toLCNFType (← liftMetaM do Meta.inferType (mkAppN e.getAppFn args[:casesInfo.arity]))
      let discr ← visitAppArg args[casesInfo.discrPos]!
      let .inductInfo indVal ← getConstInfo typeName | unreachable!
      for i in casesInfo.altsRange, numParams in casesInfo.altNumParams, ctorName in indVal.ctors do
        let (altType, alt) ← visitAlt ctorName numParams args[i]!
        unless compatibleTypes altType resultType do
          resultType := anyTypeExpr
        alts := alts.push alt
      let cases : Cases := { typeName, discr := discr.fvarId!, resultType, alts }
      let auxDecl ← mkAuxParam resultType
      pushElement (.cases auxDecl.fvarId cases)
      let result := .fvar auxDecl.fvarId
      if args.size == casesInfo.arity then
        return result
      else
        mkOverApplication result args casesInfo.arity

  visitCtor (arity : Nat) (e : Expr) : M Expr :=
    etaIfUnderApplied e arity do
      visitAppDefault e.getAppFn e.getAppArgs

  visitQuotLift (e : Expr) : M Expr := do
    let arity := 6
    etaIfUnderApplied e arity do
      let mut args := e.getAppArgs
      let α := args[0]!
      let r := args[1]!
      let f ← visitAppArg args[3]!
      let q ← visitAppArg args[5]!
      let .const _ [u, _] := e.getAppFn | unreachable!
      let invq ← mkAuxLetDecl (mkApp3 (.const ``Quot.lcInv [u]) α r q)
      let r := mkApp f invq
      mkOverApplication r args arity

  visitEqRec (e : Expr) : M Expr :=
    let arity := 6
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let f := e.getAppFn
      let recType ← toLCNFType (← liftMetaM do Meta.inferType (mkAppN f args[:arity]))
      let minor := if e.isAppOf ``Eq.rec || e.isAppOf ``Eq.ndrec then args[3]! else args[5]!
      let minor ← visit minor
      let minorType ← inferType minor
      let cast ← if compatibleTypes minorType recType then
        -- Recall that many types become compatible after LCNF conversion
        -- Example: `Fin 10` and `Fin n`
        pure minor
      else
        mkLcCast (← mkAuxLetDecl minor) recType
      mkOverApplication cast args arity

  visitFalseRec (e : Expr) : M Expr :=
    let arity := 2
    etaIfUnderApplied e arity do
      let type ← toLCNFType (← liftMetaM do Meta.inferType e)
      mkUnreachable type

  visitAndRec (e : Expr) : M Expr :=
    let arity := 5
    etaIfUnderApplied e arity do
      let args := e.getAppArgs
      let ha := mkLcProof args[0]! -- We should not use `lcErased` here since we use it to create a pre-LCNF Expr.
      let hb := mkLcProof args[1]!
      let minor := if e.isAppOf ``And.rec then args[3]! else args[4]!
      let minor := minor.beta #[ha, hb]
      visit (mkAppN minor args[arity:])

  visitNoConfusion (e : Expr) : M Expr := do
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
          mkUnreachable (← inferType e)
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

  visitProjFn (projInfo : ProjectionFunctionInfo) (e : Expr) : M Expr := do
    let typeName := projInfo.ctorName.getPrefix
    if isRuntimeBultinType typeName then
      let numArgs := e.getAppNumArgs
      let arity := projInfo.numParams + 1
      if numArgs < arity then
        visit (← etaExpandN e (arity - numArgs))
      else
        visitAppDefault e.getAppFn e.getAppArgs
    else
      let .const declName us := e.getAppFn | unreachable!
      let info ← getConstInfo declName
      let f ← Core.instantiateValueLevelParams info us
      visit (f.beta e.getAppArgs)

  visitApp (e : Expr) : M Expr := do
    if let .const declName _ := e.getAppFn then
      if declName == ``Quot.lift then
        visitQuotLift e
      else if declName == ``Quot.mk then
        visitCtor 3 e
      else if declName == ``Eq.casesOn || declName == ``Eq.rec || declName == ``Eq.ndrec then
        visitEqRec e
      else if declName == ``And.rec || declName == ``And.casesOn then
        visitAndRec e
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
        e.withApp visitAppDefault
    else
      e.withApp fun f args => do visitAppDefault (← visit f) args

  visitLambda (e : Expr) : M Expr := do
    let b := e.eta
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

  visitMData (mdata : MData) (e : Expr) : M Expr := do
    if isCompilerRelevantMData mdata then
      mkAuxLetDecl <| .mdata mdata (← visit e)
    else
      visit e

  visitProj (s : Name) (i : Nat) (e : Expr) : M Expr := do
    mkAuxLetDecl <| .proj s i (← visit e)

  visitLet (e : Expr) (xs : Array Expr) : M Expr := do
    match e with
    | .letE binderName type value body _ =>
      let type := type.instantiateRev xs
      let value := value.instantiateRev xs
      if (← (liftMetaM <| Meta.isProp type) <||> isTypeFormerType type) then
        visitLet body (xs.push value)
      else
        let type' ← toLCNFType type
        let value' ← visit value
        let letDecl ← mkLetDecl binderName type value type' value'
        visitLet body (xs.push (.fvar letDecl.fvarId))
    | _ =>
      let e := e.instantiateRev xs
      visit e

end ToLCNF

export ToLCNF (toLCNF)

end Lean.Compiler.LCNF