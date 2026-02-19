/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.AppBuilder
public import Lean.Compiler.CSimpAttr
public import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.LCNF.Bind
public import Lean.Compiler.NeverExtractAttr
import Lean.Meta.CasesInfo
import Lean.Meta.WHNF
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.LCNF.Util
import Init.Data.Format.Macro
import Init.Omega
import Lean.OriginalConstKind

public section
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
  | jp  (decl : FunDecl .pure)
  | fun (decl : FunDecl .pure)
  | let (decl : LetDecl .pure)
  | cases (p : Param .pure) (cases : Cases .pure)
  | unreach (p : Param .pure)
  deriving Inhabited

/--
State for `BindCasesM` monad
Mapping from `_alt.<idx>` variables to new join points
-/
abbrev BindCasesM.State := FVarIdMap (FunDecl .pure)

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
partial def bindCases (jpDecl : FunDecl .pure) (cases : Cases .pure) : CompilerM (Code .pure) := do
  let (alts, s) ← visitAlts cases.alts |>.run {}
  let resultType ← mkCasesResultType alts
  let result := .cases ⟨cases.typeName, resultType, cases.discr, alts⟩
  let result := s.foldl (init := result) fun result _ altJp => .jp altJp result
  return .jp jpDecl result
where
  visitAlts (alts : Array (Alt .pure)) : BindCasesM (Array (Alt .pure)) :=
    alts.mapM fun alt => return alt.updateCode (← go alt.getCode)

  findFun? (f : FVarId) : CompilerM (Option (FunDecl .pure)) := do
    if let some funDecl ← findFunDecl? (pu := .pure) f then
      return funDecl
    else if let some (.fvar f' #[]) ← findLetValue? (pu := .pure) f then
      findFun? f'
    else
      return none

  go (code : Code .pure) : BindCasesM (Code .pure) := do
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
                if let some altJp := (← get).get? f then
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
                  let mut subst : FVarSubst .pure := {}
                  let mut jpArgs := #[]
                  /- Remark: `funDecl.params.size` may be greater than `args.size`. -/
                  for param in funDecl.params[*...args.size] do
                    let type ← replaceExprFVars param.type subst (translator := true)
                    let paramNew ← mkAuxParam type
                    jpParams := jpParams.push paramNew
                    subst := subst.insert param.fvarId (.fvar paramNew.fvarId)
                    jpArgs := jpArgs.push (Arg.fvar paramNew.fvarId)
                  let letDecl ← mkAuxLetDecl (.fvar f jpArgs)
                  let jpValue := .let letDecl (.jmp jpDecl.fvarId #[.fvar letDecl.fvarId])
                  let altJp ← mkAuxJpDecl jpParams jpValue
                  modify fun map => map.insert f altJp
                  return .jmp altJp.fvarId args
          | _ => pure ()
      let k ← go k
      if let some altJp := (← get).get? decl.fvarId then
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
      return .cases ⟨c.typeName, resultType, c.discr, alts⟩
    | .return fvarId => return .jmp jpDecl.fvarId #[.fvar fvarId]
    | .jmp .. | .unreach .. => return code

def seqToCode (seq : Array Element) (k : Code .pure) : CompilerM (Code .pure) := do
  go seq seq.size k
where
  go (seq : Array Element) (i : Nat) (c : Code .pure) : CompilerM (Code .pure) := do
    if i > 0 then
      match seq[i-1]! with
      | .jp decl => go seq (i - 1) (.jp decl c)
      | .fun decl => go seq (i - 1) (.fun decl c)
      | .let decl => go seq (i - 1) (.let decl c)
      | .unreach _ =>
        let type ← c.inferType
        eraseCode c
        seq[*...i].forM fun
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
          result instead of a join point that takes a closure.
          -/
          eraseParam auxParam
          let auxFunDecl := ⟨auxParam.fvarId, auxParam.binderName, #[], auxParam.type, .cases cases⟩
          modifyLCtx fun lctx => lctx.addFunDecl auxFunDecl
          let auxFunDecl ← auxFunDecl.etaExpand
          go seq (i - 1) (.fun auxFunDecl c)
        else
          /- Create a join point for `c` and jump to it from `cases` -/
          let jpDecl ← mkAuxJpDecl' auxParam c
          go seq (i - 1) (← bindCases jpDecl cases)
    else
      return c

structure Context where
  /--
  Whether uses of `noncomputable` defs should be ignored; used in contexts that will be erased
  eventually.
  -/
  ignoreNoncomputable : Bool := false

structure State where
  /-- Local context containing the original Lean types (not LCNF ones). -/
  lctx : LocalContext := {}
  /-- Cache from Lean regular expression to LCNF argument. -/
  cache : PHashMap Expr (Arg .pure) := {}
  /--
  Determines whether caching has been disabled due to finding a use of
  a constant marked with `never_extract`.
  -/
  shouldCache : Bool := true
  /-- `toLCNFType` cache -/
  typeCache : Std.HashMap Expr Expr := {}
  /-- isTypeFormerType cache -/
  isTypeFormerTypeCache : Std.HashMap Expr Bool := {}
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

abbrev M := ReaderT Context <| StateRefT State CompilerM

@[inline] def liftMetaM (x : MetaM α) : M α := do
  x.run' { lctx := (← get).lctx }

/-- Add LCNF element to the current sequence -/
def pushElement (elem : Element) : M Unit := do
  modify fun s => { s with seq := s.seq.push elem }

def mkUnreachable (type : Expr) : M (Arg .pure) := do
  let p ← mkAuxParam type
  pushElement (.unreach p)
  return .fvar p.fvarId

def mkAuxLetDecl (e : LetValue .pure) (prefixName := `_x) : M FVarId := do
  match e with
  | .fvar fvarId #[] => return fvarId
  | _ =>
    let letDecl ← mkLetDecl (← mkFreshBinderName prefixName) (← e.inferType) e
    pushElement (.let letDecl)
    return letDecl.fvarId

def letValueToArg (e : LetValue .pure) (prefixName := `_x) : M (Arg .pure) :=
  return .fvar (← mkAuxLetDecl e prefixName)

/-- Create `Code` that executes the current `seq` and then returns `result` -/
def toCode (result : Arg .pure) : M (Code .pure) := do
  match result with
  | .fvar fvarId => seqToCode (← get).seq (.return fvarId)
  | .erased | .type .. =>
    let fvarId ← mkAuxLetDecl .erased
    seqToCode (← get).seq (.return fvarId)

def run (x : M α) : CompilerM α :=
  x.run {} |>.run' {}

/--
Return true iff `type` is `Sort _` or `As → Sort _`.
-/
private partial def isTypeFormerType (type : Expr) : M Bool := do
  match quick (← getEnv) type with
  | .true => return true
  | .false => return false
  | .undef =>
    if let some result := (← get).isTypeFormerTypeCache[type]? then
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
    | .fvar fvarId => if toAny.contains fvarId then some anyExpr else none
    | _ => none

def toLCNFType (type : Expr) : M Expr := do
  match (← get).typeCache[type]? with
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
def mkParam (binderName : Name) (type : Expr) : M (Param .pure) := do
  let binderName ← cleanupBinderName binderName
  let borrow := isMarkedBorrowed type
  let type' ← toLCNFType type
  let param ← LCNF.mkParam binderName type' borrow
  modify fun s => { s with lctx  := s.lctx.mkLocalDecl param.fvarId binderName type .default }
  return param

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (type' : Expr) (arg : Arg .pure)
    (nondep : Bool) : M (LetDecl .pure) := do
  let binderName ← cleanupBinderName binderName
  let value' ← match arg with
    | .fvar fvarId => pure <| .fvar fvarId #[]
    | .erased | .type .. => pure .erased
  let letDecl ← LCNF.mkLetDecl binderName type' value'
  modify fun s => { s with
    lctx := s.lctx.mkLetDecl letDecl.fvarId binderName type value nondep
    seq := s.seq.push <| .let letDecl
  }
  return letDecl

def visitLambda (e : Expr) : M (Array (Param .pure) × Expr) :=
  go e #[] #[]
where
  go (e : Expr) (xs : Array Expr) (ps : Array (Param .pure)) := do
    if let .lam binderName type body _ := e then
      let type := type.instantiateRev xs
      let p ← mkParam binderName type
      go body (xs.push p.toExpr) (ps.push p)
    else
      return (ps, e.instantiateRev xs)

def visitBoundedLambda (e : Expr) (n : Nat) : M (Array (Param .pure) × Expr) :=
  go e n #[] #[]
where
  go (e : Expr) (n : Nat) (xs : Array Expr) (ps : Array (Param .pure)) := do
    if n == 0 then
      return (ps, e.instantiateRev xs)
    else if let .lam binderName type body _ := e then
      let type := type.instantiateRev xs
      let p ← mkParam binderName type
      go body (n-1) (xs.push p.toExpr) (ps.push p)
    else
      return (ps, e.instantiateRev xs)

/--
Given `e` and `args` where `mkAppN e (args.map (·.toExpr))` is not necessarily well-typed
(because of dependent typing), returns `e.beta args'` where `args'` are new local declarations each
assigned to a value in `args` with adjusted type (such that the resulting expression is well-typed).
-/
def mkTypeCorrectApp (e : Expr) (args : Array (Arg .pure)) : M Expr := do
  if args.isEmpty then
    return e
  let type ← liftMetaM <| do
    let type ← Meta.inferType e
    if type.getNumHeadForalls < args.size then
      -- expose foralls
      Meta.forallBoundedTelescope type args.size Meta.mkForallFVars
    else
      return type
  go type 0 #[]
where
  go (type : Expr) (i : Nat) (xs : Array Expr) : M Expr := do
    if h : i < args.size then
      match type with
      | .forallE nm t b bi =>
        let t := t.instantiateRev xs
        let arg := args[i]
        if ← liftMetaM <| Meta.isProp t then
          go b (i + 1) (xs.push (mkLcProof t))
        else
          let decl ← mkLetDecl nm t arg.toExpr (← arg.inferType) arg (nondep := true)
          go b (i + 1) (xs.push (.fvar decl.fvarId))
      | _ => liftMetaM <| Meta.throwFunctionExpected (mkAppN e xs)
    else
      return e.beta xs

def mustEtaExpand (env : Environment) (e : Expr) : Bool :=
  if let .const declName _ := e.getAppFn then
    match env.find? declName with
    | some (.recInfo ..) | some (.ctorInfo ..) | some (.quotInfo ..) => true
    | _ => isCasesOnLike env declName || isNoConfusion env declName ||
           env.isProjectionFn declName || declName == ``Eq.ndrec
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

private def checkComputable (ref : Name) : M Unit := do
  if (← read).ignoreNoncomputable then
    return
  if ref matches ``Quot.mk | ``Quot.lift || isExtern (← getEnv) ref || (getImplementedBy? (← getEnv) ref).isSome then
    return
  if isNoncomputable (← getEnv) ref then
    throwNamedError lean.dependsOnNoncomputable m!"failed to compile definition, consider marking it as 'noncomputable' because it depends on '{.ofConstName ref}', which is 'noncomputable'"
  else if getOriginalConstKind? (← getEnv) ref matches some .axiom | some .quot | some .induct | some .thm then
    throwNamedError lean.dependsOnNoncomputable f!"`{ref}` not supported by code generator; consider marking definition as `noncomputable`"

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
  | .natVal val => .nat val
  | .strVal val => .str val

/--
Put the given expression in `LCNF`.

- Nested proofs are replaced with `lcProof`-applications.
- Eta-expand applications of declarations that satisfy `shouldEtaExpand`.
- Put computationally relevant expressions in A-normal form.
-/
partial def toLCNF (e : Expr) : CompilerM (Code .pure) := do
  run do toCode (← visit e)
where
  visitCore (e : Expr) : M (Arg .pure) := withIncRecDepth do
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
    modify fun s => if s.shouldCache then { s with cache := s.cache.insert e r } else s
    return r

  visit (e : Expr) : M (Arg .pure) := withIncRecDepth do
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

  visitLit (lit : Literal) : M (Arg .pure) :=
    letValueToArg (.lit (litToValue lit))

  visitAppArg (e : Expr) : M (Arg .pure) := do
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
  visitAppDefaultConst (f : Expr) (args : Array Expr) : M (Arg .pure) := do
    let env ← getEnv
    let .const declName us ← CSimp.replaceConstant env f | unreachable!
    let args ← args.mapM visitAppArg
    if hasNeverExtractAttribute env declName then
      modify fun s => {s with shouldCache := false }
    letValueToArg <| .const declName us args

  /-- Eta expand if under applied, otherwise apply k -/
  etaIfUnderApplied (e : Expr) (arity : Nat) (k : Unit → M (Arg .pure)) : M (Arg .pure) := do
    let numArgs := e.getAppNumArgs
    if numArgs < arity then
      visit (← etaExpandN e (arity - numArgs))
    else
      k ()

  /--
  If `args.size == arity`, then just return `app`.
  Otherwise return
  ```
  let k := app
  k args[arity...*]
  ```
  -/
  mkOverApplication (app : Arg .pure) (args : Array Expr) (arity : Nat) : M (Arg .pure) := do
    if args.size == arity then
      return app
    else
      match app with
      | .fvar f =>
        let mut argsNew := #[]
        for h : i in arity...args.size do
          argsNew := argsNew.push (← visitAppArg args[i])
        letValueToArg <| .fvar f argsNew
      | .erased | .type .. => return .erased

  /--
  Visit a `matcher`/`casesOn` alternative.
  -/
  visitAlt (casesAltInfo : CasesAltInfo) (e : Expr) (overArgs : Array (Arg .pure)) :
      M (Expr × (Alt .pure)) := do
    withNewScope do
    match casesAltInfo with
    | .default numHyps =>
      let e := mkAppN e (Array.replicate numHyps erasedExpr)
      let e ← mkTypeCorrectApp e overArgs
      let c ← toCode (← visit e)
      let altType ← c.inferType
      return (altType, .default c)
    | .ctor ctorName numParams =>
      let mut (ps, e) ← visitBoundedLambda e numParams
      if ps.size < numParams then
        e ← etaExpandN e (numParams - ps.size)
        let (ps', e') ← ToLCNF.visitLambda e
        ps := ps ++ ps'
        e := e'
      e ← mkTypeCorrectApp e overArgs
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

  visitCases (casesInfo : CasesInfo) (e : Expr) : M (Arg .pure) :=
    etaIfUnderApplied e casesInfo.arity fun _ => do
      let args := e.getAppArgs
      let overArgs ← (args.drop casesInfo.arity).mapM visitAppArg
      let mut resultType ← toLCNFType (← liftMetaM do Meta.inferType (mkAppN e.getAppFn args))
      let typeName := casesInfo.indName
      let .inductInfo indVal ← getConstInfo typeName | unreachable!
      if casesInfo.numAlts == 0 then
        /- `casesOn` of an empty type. -/
        mkUnreachable resultType
      else if ← Meta.MetaM.run' <| Meta.isInductivePredicateVal indVal then
        assert! casesInfo.numAlts == 1
        let numParams := indVal.numParams
        let numIndices := indVal.numIndices
        let .ctorInfo ctorVal ← getConstInfo indVal.ctors[0]! | unreachable!
        let .ctor _ numCtorFields := casesInfo.altNumParams[0]! | unreachable!
        let fieldArgs : Array Expr ←
          Meta.MetaM.run' <| Meta.forallTelescope ctorVal.type fun params indApp => do
            let ⟨indAppF, indAppArgs⟩ := indApp.getAppFnArgs
            assert! indAppF == typeName
            -- TODO: We only use `toArray` so that we get access to `findIdx?`. Remove
            -- this when that changes.
            let indexArgs := indAppArgs[numParams...*].toArray

            let mut fieldArgs := .emptyWithCapacity numCtorFields
            for i in *...numCtorFields do
              let p := params[numParams + i]!
              let fieldArg ← if let some indexIdx := indexArgs.findIdx? (· == p) then
                pure args[numParams + 1 + indexIdx]!
              else
                pure <| mkLcProof (← p.fvarId!.getType)
              fieldArgs := fieldArgs.push fieldArg
            return fieldArgs
        let f := args[casesInfo.altsRange.lower]!
        visit (mkAppN (mkAppN f fieldArgs) (overArgs.map (·.toExpr)))
      else
        let mut alts := #[]
        let discr ← visitAppArg args[casesInfo.discrPos]!
        let discrFVarId ← match discr with
          | .fvar discrFVarId => pure discrFVarId
          | .erased | .type .. => mkAuxLetDecl .erased
        for i in casesInfo.altsRange, numParams in casesInfo.altNumParams do
          let (altType, alt) ← visitAlt numParams args[i]! overArgs
          resultType := joinTypes altType resultType
          alts := alts.push alt
        let cases := ⟨typeName, resultType, discrFVarId, alts⟩
        let auxDecl ← mkAuxParam resultType
        pushElement (.cases auxDecl cases)
        return .fvar auxDecl.fvarId

  visitCtor (arity : Nat) (e : Expr) : M (Arg .pure) :=
    etaIfUnderApplied e arity fun _ => do
      let f := e.getAppFn
      let args := e.getAppArgs
      let env ← getEnv
      let .const declName us ← CSimp.replaceConstant env f | unreachable!
      let ctorInfo? ← isCtor? declName
      let args ← args.mapIdxM fun idx arg =>
        -- We can rely on `toMono` erasing ctor params eventually; we do not do so here so that type
        -- inference on the value is preserved.
        withReader (fun ctx =>
            { ignoreNoncomputable := ctx.ignoreNoncomputable || ctorInfo?.any (idx < ·.numParams) }) do
          visitAppArg arg
      if hasNeverExtractAttribute env declName then
        modify fun s => {s with shouldCache := false }
      letValueToArg <| .const declName us args

  visitQuotMk (e : Expr) : M (Arg .pure)  := do
    let arity := 3
    etaIfUnderApplied e arity fun _ => do
      let args := e.getAppArgs
      visit args[2]!

  visitQuotLift (e : Expr) : M (Arg .pure)  := do
    let arity := 6
    etaIfUnderApplied e arity fun _ => do
      let args := e.getAppArgs
      visit (mkApp args[3]! args[5]!)

  visitEqRec (e : Expr) : M (Arg .pure) :=
    let arity := 6
    etaIfUnderApplied e arity fun _ => do
      let args := e.getAppArgs
      let minor := if e.isAppOf ``Eq.rec || e.isAppOf ``Eq.ndrec then args[3]! else args[5]!
      let minor ← visit minor
      mkOverApplication minor args arity

  visitHEqRec (e : Expr) : M (Arg .pure) :=
    let arity := 7
    etaIfUnderApplied e arity fun _ => do
      let args := e.getAppArgs
      let minor := if e.isAppOf ``HEq.rec || e.isAppOf ``HEq.ndrec then args[3]! else args[6]!
      let minor ← visit minor
      mkOverApplication minor args arity

  visitFalseRec (e : Expr) : M (Arg .pure) :=
    let arity := 2
    etaIfUnderApplied e arity fun _ => do
      let type ← toLCNFType (← liftMetaM do Meta.inferType e)
      mkUnreachable type

  visitLcUnreachable (e : Expr) : M (Arg .pure) :=
    let arity := 1
    etaIfUnderApplied e arity fun _ => do
      let type ← toLCNFType (← liftMetaM do Meta.inferType e)
      mkUnreachable type

  visitAndIffRecCore (e : Expr) (minorPos : Nat) : M (Arg .pure) :=
    let arity := 5
    etaIfUnderApplied e arity fun _ => do
      let args := e.getAppArgs
      let ha := mkLcProof args[0]! -- We should not use `lcErased` here since we use it to create a pre-LCNF Expr.
      let hb := mkLcProof args[1]!
      let minor := args[minorPos]!
      let minor := minor.beta #[ha, hb]
      visit (mkAppN minor args[arity...*])

  visitNoConfusion (e : Expr) : M (Arg .pure) := do
    let .const declName _ := e.getAppFn | unreachable!
    let info := getNoConfusionInfo (← getEnv) declName
    let typeName := declName.getPrefix
    etaIfUnderApplied e info.arity fun _ => do
      let args := e.getAppArgs
      let visitMajor (numNonPropFields : Nat) := do
        etaIfUnderApplied e (info.arity+1) fun _ => do
          let major := args[info.arity]!
          let major ← expandNoConfusionMajor major numNonPropFields
          let major := mkAppN major args[(info.arity+1)...*]
          visit major

      match info with
      | .regular _ lhsPos rhsPos =>
        let lhs ← liftMetaM do Meta.whnf args[lhsPos]!
        let rhs ← liftMetaM do Meta.whnf args[rhsPos]!
        let lhs ← liftMetaM lhs.toCtorIfLit
        let rhs ← liftMetaM rhs.toCtorIfLit
        match (← liftMetaM <| Meta.isConstructorApp? lhs), (← liftMetaM <| Meta.isConstructorApp? rhs) with
        | some lhsCtorVal, some rhsCtorVal =>
          if lhsCtorVal.name == rhsCtorVal.name then
            let numNonPropFields ← liftMetaM <| Meta.forallTelescope lhsCtorVal.type fun params _ =>
              params[lhsCtorVal.numParams...*].foldlM (init := 0) fun n param => do
                let type ← param.fvarId!.getType
                return if !(← Meta.isProp type) then n + 1 else n
            visitMajor numNonPropFields
          else
            let type ← toLCNFType (← liftMetaM <| Meta.inferType e)
            mkUnreachable type
        | _, _ =>
          throwError "code generator failed, unsupported occurrence of `{.ofConstName declName}`"
      | .perCtor _ numNonPropFields =>
        visitMajor numNonPropFields

  expandNoConfusionMajor (major : Expr) (numFields : Nat) : M Expr := do
    match numFields with
    | 0 => return major
    | n+1 =>
      if let .lam _ d b _ := major then
        let proof := mkLcProof d
        expandNoConfusionMajor (b.instantiate1 proof) n
      else
        expandNoConfusionMajor (← etaExpandN major (n+1)) (n+1)

  visitProjFn (projInfo : ProjectionFunctionInfo) (e : Expr) : M (Arg .pure) := do
    let typeName := projInfo.ctorName.getPrefix
    if isRuntimeBuiltinType typeName then
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

  visitApp (e : Expr) : M (Arg .pure) := do
    if let .const declName us ← CSimp.replaceConstant (← getEnv) e.getAppFn then
      checkComputable declName
      if declName == ``Quot.lift then
        visitQuotLift e
      else if declName == ``Quot.mk then
        visitQuotMk e
      else if declName == ``Eq.rec || declName == ``Eq.recOn || declName == ``Eq.ndrec then
        visitEqRec e
      else if declName == ``HEq.rec || declName == ``HEq.ndrec then
        visitHEqRec e
      else if declName == ``And.rec || declName == ``Iff.rec then
        visitAndIffRecCore e (minorPos := 3)
      else if declName == ``False.rec || declName == ``Empty.rec then
        visitFalseRec e
      else if declName == ``lcUnreachable then
        visitLcUnreachable e
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

  visitLambda (e : Expr) : M (Arg .pure) := do
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

  visitMData (_mdata : MData) (e : Expr) : M (Arg .pure) := do
    visit e

  visitProj (s : Name) (i : Nat) (e : Expr) : M (Arg .pure) := do
    if isRuntimeBuiltinType s then
      let structInfo := getStructureInfo (← getEnv) s
      let projExpr ← liftMetaM <| Meta.mkProjection e structInfo.fieldNames[i]!
      visitApp projExpr
    else
      match (← visit e) with
      | .erased | .type .. => return .erased
      | .fvar fvarId => letValueToArg <| .proj s i fvarId

  visitLet (e : Expr) (xs : Array Expr) : M (Arg .pure) := do
    match e with
    | .letE binderName type value body nondep =>
      let type := type.instantiateRev xs
      let value := value.instantiateRev xs
      if (← (liftMetaM <| Meta.isProp type) <||> isTypeFormerType type) then
        visitLet body (xs.push value)
      else
        let type' ← toLCNFType type
        let letDecl ← mkLetDecl binderName type value type' (← visit value) nondep
        visitLet body (xs.push (.fvar letDecl.fvarId))
    | _ =>
      let e := e.instantiateRev xs
      visit e

end ToLCNF

export ToLCNF (toLCNF)

end Lean.Compiler.LCNF
