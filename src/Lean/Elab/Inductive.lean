/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExprWhere
import Lean.Util.ReplaceLevel
import Lean.Util.ReplaceExpr
import Lean.Util.CollectLevelParams
import Lean.Meta.Constructions
import Lean.Meta.CollectFVars
import Lean.Meta.SizeOf
import Lean.Meta.Injective
import Lean.Meta.IndPredBelow
import Lean.Elab.Command
import Lean.Elab.ComputedFields
import Lean.Elab.DefView
import Lean.Elab.DeclUtil
import Lean.Elab.Deriving.Basic

namespace Lean.Elab.Command
open Meta

builtin_initialize
  registerTraceClass `Elab.inductive

def checkValidInductiveModifier [Monad m] [MonadError m] (modifiers : Modifiers) : m Unit := do
  if modifiers.isNoncomputable then
    throwError "invalid use of 'noncomputable' in inductive declaration"
  if modifiers.isPartial then
    throwError "invalid use of 'partial' in inductive declaration"

def checkValidCtorModifier [Monad m] [MonadError m] (modifiers : Modifiers) : m Unit := do
  if modifiers.isNoncomputable then
    throwError "invalid use of 'noncomputable' in constructor declaration"
  if modifiers.isPartial then
    throwError "invalid use of 'partial' in constructor declaration"
  if modifiers.isUnsafe then
    throwError "invalid use of 'unsafe' in constructor declaration"
  if modifiers.attrs.size != 0 then
    throwError "invalid use of attributes in constructor declaration"

structure CtorView where
  ref       : Syntax
  modifiers : Modifiers
  declName  : Name
  binders   : Syntax
  type?     : Option Syntax
  deriving Inhabited

structure ComputedFieldView where
  ref       : Syntax
  modifiers : Syntax
  fieldId   : Name
  type      : Syntax.Term
  matchAlts : TSyntax ``Parser.Term.matchAlts

structure InductiveView where
  ref             : Syntax
  declId          : Syntax
  modifiers       : Modifiers
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Syntax
  type?           : Option Syntax
  ctors           : Array CtorView
  derivingClasses : Array DerivingClassView
  computedFields  : Array ComputedFieldView
  deriving Inhabited

structure ElabHeaderResult where
  view       : InductiveView
  lctx       : LocalContext
  localInsts : LocalInstances
  params     : Array Expr
  type       : Expr
  deriving Inhabited

private partial def elabHeaderAux (views : Array InductiveView) (i : Nat) (acc : Array ElabHeaderResult) : TermElabM (Array ElabHeaderResult) :=
  Term.withAutoBoundImplicitForbiddenPred (fun n => views.any (·.shortDeclName == n)) do
    if h : i < views.size then
      let view := views.get ⟨i, h⟩
      let acc ← Term.withAutoBoundImplicit <| Term.elabBinders view.binders.getArgs fun params => do
        match view.type? with
        | none         =>
          let u ← mkFreshLevelMVar
          let type := mkSort u
          Term.synthesizeSyntheticMVarsNoPostponing
          Term.addAutoBoundImplicits' params type fun params type => do
            return acc.push { lctx := (← getLCtx), localInsts := (← getLocalInstances), params, type, view }
        | some typeStx =>
          let (type, _) ← Term.withAutoBoundImplicit do
            let type ← Term.elabType typeStx
            unless (← isTypeFormerType type) do
              throwErrorAt typeStx "invalid inductive type, resultant type is not a sort"
            Term.synthesizeSyntheticMVarsNoPostponing
            let indices ← Term.addAutoBoundImplicits #[]
            return (← mkForallFVars indices type, indices.size)
          Term.addAutoBoundImplicits' params type fun params type => do
            trace[Elab.inductive] "header params: {params}, type: {type}"
            return acc.push { lctx := (← getLCtx), localInsts := (← getLocalInstances), params, type, view }
      elabHeaderAux views (i+1) acc
    else
      return acc

private def checkNumParams (rs : Array ElabHeaderResult) : TermElabM Nat := do
  let numParams := rs[0]!.params.size
  for r in rs do
    unless r.params.size == numParams do
      throwErrorAt r.view.ref "invalid inductive type, number of parameters mismatch in mutually inductive datatypes"
  return numParams

private def checkUnsafe (rs : Array ElabHeaderResult) : TermElabM Unit := do
  let isUnsafe := rs[0]!.view.modifiers.isUnsafe
  for r in rs do
    unless r.view.modifiers.isUnsafe == isUnsafe do
      throwErrorAt r.view.ref "invalid inductive type, cannot mix unsafe and safe declarations in a mutually inductive datatypes"

private def checkLevelNames (views : Array InductiveView) : TermElabM Unit := do
  if views.size > 1 then
    let levelNames := views[0]!.levelNames
    for view in views do
      unless view.levelNames == levelNames do
        throwErrorAt view.ref "invalid inductive type, universe parameters mismatch in mutually inductive datatypes"

private def mkTypeFor (r : ElabHeaderResult) : TermElabM Expr := do
  withLCtx r.lctx r.localInsts do
    mkForallFVars r.params r.type

private def throwUnexpectedInductiveType : TermElabM α :=
  throwError "unexpected inductive resulting type"

private def eqvFirstTypeResult (firstType type : Expr) : MetaM Bool :=
  forallTelescopeReducing firstType fun _ firstTypeResult => isDefEq firstTypeResult type

-- Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
private partial def checkParamsAndResultType (type firstType : Expr) (numParams : Nat) : TermElabM Unit := do
  try
    forallTelescopeCompatible type firstType numParams fun _ type firstType =>
    forallTelescopeReducing type fun _ type =>
    forallTelescopeReducing firstType fun _ firstType => do
      let type ← whnfD type
      match type with
      | .sort .. =>
        unless (← isDefEq firstType type) do
          throwError "resulting universe mismatch, given{indentExpr type}\nexpected type{indentExpr firstType}"
      | _ =>
        throwError "unexpected inductive resulting type"
  catch
    | Exception.error ref msg => throw (Exception.error ref m!"invalid mutually inductive types, {msg}")
    | ex => throw ex

-- Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
private def checkHeader (r : ElabHeaderResult) (numParams : Nat) (firstType? : Option Expr) : TermElabM Expr := do
  let type ← mkTypeFor r
  match firstType? with
  | none           => return type
  | some firstType =>
    withRef r.view.ref <| checkParamsAndResultType type firstType numParams
    return firstType

-- Auxiliary function for checking whether the types in mutually inductive declaration are compatible.
private partial def checkHeaders (rs : Array ElabHeaderResult) (numParams : Nat) (i : Nat) (firstType? : Option Expr) : TermElabM Unit := do
  if i < rs.size then
    let type ← checkHeader rs[i]! numParams firstType?
    checkHeaders rs numParams (i+1) type

private def elabHeader (views : Array InductiveView) : TermElabM (Array ElabHeaderResult) := do
  let rs ← elabHeaderAux views 0 #[]
  if rs.size > 1 then
    checkUnsafe rs
    let numParams ← checkNumParams rs
    checkHeaders rs numParams 0 none
  return rs

/-- Create a local declaration for each inductive type in `rs`, and execute `x params indFVars`, where `params` are the inductive type parameters and
   `indFVars` are the new local declarations.
   We use the local context/instances and parameters of rs[0].
   Note that this method is executed after we executed `checkHeaders` and established all
   parameters are compatible. -/
private partial def withInductiveLocalDecls (rs : Array ElabHeaderResult) (x : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let namesAndTypes ← rs.mapM fun r => do
    let type ← mkTypeFor r
    pure (r.view.declName, r.view.shortDeclName, type)
  let r0     := rs[0]!
  let params := r0.params
  withLCtx r0.lctx r0.localInsts <| withRef r0.view.ref do
    let rec loop (i : Nat) (indFVars : Array Expr) := do
      if h : i < namesAndTypes.size then
        let (declName, shortDeclName, type) := namesAndTypes.get ⟨i, h⟩
        Term.withAuxDecl shortDeclName type declName fun indFVar => loop (i+1) (indFVars.push indFVar)
      else
        x params indFVars
    loop 0 #[]

private def isInductiveFamily (numParams : Nat) (indFVar : Expr) : TermElabM Bool := do
  let indFVarType ← inferType indFVar
  forallTelescopeReducing indFVarType fun xs _ =>
    return xs.size > numParams

private def getArrowBinderNames (type : Expr) : Array Name :=
  go type #[]
where
  go (type : Expr) (acc : Array Name) : Array Name :=
    match type with
    | .forallE n _ b _ => go b (acc.push n)
    | .mdata _ b       => go b acc
    | _ => acc

/--
  Replace binder names in `type` with `newNames`.
  Remark: we only replace the names for binder containing macroscopes.
-/
private def replaceArrowBinderNames (type : Expr) (newNames : Array Name) : Expr :=
  go type 0
where
  go (type : Expr) (i : Nat) : Expr :=
    if i < newNames.size then
      match type with
      | .forallE n d b bi =>
        if n.hasMacroScopes then
          mkForall newNames[i]! bi d (go b (i+1))
        else
          mkForall n bi d (go b (i+1))
      | _ => type
    else
      type

/--
  Reorder constructor arguments to improve the effectiveness of the `fixedIndicesToParams` method.

  The idea is quite simple. Given a constructor type of the form
  ```
  (a₁ : A₁) → ... → (aₙ : Aₙ) → C b₁ ... bₘ
  ```
  We try to find the longest prefix `b₁ ... bᵢ`, `i ≤ m` s.t.
  - each `bₖ` is in `{a₁, ..., aₙ}`
  - each `bₖ` only depends on variables in `{b₁, ..., bₖ₋₁}`

  Then, it moves this prefix `b₁ ... bᵢ` to the front.

  Remark: We only reorder implicit arguments that have macroscopes. See issue #1156.
  The macroscope test is an approximation, we could have restricted ourselves to auto-implicit arguments.
-/
private def reorderCtorArgs (ctorType : Expr) : MetaM Expr := do
  forallTelescopeReducing ctorType fun as type => do
    /- `type` is of the form `C ...` where `C` is the inductive datatype being defined. -/
    let bs := type.getAppArgs
    let mut as  := as
    let mut bsPrefix := #[]
    for b in bs do
      unless b.isFVar && as.contains b do
        break
      let localDecl ← getFVarLocalDecl b
      if localDecl.binderInfo.isExplicit then
        break
      unless localDecl.userName.hasMacroScopes do
        break
      if (← localDeclDependsOnPred localDecl fun fvarId => as.any fun p => p.fvarId! == fvarId) then
        break
      bsPrefix := bsPrefix.push b
      as := as.erase b
    if bsPrefix.isEmpty then
      return ctorType
    else
      let r ← mkForallFVars (bsPrefix ++ as) type
      /- `r` already contains the resulting type.
         To be able to produce more better error messages, we copy the first `bsPrefix.size` binder names from `C` to `r`.
         This is important when some of constructor parameters were inferred using the auto-bound implicit feature.
         For example, in the following declaration.
         ```
          inductive Member : α → List α → Type u
            | head : Member a (a::as)
            | tail : Member a bs → Member a (b::bs)
         ```
         if we do not copy the binder names
         ```
         #check @Member.head
         ```
         produces `@Member.head : {x : Type u_1} → {a : x} → {as : List x} → Member a (a :: as)`
         which is correct, but a bit confusing. By copying the binder names, we obtain
         `@Member.head : {α : Type u_1} → {a : α} → {as : List α} → Member a (a :: as)`
       -/
      let C := type.getAppFn
      let binderNames := getArrowBinderNames (← instantiateMVars (← inferType C))
      return replaceArrowBinderNames r binderNames[:bsPrefix.size]

/--
  Execute `k` with updated binder information for `xs`. Any `x` that is explicit becomes implicit.
-/
private def withExplicitToImplicit (xs : Array Expr) (k : TermElabM α) : TermElabM α := do
  let mut toImplicit := #[]
  for x in xs do
    if (← getFVarLocalDecl x).binderInfo.isExplicit then
      toImplicit := toImplicit.push (x.fvarId!, BinderInfo.implicit)
  withNewBinderInfos toImplicit k

/--
  Elaborate constructor types.

  Remark: we check whether the resulting type is correct, and the parameter occurrences are consistent, but
  we currently do not check for:
  - Positivity (it is a rare failure, and the kernel already checks for it).
  - Universe constraints (the kernel checks for it).
-/
private def elabCtors (indFVars : Array Expr) (indFVar : Expr) (params : Array Expr) (r : ElabHeaderResult) : TermElabM (List Constructor) := withRef r.view.ref do
  let indFamily ← isInductiveFamily params.size indFVar
  r.view.ctors.toList.mapM fun ctorView =>
    Term.withAutoBoundImplicit <| Term.elabBinders ctorView.binders.getArgs fun ctorParams =>
      withRef ctorView.ref do
        let rec elabCtorType (k : Expr → TermElabM Constructor) : TermElabM Constructor := do
          match ctorView.type? with
          | none          =>
            if indFamily then
              throwError "constructor resulting type must be specified in inductive family declaration"
            k <| mkAppN indFVar params
          | some ctorType =>
            let type ← Term.elabType ctorType
            trace[Elab.inductive] "elabType {ctorView.declName} : {type} "
            Term.synthesizeSyntheticMVars (mayPostpone := true)
            let type ← instantiateMVars type
            let type ← checkParamOccs type
            forallTelescopeReducing type fun _ resultingType => do
              unless resultingType.getAppFn == indFVar do
                throwError "unexpected constructor resulting type{indentExpr resultingType}"
              unless (← isType resultingType) do
                throwError "unexpected constructor resulting type, type expected{indentExpr resultingType}"
            k type
        elabCtorType fun type => do
          Term.synthesizeSyntheticMVarsNoPostponing
          let ctorParams ← Term.addAutoBoundImplicits ctorParams
          let except (mvarId : MVarId) := ctorParams.any fun ctorParam => ctorParam.isMVar && ctorParam.mvarId! == mvarId
          /-
            We convert metavariables in the resulting type info extra parameters. Otherwise, we would not be able to elaborate
            declarations such as
            ```
            inductive Palindrome : List α → Prop where
              | nil      : Palindrome [] -- We would get an error here saying "failed to synthesize implicit argument" at `@List.nil ?m`
              | single   : (a : α) → Palindrome [a]
              | sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])
            ```
            We used to also collect unassigned metavariables on `ctorParams`, but it produced counterintuitive behavior.
            For example, the following declaration used to be accepted.
            ```
            inductive Foo
            | bar (x)

            #check Foo.bar
            -- @Foo.bar : {x : Sort u_1} → x → Foo
            ```
            which is also inconsistent with the behavior of auto implicits in definitions. For example, the following example was never accepted.
            ```
            def bar (x) := 1
            ```
          -/
          let extraCtorParams ← Term.collectUnassignedMVars (← instantiateMVars type) #[] except
          trace[Elab.inductive] "extraCtorParams: {extraCtorParams}"
          /- We must abstract `extraCtorParams` and `ctorParams` simultaneously to make
             sure we do not create auxiliary metavariables. -/
          let type  ← mkForallFVars (extraCtorParams ++ ctorParams) type
          let type ← reorderCtorArgs type
          let type ← mkForallFVars params type
          trace[Elab.inductive] "{ctorView.declName} : {type}"
          return { name := ctorView.declName, type }
where
  checkParamOccs (ctorType : Expr) : MetaM Expr :=
    let visit (e : Expr) : MetaM TransformStep := do
      let f := e.getAppFn
      if indFVars.contains f then
        let mut args := e.getAppArgs
        unless args.size ≥ params.size do
          throwError "unexpected inductive type occurrence{indentExpr e}"
        for i in [:params.size] do
          let param := params[i]!
          let arg := args[i]!
          unless (← isDefEq param arg) do
            throwError "inductive datatype parameter mismatch{indentExpr arg}\nexpected{indentExpr param}"
          args := args.set! i param
        return TransformStep.done (mkAppN f args)
      else
        return .continue
    transform ctorType (pre := visit)

private def getResultingUniverse : List InductiveType → TermElabM Level
  | []           => throwError "unexpected empty inductive declaration"
  | indType :: _ => forallTelescopeReducing indType.type fun _ r => do
    let r ← whnfD r
    match r with
    | Expr.sort u => return u
    | _           => throwError "unexpected inductive type resulting type{indentExpr r}"

/--
  Return `some ?m` if `u` is of the form `?m + k`.
  Return none if `u` does not contain universe metavariables.
  Throw exception otherwise. -/
def shouldInferResultUniverse (u : Level) : TermElabM (Option LMVarId) := do
  let u ← instantiateLevelMVars u
  if u.hasMVar then
    match u.getLevelOffset with
    | Level.mvar mvarId => return some mvarId
    | _ =>
      throwError "cannot infer resulting universe level of inductive datatype, given level contains metavariables {mkSort u}, provide universe explicitly"
  else
    return none

/--
  Convert universe metavariables into new parameters. It skips `univToInfer?` (the inductive datatype resulting universe) because
  it should be inferred later using `inferResultingUniverse`.
-/
private def levelMVarToParam (indTypes : List InductiveType) (univToInfer? : Option LMVarId) : TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type  ← levelMVarToParam' indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← levelMVarToParam' ctor.type
      return { ctor with type := ctorType }
    return { indType with ctors, type }
where
  levelMVarToParam' (type : Expr) : TermElabM Expr := do
    Term.levelMVarToParam type (except := fun mvarId => univToInfer? == some mvarId)

def mkResultUniverse (us : Array Level) (rOffset : Nat) : Level :=
  if us.isEmpty && rOffset == 0 then
    levelOne
  else
    let r := Level.mkNaryMax us.toList
    if rOffset == 0 && !r.isZero && !r.isNeverZero then
      mkLevelMax r levelOne |>.normalize
    else
      r.normalize

 /--
   Auxiliary function for `updateResultingUniverse`
   `accLevel u r rOffset` add `u` to state if it is not already there and
   it is different from the resulting universe level `r+rOffset`.


   If `u` is a `max`, then its components are recursively processed.
   If `u` is a `succ` and `rOffset > 0`, we process the `u`s child using `rOffset-1`.

   This method is used to infer the resulting universe level of an inductive datatype.
 -/
def accLevel (u : Level) (r : Level) (rOffset : Nat) : OptionT (StateT (Array Level) Id) Unit := do
  go u rOffset
where
  go (u : Level) (rOffset : Nat) : OptionT (StateT (Array Level) Id) Unit := do
    match u, rOffset with
    | .max u v,  rOffset   => go u rOffset; go v rOffset
    | .imax u v, rOffset   => go u rOffset; go v rOffset
    | .zero,     _         => return ()
    | .succ u,   rOffset+1 => go u rOffset
    | u,         rOffset   =>
      if rOffset == 0 && u == r then
        return ()
      else if r.occurs u  then
        failure
      else if rOffset > 0 then
        failure
      else if (← get).contains u then
        return ()
      else
        modify fun us => us.push u

/--
  Auxiliary function for `updateResultingUniverse`
  `accLevelAtCtor ctor ctorParam r rOffset` add `u` (`ctorParam`'s universe) to state if it is not already there and
  it is different from the resulting universe level `r+rOffset`.

  See `accLevel`.
-/
def accLevelAtCtor (ctor : Constructor) (ctorParam : Expr) (r : Level) (rOffset : Nat) : StateRefT (Array Level) TermElabM Unit := do
  let type ← inferType ctorParam
  let u ← instantiateLevelMVars (← getLevel type)
  match (← modifyGet fun s => accLevel u r rOffset |>.run |>.run s) with
  | some _ => pure ()
  | none =>
    let typeType ← inferType type
    let mut msg := m!"failed to compute resulting universe level of inductive datatype, constructor '{ctor.name}' has type{indentExpr ctor.type}\nparameter"
    let localDecl ← getFVarLocalDecl ctorParam
    unless localDecl.userName.hasMacroScopes do
      msg := msg ++ m!" '{ctorParam}'"
    msg := msg ++ m!" has type{indentD m!"{type} : {typeType}"}\ninductive type resulting type{indentExpr (mkSort (r.addOffset rOffset))}"
    if r.isMVar then
      msg := msg ++ "\nrecall that Lean only infers the resulting universe level automatically when there is a unique solution for the universe level constraints, consider explicitly providing the inductive type resulting universe level"
    throwError msg

/--
  Execute `k` using the `Syntax` reference associated with constructor `ctorName`.
-/
def withCtorRef [Monad m] [MonadRef m] (views : Array InductiveView) (ctorName : Name) (k : m α) : m α := do
  for view in views do
    for ctorView in view.ctors do
      if ctorView.declName == ctorName then
        return (← withRef ctorView.ref k)
  k

/-- Auxiliary function for `updateResultingUniverse` -/
private partial def collectUniverses (views : Array InductiveView) (r : Level) (rOffset : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (Array Level) := do
  let (_, us) ← go |>.run #[]
  return us
where
  go : StateRefT (Array Level) TermElabM Unit :=
    indTypes.forM fun indType => indType.ctors.forM fun ctor =>
      withCtorRef views ctor.name do
        forallTelescopeReducing ctor.type fun ctorParams _ =>
          for ctorParam in ctorParams[numParams:] do
            accLevelAtCtor ctor ctorParam r rOffset

private def updateResultingUniverse (views : Array InductiveView) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) := do
  let r ← getResultingUniverse indTypes
  let rOffset : Nat   := r.getOffset
  let r       : Level := r.getLevelOffset
  unless r.isMVar do
    throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly: {r}"
  let us ← collectUniverses views r rOffset numParams indTypes
  trace[Elab.inductive] "updateResultingUniverse us: {us}, r: {r}, rOffset: {rOffset}"
  let rNew := mkResultUniverse us rOffset
  assignLevelMVar r.mvarId! rNew
  indTypes.mapM fun indType => do
    let type ← instantiateMVars indType.type
    let ctors ← indType.ctors.mapM fun ctor => return { ctor with type := (← instantiateMVars ctor.type) }
    return { indType with type, ctors }

register_builtin_option bootstrap.inductiveCheckResultingUniverse : Bool := {
    defValue := true,
    group    := "bootstrap",
    descr    := "by default the `inductive/structure commands report an error if the resulting universe is not zero, but may be zero for some universe parameters. Reason: unless this type is a subsingleton, it is hardly what the user wants since it can only eliminate into `Prop`. In the `Init` package, we define subsingletons, and we use this option to disable the check. This option may be deleted in the future after we improve the validator"
}

def checkResultingUniverse (u : Level) : TermElabM Unit := do
  if bootstrap.inductiveCheckResultingUniverse.get (← getOptions) then
    let u ← instantiateLevelMVars u
    if !u.isZero && !u.isNeverZero then
      throwError "invalid universe polymorphic type, the resultant universe is not Prop (i.e., 0), but it may be Prop for some parameter values (solution: use 'u+1' or 'max 1 u'{indentD u}"

private def checkResultingUniverses (views : Array InductiveView) (numParams : Nat) (indTypes : List InductiveType) : TermElabM Unit := do
  let u := (← instantiateLevelMVars (← getResultingUniverse indTypes)).normalize
  checkResultingUniverse u
  unless u.isZero do
    indTypes.forM fun indType => indType.ctors.forM fun ctor =>
      forallTelescopeReducing ctor.type fun ctorArgs _ => do
        for ctorArg in ctorArgs[numParams:] do
          let type ← inferType ctorArg
          let v := (← instantiateLevelMVars (← getLevel type)).normalize
          let rec check (v' : Level) (u' : Level) : TermElabM Unit :=
            match v', u' with
            | .succ v', .succ u' => check v' u'
            | .mvar id, .param ..  =>
              /- Special case:
                 The constructor parameter `v` is at unverse level `?v+k` and
                 the resulting inductive universe level is `u'+k`, where `u'` is a parameter (or zero).
                 Thus, `?v := u'` is the only choice for satisfying the universe constraint `?v+k <= u'+k`.
                 Note that, we still generate an error for cases where there is more than one of satisfying the constraint.
                 Examples:
                 -----------------------------------------------------------
                 | ctor universe level | inductive datatype universe level |
                 -----------------------------------------------------------
                 |   ?v                | max u w                           |
                 -----------------------------------------------------------
                 |   ?v                | u + 1                             |
                 -----------------------------------------------------------
              -/
              assignLevelMVar id u'
            | .mvar id, .zero => assignLevelMVar id u' -- TODO: merge with previous case
            | _, _ =>
              unless u.geq v do
                let mut msg := m!"invalid universe level in constructor '{ctor.name}', parameter"
                let localDecl ← getFVarLocalDecl ctorArg
                unless localDecl.userName.hasMacroScopes do
                  msg := msg ++ m!" '{ctorArg}'"
                msg := msg ++ m!" has type{indentExpr type}"
                msg := msg ++ m!"\nat universe level{indentD v}"
                msg := msg ++ m!"\nit must be smaller than or equal to the inductive datatype universe level{indentD u}"
                withCtorRef views ctor.name <| throwError msg
          check v u

private def collectUsed (indTypes : List InductiveType) : StateRefT CollectFVars.State MetaM Unit := do
  indTypes.forM fun indType => do
    indType.type.collectFVars
    indType.ctors.forM fun ctor =>
      ctor.type.collectFVars

private def removeUnused (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed indTypes).run {}
  Meta.removeUnused vars used

private def withUsed {α} (vars : Array Expr) (indTypes : List InductiveType) (k : Array Expr → TermElabM α) : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused vars indTypes
  withLCtx lctx localInsts <| k vars

private def updateParams (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type ← mkForallFVars vars indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← withExplicitToImplicit vars (mkForallFVars vars ctor.type)
      return { ctor with type := ctorType }
    return { indType with type, ctors }

private def collectLevelParamsInInductive (indTypes : List InductiveType) : Array Name := Id.run do
  let mut usedParams : CollectLevelParams.State := {}
  for indType in indTypes do
    usedParams := collectLevelParams usedParams indType.type
    for ctor in indType.ctors do
      usedParams := collectLevelParams usedParams ctor.type
  return usedParams.params

private def mkIndFVar2Const (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name) : ExprMap Expr := Id.run do
  let levelParams := levelNames.map mkLevelParam;
  let mut m : ExprMap Expr := {}
  for i in [:views.size] do
    let view    := views[i]!
    let indFVar := indFVars[i]!
    m := m.insert indFVar (mkConst view.declName levelParams)
  return m

/-- Remark: `numVars <= numParams`. `numVars` is the number of context `variables` used in the inductive declaration,
   and `numParams` is `numVars` + number of explicit parameters provided in the declaration. -/
private def replaceIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name)
    (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars levelNames
  indTypes.mapM fun indType => do
    let ctors ← indType.ctors.mapM fun ctor => do
      let type ← forallBoundedTelescope ctor.type numParams fun params type => do
        let type := type.replace fun e =>
          if !e.isFVar then
            none
          else match indFVar2Const.find? e with
            | none   => none
            | some c => mkAppN c (params.extract 0 numVars)
        instantiateMVars (← mkForallFVars params type)
      return { ctor with type }
    return { indType with ctors }

private def mkAuxConstructions (views : Array InductiveView) : TermElabM Unit := do
  let env ← getEnv
  let hasEq   := env.contains ``Eq
  let hasHEq  := env.contains ``HEq
  let hasUnit := env.contains ``PUnit
  let hasProd := env.contains ``Prod
  for view in views do
    let n := view.declName
    mkRecOn n
    if hasUnit then mkCasesOn n
    if hasUnit && hasEq && hasHEq then mkNoConfusion n
    if hasUnit && hasProd then mkBelow n
    if hasUnit && hasProd then mkIBelow n
  for view in views do
    let n := view.declName;
    if hasUnit && hasProd then mkBRecOn n
    if hasUnit && hasProd then mkBInductionOn n

private def getArity (indType : InductiveType) : MetaM Nat :=
  forallTelescopeReducing indType.type fun xs _ => return xs.size

private def resetMaskAt (mask : Array Bool) (i : Nat) : Array Bool :=
  if h : i < mask.size then
    mask.set ⟨i, h⟩ false
  else
    mask

/--
  Compute a bit-mask that for `indType`. The size of the resulting array `result` is the arity of `indType`.
  The first `numParams` elements are `false` since they are parameters.
  For `i ∈ [numParams, arity)`, we have that `result[i]` if this index of the inductive family is fixed.
-/
private def computeFixedIndexBitMask (numParams : Nat) (indType : InductiveType) (indFVars : Array Expr) : MetaM (Array Bool) := do
  let arity ← getArity indType
  if arity ≤ numParams then
    return mkArray arity false
  else
    let maskRef ← IO.mkRef (mkArray numParams false ++ mkArray (arity - numParams) true)
    let rec go (ctors : List Constructor) : MetaM (Array Bool) := do
      match ctors with
      | [] => maskRef.get
      | ctor :: ctors =>
        forallTelescopeReducing ctor.type fun xs type => do
          let typeArgs := type.getAppArgs
          for i in [numParams:arity] do
            unless i < xs.size && xs[i]! == typeArgs[i]! do -- Remark: if we want to allow arguments to be rearranged, this test should be xs.contains typeArgs[i]
              maskRef.modify fun mask => mask.set! i false
          for x in xs[numParams:] do
            let xType ← inferType x
            let cond (e : Expr) := indFVars.any (fun indFVar => e.getAppFn == indFVar) && e.getAppNumArgs > numParams
            xType.forEachWhere cond fun e => do
              let eArgs := e.getAppArgs
              for i in [numParams:eArgs.size] do
                if i >= typeArgs.size then
                  maskRef.modify (resetMaskAt · i)
                else
                  unless eArgs[i]! == typeArgs[i]! do
                    maskRef.modify (resetMaskAt · i)
        go ctors
    go indType.ctors

/-- Return true iff `arrowType` is an arrow and its domain is defeq to `type` -/
private def isDomainDefEq (arrowType : Expr) (type : Expr) : MetaM Bool := do
  if !arrowType.isForall then
    return false
  else
    /-
      We used to use `withNewMCtxDepth` to make sure we do not assign universe metavariables,
      but it was not satisfactory. For example, in declarations such as
      ```
      inductive Eq : α → α → Prop where
      | refl (a : α) : Eq a a
      ```
      We want the first two indices to be promoted to parameters, and this will only
      happen if we can assign universe metavariables.
    -/
    isDefEq arrowType.bindingDomain! type

/--
  Convert fixed indices to parameters.
-/
private partial def fixedIndicesToParams (numParams : Nat) (indTypes : Array InductiveType) (indFVars : Array Expr) : MetaM Nat := do
  let masks ← indTypes.mapM (computeFixedIndexBitMask numParams · indFVars)
  if masks.all fun mask => !mask.contains true then
    return numParams
  trace[Elab.inductive] "masks: {masks}"
  -- We process just a non-fixed prefix of the indices for now. Reason: we don't want to change the order.
  -- TODO: extend it in the future. For example, it should be reasonable to change
  -- the order of indices generated by the auto implicit feature.
  let mask := masks[0]!
  forallBoundedTelescope indTypes[0]!.type numParams fun params type => do
    let otherTypes ← indTypes[1:].toArray.mapM fun indType => do whnfD (← instantiateForall indType.type params)
    let ctorTypes ← indTypes.toList.mapM fun indType => indType.ctors.mapM fun ctor => do whnfD (← instantiateForall ctor.type params)
    let typesToCheck := otherTypes.toList ++ ctorTypes.join
    let rec go (i : Nat) (type : Expr) (typesToCheck : List Expr) : MetaM Nat := do
      if i < mask.size then
        if !masks.all fun mask => i < mask.size && mask[i]! then
           return i
        if !type.isForall then
          return i
        let paramType := type.bindingDomain!
        if !(← typesToCheck.allM fun type => isDomainDefEq type paramType) then
          trace[Elab.inductive] "domain not def eq: {i}, {type} =?= {paramType}"
          return i
        withLocalDeclD `a paramType fun paramNew => do
          let typesToCheck ← typesToCheck.mapM fun type => whnfD (type.bindingBody!.instantiate1 paramNew)
          go (i+1) (type.bindingBody!.instantiate1 paramNew) typesToCheck
      else
        return i
    go numParams type typesToCheck

private def mkInductiveDecl (vars : Array Expr) (views : Array InductiveView) : TermElabM Unit := Term.withoutSavingRecAppSyntax do
  let view0 := views[0]!
  let scopeLevelNames ← Term.getLevelNames
  checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref <| Term.withLevelNames allUserLevelNames do
    let rs ← elabHeader views
    withInductiveLocalDecls rs fun params indFVars => do
      trace[Elab.inductive] "indFVars: {indFVars}"
      let mut indTypesArray := #[]
      for i in [:views.size] do
        let indFVar := indFVars[i]!
        Term.addLocalVarInfo views[i]!.declId indFVar
        let r       := rs[i]!
        let type  ← mkForallFVars params r.type
        let ctors ← withExplicitToImplicit params (elabCtors indFVars indFVar params r)
        indTypesArray := indTypesArray.push { name := r.view.declName, type, ctors }
      Term.synthesizeSyntheticMVarsNoPostponing
      let numExplicitParams ← fixedIndicesToParams params.size indTypesArray indFVars
      trace[Elab.inductive] "numExplicitParams: {numExplicitParams}"
      let indTypes := indTypesArray.toList
      let u ← getResultingUniverse indTypes
      let univToInfer? ← shouldInferResultUniverse u
      withUsed vars indTypes fun vars => do
        let numVars   := vars.size
        let numParams := numVars + numExplicitParams
        let indTypes ← updateParams vars indTypes
        let indTypes ← if let some univToInfer := univToInfer? then
          updateResultingUniverse views numParams (← levelMVarToParam indTypes univToInfer)
        else
          checkResultingUniverses views numParams indTypes
          levelMVarToParam indTypes none
        let usedLevelNames := collectLevelParamsInInductive indTypes
        match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
        | .error msg      => throwError msg
        | .ok levelParams => do
          let indTypes ← replaceIndFVarsWithConsts views indFVars levelParams numVars numParams indTypes
          let decl := Declaration.inductDecl levelParams numParams indTypes isUnsafe
          Term.ensureNoUnassignedMVars decl
          addDecl decl
          mkAuxConstructions views
    withSaveInfoContext do  -- save new env
      for view in views do
        Term.addTermInfo' view.ref[1] (← mkConstWithLevelParams view.declName) (isBinder := true)
        for ctor in view.ctors do
          Term.addTermInfo' ctor.ref[3] (← mkConstWithLevelParams ctor.declName) (isBinder := true)
        -- We need to invoke `applyAttributes` because `class` is implemented as an attribute.
        Term.applyAttributesAt view.declName view.modifiers.attrs .afterTypeChecking

private def applyDerivingHandlers (views : Array InductiveView) : CommandElabM Unit := do
  let mut processed : NameSet := {}
  for view in views do
    for classView in view.derivingClasses do
      let className := classView.className
      unless processed.contains className do
        processed := processed.insert className
        let mut declNames := #[]
        for view in views do
          if view.derivingClasses.any fun classView => classView.className == className then
            declNames := declNames.push view.declName
        classView.applyHandlers declNames

private def applyComputedFields (indViews : Array InductiveView) : CommandElabM Unit := do
  if indViews.all (·.computedFields.isEmpty) then return

  let mut computedFields := #[]
  let mut computedFieldDefs := #[]
  for indView@{declName, ..} in indViews do
    for {ref, fieldId, type, matchAlts, modifiers, ..} in indView.computedFields do
      computedFieldDefs := computedFieldDefs.push <| ← do
        let modifiers ← match modifiers with
          | `(Lean.Parser.Command.declModifiersT| $[$doc:docComment]? $[$attrs:attributes]? $[$vis]? $[noncomputable]?) =>
            `(Lean.Parser.Command.declModifiersT| $[$doc]? $[$attrs]? $[$vis]? noncomputable)
          | _ => do
            withRef modifiers do logError "unsupported modifiers for computed field"
            `(Parser.Command.declModifiersT| noncomputable)
        `($(⟨modifiers⟩):declModifiers
          def%$ref $(mkIdent <| `_root_ ++ declName ++ fieldId):ident : $type $matchAlts:matchAlts)
    let computedFieldNames := indView.computedFields.map fun {fieldId, ..} => declName ++ fieldId
    computedFields := computedFields.push (declName, computedFieldNames)
  withScope (fun scope => { scope with
      opts := scope.opts
        |>.setBool `bootstrap.genMatcherCode false
        |>.setBool `elaboratingComputedFields true}) <|
    elabCommand <| ← `(mutual $computedFieldDefs* end)

  liftTermElabM do Term.withDeclName indViews[0]!.declName do
    ComputedFields.setComputedFields computedFields

def elabInductiveViews (views : Array InductiveView) : CommandElabM Unit := do
  let view0 := views[0]!
  let ref := view0.ref
  runTermElabM fun vars => Term.withDeclName view0.declName do withRef ref do
    mkInductiveDecl vars views
    mkSizeOfInstances view0.declName
    Lean.Meta.IndPredBelow.mkBelow view0.declName
    for view in views do
      mkInjectiveTheorems view.declName
  applyComputedFields views -- NOTE: any generated code before this line is invalid
  applyDerivingHandlers views
  runTermElabM fun _ => Term.withDeclName view0.declName do withRef ref do
    for view in views do
      Term.applyAttributesAt view.declName view.modifiers.attrs .afterCompilation

end Lean.Elab.Command
