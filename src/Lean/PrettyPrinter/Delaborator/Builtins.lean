/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura, Gabriel Ebner, Mario Carneiro
-/
prelude
import Lean.Parser
import Lean.PrettyPrinter.Delaborator.Attributes
import Lean.PrettyPrinter.Delaborator.Basic
import Lean.PrettyPrinter.Delaborator.SubExpr
import Lean.PrettyPrinter.Delaborator.TopDownAnalyze
import Lean.Meta.CoeAttr

namespace Lean.PrettyPrinter.Delaborator
open Lean.Meta
open Lean.Parser.Term
open SubExpr
open TSyntax.Compat

/--
If `cond` is true, wraps the syntax produced by `d` in a type ascription.
-/
def withTypeAscription (d : Delab) (cond : Bool := true) : DelabM Term := do
  let stx ← d
  if cond then
    let stx ← annotateCurPos stx
    let typeStx ← withType delab
    `(($stx : $typeStx))
  else
    return stx

/--
Wraps the identifier (or identifier with explicit universe levels) with `@` if `pp.analysis.blockImplicit` is set to true.
-/
def maybeAddBlockImplicit (identLike : Syntax) : DelabM Syntax := do
  if ← getPPOption getPPAnalysisBlockImplicit then `(@$identLike) else pure identLike

@[builtin_delab fvar]
def delabFVar : Delab := do
  let Expr.fvar fvarId ← getExpr | unreachable!
  try
    let l ← fvarId.getDecl
    maybeAddBlockImplicit (mkIdent l.userName)
  catch _ =>
    -- loose free variable, use internal name
    maybeAddBlockImplicit <| mkIdent (fvarId.name.replacePrefix `_uniq `_fvar)

-- loose bound variable, use pseudo syntax
@[builtin_delab bvar]
def delabBVar : Delab := do
  let Expr.bvar idx ← getExpr | unreachable!
  pure $ mkIdent $ Name.mkSimple $ "#" ++ toString idx

@[builtin_delab mvar]
def delabMVar : Delab := do
  let Expr.mvar n ← getExpr | unreachable!
  withTypeAscription (cond := ← getPPOption getPPMVarsWithType) do
    if ← getPPOption getPPMVars then
      let mvarDecl ← n.getDecl
      let n :=
        match mvarDecl.userName with
        | .anonymous => n.name.replacePrefix `_uniq `m
        | n => n
      `(?$(mkIdent n))
    else
      `(?_)

@[builtin_delab sort]
def delabSort : Delab := do
  let Expr.sort l ← getExpr | unreachable!
  match l with
  | Level.zero => `(Prop)
  | Level.succ .zero => `(Type)
  | _ =>
    let mvars ← getPPOption getPPMVars
    match l.dec with
    | some l' => `(Type $(Level.quote l' (prec := max_prec) (mvars := mvars)))
    | none    => `(Sort $(Level.quote l (prec := max_prec) (mvars := mvars)))

/--
Delaborator for `const` expressions.
This is not registered as a delaborator, as `const` is not an expression kind
(see [delab] description and `Lean.PrettyPrinter.Delaborator.getExprKind`).
Rather, it is called through the `app` delaborator.
-/
def delabConst : Delab := do
  let Expr.const c₀ ls ← getExpr | unreachable!
  let c₀ := if (← getPPOption getPPPrivateNames) then c₀ else (privateToUserName? c₀).getD c₀

  let mut c ← unresolveNameGlobal c₀ (fullNames := ← getPPOption getPPFullNames)
  let stx ← if ls.isEmpty || !(← getPPOption getPPUniverses) then
    if (← getLCtx).usesUserName c then
      -- `c` is also a local declaration
      if c == c₀ && !(← read).inPattern then
        -- `c` is the fully qualified named. So, we append the `_root_` prefix
        c := `_root_ ++ c
      else
        c := c₀
    pure <| mkIdent c
  else
    let mvars ← getPPOption getPPMVars
    `($(mkIdent c).{$[$(ls.toArray.map (Level.quote · (prec := 0) (mvars := mvars)))],*})

  let stx ← maybeAddBlockImplicit stx
  if (← getPPOption getPPTagAppFns) then
    annotateTermInfo stx
  else
    return stx

def withMDataOptions [Inhabited α] (x : DelabM α) : DelabM α := do
  match ← getExpr with
  | Expr.mdata m .. =>
    let mut posOpts := (← read).optionsPerPos
    let pos ← getPos
    for (k, v) in m do
      if (`pp).isPrefixOf k then
        let opts := posOpts.find? pos |>.getD {}
        posOpts := posOpts.insert pos (opts.insert k v)
    withReader ({ · with optionsPerPos := posOpts }) $ withMDataExpr x
  | _ => x

partial def withMDatasOptions [Inhabited α] (x : DelabM α) : DelabM α := do
  if (← getExpr).isMData then withMDataOptions (withMDatasOptions x) else x

/--
A structure that records details of a function parameter.
-/
structure ParamKind where
  /-- Binder name for the parameter. -/
  name        : Name
  /-- Binder info for the parameter. -/
  bInfo       : BinderInfo
  /-- The default value for the parameter, if the parameter has a default value. -/
  defVal      : Option Expr := none
  /-- Whether the parameter is an autoparam (i.e., whether it uses a tactic for the default value). -/
  isAutoParam : Bool := false
  deriving Inhabited

/--
Returns true if the parameter is an explicit parameter that has neither a default value nor a tactic.
-/
def ParamKind.isRegularExplicit (param : ParamKind) : Bool :=
  param.bInfo.isExplicit && !param.isAutoParam && param.defVal.isNone

/--
Given a function `f` supplied with arguments `args`, returns an array whose n-th element
is set to the kind of the n-th argument's associated parameter.
We do not assume the expression `mkAppN f args` is sensical,
and this function captures errors (except for panics) and returns the empty array in that case.

The returned array might be longer than the number of arguments.
It gives parameter kinds for the fully-applied function.
Note: the `defVal` expressions are only guaranteed to be valid for parameters associated to the supplied arguments;
after this, they might refer to temporary fvars.

This function properly handles "overapplied" functions.
For example, while `id` takes one explicit argument, it can take more than one explicit
argument when its arguments are specialized to function types, like in `id id 2`.
-/
def getParamKinds (f : Expr) (args : Array Expr) : MetaM (Array ParamKind) := do
  try
    let mut result : Array ParamKind := Array.mkEmpty args.size
    let mut fnType ← inferType f
    let mut j := 0
    for i in [0:args.size] do
      unless fnType.isForall do
        fnType ← withTransparency .all <| whnf (fnType.instantiateRevRange j i args)
        j := i
      let .forallE n t b bi := fnType | failure
      let defVal := t.getOptParamDefault? |>.map (·.instantiateRevRange j i args)
      result := result.push { name := n, bInfo := bi, defVal, isAutoParam := t.isAutoParam }
      fnType := b
    fnType := fnType.instantiateRevRange j args.size args
    -- We still want to consider parameters past the ones for the supplied arguments for analysis.
    forallTelescopeReducing fnType fun xs _ => do
      xs.foldlM (init := result) fun result x => do
        let l ← x.fvarId!.getDecl
        -- Warning: the defVal might refer to fvars that are only valid in this context
        pure <| result.push { name := l.userName, bInfo := l.binderInfo, defVal := l.type.getOptParamDefault?, isAutoParam := l.type.isAutoParam }
  catch _ => pure #[] -- recall that expr may be nonsensical

def shouldShowMotive (motive : Expr) (opts : Options) : MetaM Bool := do
  pure (getPPMotivesAll opts)
  <||> (pure (getPPMotivesPi opts) <&&> returnsPi motive)
  <||> (pure (getPPMotivesNonConst opts) <&&> isNonConstFun motive)

/--
Takes application syntax and converts it into structure instance notation, if possible.
Assumes that the application is pretty printed in implicit mode.
-/
def unexpandStructureInstance (stx : Syntax) : Delab := whenPPOption getPPStructureInstances do
  let env ← getEnv
  let e ← getExpr
  let some s ← isConstructorApp? e | failure
  guard <| isStructure env s.induct
  /- If implicit arguments should be shown, and the structure has parameters, we should not
     pretty print using { ... }, because we will not be able to see the parameters. -/
  let fieldNames := getStructureFields env s.induct
  let mut fields := #[]
  guard $ fieldNames.size == stx[1].getNumArgs
  if hasPPUsingAnonymousConstructorAttribute env s.induct then
    return ← withTypeAscription (cond := (← withType <| getPPOption getPPStructureInstanceType)) do
      `(⟨$[$(stx[1].getArgs)],*⟩)
  let args := e.getAppArgs
  let fieldVals := args.extract s.numParams args.size
  for idx in [:fieldNames.size] do
    let fieldName := fieldNames[idx]!
    if (← getPPOption getPPStructureInstancesFlatten) && (Lean.isSubobjectField? env s.induct fieldName).isSome then
      match stx[1][idx] with
      | `({ $fields',* $[: $_]?}) =>
        -- We have found a subobject field that itself is printed with structure instance notation.
        -- Scavange its fields.
        fields := fields ++ fields'.getElems
        continue
      | _ => pure ()
    let fieldId := mkIdent fieldName
    let fieldPos ← nextExtraPos
    let fieldId := annotatePos fieldPos fieldId
    addFieldInfo fieldPos (s.induct ++ fieldName) fieldName fieldId fieldVals[idx]!
    let field ← `(structInstField|$fieldId:ident := $(stx[1][idx]))
    fields := fields.push field
  let tyStx ← withType do
    if (← getPPOption getPPStructureInstanceType) then delab >>= pure ∘ some else pure none
  `({ $fields,* $[: $tyStx]? })

/--
If `e` is an application that is a candidate for using field notation,
returns the parameter index and the field name to use.
Checks that there are enough arguments.
-/
def appFieldNotationCandidate? : DelabM (Option (Nat × Name)) := do
  let e ← getExpr
  unless e.isApp do return none
  let some (field, idx) ← fieldNotationCandidate? e.getAppFn e.getAppArgs (← getPPOption getPPFieldNotationGeneralized)
    | return none
  unless idx < e.getAppNumArgs do return none
  /-
  There are some kinds of expressions that cause issues with field notation,
  so we prevent using it in these cases.
  For example, `2.succ` is not parseable.
  -/
  let obj := e.getArg! idx
  if obj.isRawNatLit || obj.isAppOfArity ``OfNat.ofNat 3 || obj.isAppOfArity ``OfScientific.ofScientific 5 then
    return none
  return (idx, field)

/--
Consumes projections to parent structures, and runs `d` in the resulting context.
For example, if the current expression is `o.toB.toA`, runs `d` with `o` as the current expression.

If `explicit` is true, then does not consume parent projections for structures with parameters,
since these are implicit arguments.
-/
private partial def withoutParentProjections (explicit : Bool) (d : DelabM α) : DelabM α := do
  if ← try isParentProj explicit (← getExpr) catch _ => pure false then
    withAppArg <| withoutParentProjections explicit d
  else
    d

/--
In explicit mode, decides whether or not the applied function needs `@`,
where `numArgs` is the number of arguments actually supplied to `f`.
-/
def needsExplicit (f : Expr) (numArgs : Nat) (paramKinds : Array ParamKind) : Bool :=
  if paramKinds.size == 0 && 0 < numArgs && f matches .const _ [] then
    -- Error calculating ParamKinds,
    -- but we presume that the universe list has been intentionally erased, for example by LCNF.
    -- The arguments in this case are *only* the explicit arguments, so we don't want to prefix with `@`.
    false
  else
    -- Error calculating ParamKinds, so return `true` to be safe
    paramKinds.size < numArgs
    -- One of the supplied parameters isn't explicit
    || paramKinds[:numArgs].any (fun param => !param.bInfo.isExplicit)
    -- The next parameter is implicit or inst implicit
    || (numArgs < paramKinds.size && paramKinds[numArgs]!.bInfo matches .implicit | .instImplicit)
    -- One of the parameters after the supplied parameters is explicit but not regular explicit.
    || paramKinds[numArgs:].any (fun param => param.bInfo.isExplicit && !param.isRegularExplicit)

/--
Delaborates a function application in explicit mode.
* If `insertExplicit` is true, then ensures the head syntax is wrapped with `@`.
* If `fieldNotation` is true, then allows the application to be pretty printed using field notation.
  Field notation will not be used when `insertExplicit` is true.
-/
def delabAppExplicitCore (fieldNotation : Bool) (numArgs : Nat) (delabHead : (insertExplicit : Bool) → Delab) (paramKinds : Array ParamKind) : Delab := do
  let insertExplicit := needsExplicit ((← getExpr).getBoundedAppFn numArgs) numArgs paramKinds
  let fieldNotation ← pure (fieldNotation && !insertExplicit) <&&> getPPOption getPPFieldNotation
    <&&> not <$> getPPOption getPPAnalysisNoDot
    <&&> withBoundedAppFn numArgs do pure (← getExpr).consumeMData.isConst <&&> not <$> withMDatasOptions (getPPOption getPPAnalysisBlockImplicit <|> getPPOption getPPUniverses)
  let field? ← if fieldNotation then appFieldNotationCandidate? else pure none
  let (fnStx, _, argStxs) ← withBoundedAppFnArgs numArgs
    (do return (← delabHead insertExplicit, paramKinds.toList, Array.mkEmpty numArgs))
    (fun ⟨fnStx, paramKinds, argStxs⟩ => do
      let isInstImplicit := paramKinds.head? |>.map (·.bInfo == .instImplicit) |>.getD false
      let argStx ← if some argStxs.size = field?.map Prod.fst then
                     -- With field notation, we can erase parent projections for the object
                     withoutParentProjections (explicit := true) delab
                   else if ← getPPOption getPPAnalysisHole then `(_)
                   else if isInstImplicit == true then
                     withTypeAscription (cond := ← getPPOption getPPInstanceTypes) do
                       if ← getPPOption getPPInstances then delab else `(_)
                   else delab
      pure (fnStx, paramKinds.tailD [], argStxs.push argStx))
  if let some (idx, field) := field? then
    -- Delaborate using field notation
    let obj := argStxs[idx]!
    let mut head : Term ← `($obj.$(mkIdent field))
    if idx == 0 then
      -- If it's the first argument, then we can tag `obj.field` with the first app.
      head ← withBoundedAppFn (numArgs - 1) <| annotateTermInfo head
    return Syntax.mkApp head (argStxs.eraseIdx idx)
  else
    return Syntax.mkApp fnStx argStxs

/--
Delaborates a function application in the standard mode, where implicit arguments are generally not
included, unless `pp.analysis.namedArg` is set at that argument.

This delaborator is where `app_unexpander`s and the structure instance unexpander are applied, if `unexpand` is true.
When `unexpand` is true, also considers opportunities for field notation, which takes priority over other unexpanders.

Assumes `numArgs ≤ paramKinds.size`.
-/
def delabAppImplicitCore (unexpand : Bool) (numArgs : Nat) (delabHead : Delab) (paramKinds : Array ParamKind) : Delab := do
  let unexpand ← pure unexpand
    <&&> withBoundedAppFn numArgs do pure (← getExpr).consumeMData.isConst <&&> not <$> withMDatasOptions (getPPOption getPPUniverses)
  let field? ←
    if ← pure unexpand <&&> getPPOption getPPFieldNotation <&&> not <$> getPPOption getPPAnalysisNoDot then
      appFieldNotationCandidate?
    else
      pure none
  let (shouldUnexpand, fnStx, fieldIdx?, _, _, argStxs, argData) ←
    withBoundedAppFnArgs numArgs
      (do return (unexpand, ← delabHead, none, 0, paramKinds.toList, Array.mkEmpty numArgs, (Array.mkEmpty numArgs).push (unexpand, 0)))
      (fun (shouldUnexpand, fnStx, fieldIdx?, idx, paramKinds, argStxs, argData) => do
        /-
        - `argStxs` is the accumulated array of arguments that should be pretty printed
        - `argData` is a list of `Bool × Nat` used to figure out:
          1. whether an unexpander could be used for the prefix up to this argument and
          2. how many arguments we need to include after this one when annotating the result of unexpansion.
          Argument `argStxs[i]` corresponds to `argData[i+1]`, with `argData[0]` being for the head itself.
        -/
        if some idx = field?.map Prod.fst then
          -- This is the object for field notation.
          let fieldObj ← withoutParentProjections (explicit := false) delab
          return (false, fnStx, some argStxs.size, idx + 1, paramKinds.tailD [], argStxs.push fieldObj, argData.push (false, 1))
        let (argUnexpandable, stx?) ← mkArgStx (numArgs - idx - 1) paramKinds
        let shouldUnexpand := shouldUnexpand && argUnexpandable
        let (argStxs, argData) :=
          match stx?, argData.back with
          -- By default, a pretty-printed argument accounts for just itself.
          | some stx, _ => (argStxs.push stx, argData.push (shouldUnexpand, 1))
          -- A non-pretty-printed argument is accounted for by the previous pretty printed one.
          | none, (_, argCount) => (argStxs, argData.pop.push (shouldUnexpand, argCount + 1))
        return (shouldUnexpand, fnStx, fieldIdx?, idx + 1, paramKinds.tailD [], argStxs, argData))
  if let some fieldIdx := fieldIdx? then
    -- Delaborate using field notation
    let field := field?.get!.2
    let obj := argStxs[fieldIdx]!
    let mut head : Term ← `($obj.$(mkIdent field))
    if fieldIdx == 0 then
      -- If it's the first argument (after some implicit arguments), we can tag `obj.field` with a prefix of the application
      -- including the implicit arguments immediately before and after `obj`.
      head ← withBoundedAppFn (numArgs - argData[0]!.2 - argData[1]!.2) <| annotateTermInfo <| head
    return Syntax.mkApp head (argStxs.eraseIdx fieldIdx)
  if ← pure (argData.any Prod.fst) <&&> getPPOption getPPNotation then
    -- Try using an app unexpander for a prefix of the arguments.
    if let some stx ← (some <$> tryAppUnexpanders fnStx argStxs argData) <|> pure none then
      return stx
  let stx := Syntax.mkApp fnStx argStxs
  if ← pure shouldUnexpand <&&> getPPOption getPPStructureInstances then
    -- Try using the structure instance unexpander.
    -- It only makes sense applying this to the entire application, since structure instances cannot themselves be applied.
    if let some stx ← (some <$> unexpandStructureInstance stx) <|> pure none then
      return stx
  return stx
where
  mkNamedArg (name : Name) (argStx : Syntax) : DelabM (Bool × Option Syntax) :=
    return (false, ← `(Parser.Term.namedArgument| ($(mkIdent name) := $argStx)))
  /--
  If the argument should be pretty printed then it returns the syntax for that argument.
  The boolean is `false` if an unexpander should not be used for the application due to this argument.
  The argumnet `remainingArgs` is the number of arguments in the application after this one.
  -/
  mkArgStx (remainingArgs : Nat) (paramKinds : List ParamKind) : DelabM (Bool × Option Syntax) := do
    if ← getPPOption getPPAnalysisSkip then return (true, none)
    else if ← getPPOption getPPAnalysisHole then return (true, ← `(_))
    else
      let arg ← getExpr
      let param :: _ := paramKinds | unreachable!
      if ← getPPOption getPPAnalysisNamedArg then
        mkNamedArg param.name (← delab)
      else if param.defVal.isSome && remainingArgs == 0 && param.defVal.get! == arg then
        -- Assumption: `useAppExplicit` has already detected whether it is ok to omit this argument
        return (true, none)
      else if param.bInfo.isExplicit then
        return (true, ← delab)
      else if ← pure (param.name == `motive) <&&> shouldShowMotive arg (← getOptions) then
        mkNamedArg param.name (← delab)
      else
        return (true, none)
  /--
  Runs the given unexpanders, returning the resulting syntax if any are applicable, and otherwise fails.
  -/
  tryUnexpand (fs : List Unexpander) (stx : Syntax) : DelabM Syntax := do
    let ref ← getRef
    fs.firstM fun f =>
      match f stx |>.run ref |>.run () with
      | EStateM.Result.ok stx _ => return stx
      | _ => failure
  /--
  If the expression is a candidate for app unexpanders,
  try applying an app unexpander using some prefix of the arguments, longest prefix first.
  This function makes sure that the unexpanded syntax is annotated and given TermInfo so that it is hoverable in the InfoView.
  -/
  tryAppUnexpanders (fnStx : Term) (argStxs : Array Syntax) (argData : Array (Bool × Nat)) : Delab := do
    let .const c _ := (← getExpr).getAppFn.consumeMData | unreachable!
    let fs := appUnexpanderAttribute.getValues (← getEnv) c
    if fs.isEmpty then failure
    let rec go (prefixArgs : Nat) : DelabM Term := do
      let (unexpand, argCount) := argData[prefixArgs]!
      match prefixArgs with
      | 0 =>
        guard unexpand
        let stx ← tryUnexpand fs fnStx
        return Syntax.mkApp (← annotateTermInfo stx) argStxs
      | prefixArgs' + 1 =>
        (do guard unexpand
            let stx ← tryUnexpand fs <| Syntax.mkApp fnStx (argStxs.extract 0 prefixArgs)
            return Syntax.mkApp (← annotateTermInfo stx) (argStxs.extract prefixArgs argStxs.size))
        <|> withBoundedAppFn argCount (go prefixArgs')
    go argStxs.size

/--
Returns true if an application should use explicit mode when delaborating.
Explicit mode turns off unexpanders
-/
def useAppExplicit (numArgs : Nat) (paramKinds : Array ParamKind) : DelabM Bool := do
  -- If `pp.explicit` is set, then use explicit mode.
  -- (Note that explicit mode can decide to omit `@` if the application has no implicit arguments.)
  if ← getPPOption getPPExplicit then return true

  if ← withBoundedAppFn numArgs <| withMDatasOptions <| getPPOption getPPAnalysisBlockImplicit then
    return true

  -- If there was an error collecting ParamKinds, fall back to explicit mode.
  if paramKinds.size < numArgs then return true

  if numArgs < paramKinds.size then
    let nextParam := paramKinds[numArgs]!

    -- If the next parameter is implicit or inst implicit, fall back to explicit mode.
    -- This is necessary for `@Eq` for example.
    if nextParam.bInfo matches .implicit | .instImplicit then return true

  -- If any of the next parameters is explicit but has an optional value or is an autoparam, fall back to explicit mode.
  -- This is necessary since these are eagerly processed when elaborating.
  if paramKinds[numArgs:].any fun param => param.bInfo.isExplicit && !param.isRegularExplicit then return true

  return false

/--
Delaborates applications. Removes up to `maxArgs` arguments to form the "head" of the application.
* `delabHead` is a delaborator to use for the head of the expression.
  It is passed whether the result needs to have `@` inserted.
* If `unexpand` is true, then allow unexpanders and field notation.
  This should likely be set to `false` except in the main `delabApp` delaborator.

Propagates `pp.tagAppFns` into the head for `delabHead`.
-/
def delabAppCore (maxArgs : Nat) (delabHead : (insertExplicit : Bool) → Delab) (unexpand : Bool) : Delab := do
  let tagAppFn ← getPPOption getPPTagAppFns
  let delabHead' (insertExplicit : Bool) : Delab := withOptionAtCurrPos `pp.tagAppFns tagAppFn (delabHead insertExplicit)
  let e ← getExpr
  let fn := e.getBoundedAppFn maxArgs
  let args := e.getBoundedAppArgs maxArgs
  let paramKinds ← getParamKinds fn args
  if (← useAppExplicit args.size paramKinds) then
    -- Don't use field notation when `pp.tagAppFns` is true since that obscures the head application.
    delabAppExplicitCore (fieldNotation := unexpand && !tagAppFn) args.size delabHead' paramKinds
  else
    delabAppImplicitCore (unexpand := unexpand) args.size (delabHead' false) paramKinds

/--
Default delaborator for applications.
-/
@[builtin_delab app]
def delabApp : Delab := do
  let delabAppFn (insertExplicit : Bool) : Delab := do
    let stx ← if (← getExpr).consumeMData.isConst then withMDatasOptions delabConst else delab
    if insertExplicit && !stx.raw.isOfKind ``Lean.Parser.Term.explicit then `(@$stx) else pure stx
  delabAppCore (← getExpr).getAppNumArgs delabAppFn (unexpand := true)

/--
The `withOverApp` combinator allows delaborators to handle "over-application" by using the core
application delaborator to handle additional arguments.

For example, suppose `f : {A : Type} → Foo A → A` and we want to implement a delaborator for
applications `f x` to pretty print as `F[x]`. Because `A` is a type variable we might encounter
a term of the form `@f (A → B) x y`, which has an additional argument `y`.
With this combinator one can use an arity-2 delaborator to pretty print this as `F[x] y`.

* `arity`: the expected number of arguments to `f`.
  The combinator will fail if fewer than this number of arguments are passed,
  and if more than this number of arguments are passed the arguments are handled using
  the standard application delaborator.
* `x`: delaborates the head application of the expected arity (`f x` in the example).
  The value of `pp.tagAppFns` for the whole application is propagated to the expression that `x` sees.

In the event of overapplication, the delaborator `x` is wrapped in
`Lean.PrettyPrinter.Delaborator.withAnnotateTermInfo` to register `TermInfo` for the resulting term.
The effect of this is that the term is hoverable in the Infoview.

If the application would require inserting `@` around the result of `x`, the delaborator fails
since we cannot be sure that this insertion will be well-formed.
-/
def withOverApp (arity : Nat) (x : Delab) : Delab := do
  let n := (← getExpr).getAppNumArgs
  guard <| n ≥ arity
  if n == arity then
    x
  else
    let delabHead (insertExplicit : Bool) : Delab := do
      guard <| !insertExplicit
      withAnnotateTermInfo x
    delabAppCore (n - arity) delabHead (unexpand := false)

/-- State for `delabAppMatch` and helpers. -/
structure AppMatchState where
  info        : MatcherInfo
  matcherTy   : Expr
  params      : Array Expr := #[]
  motive      : Option (Term × Expr) := none
  motiveNamed : Bool := false
  discrs      : Array Term := #[]
  varNames    : Array (Array Name) := #[]
  rhss        : Array Term := #[]
  -- additional arguments applied to the result of the `match` expression
  moreArgs    : Array Term := #[]
/--
  Extract arguments of motive applications from the matcher type.
  For the example below: `#[#[`([])], #[`(a::as)]]` -/
private partial def delabPatterns (st : AppMatchState) : DelabM (Array (Array Term)) :=
  withReader (fun ctx => { ctx with inPattern := true, optionsPerPos := {} }) do
    let ty ← instantiateForall st.matcherTy st.params
    -- need to reduce `let`s that are lifted into the matcher type
    forallTelescopeReducing ty fun params _ => do
      -- skip motive and discriminators
      let alts := Array.ofSubarray params[1 + st.discrs.size:]
      alts.mapIdxM fun idx alt => do
        let ty ← inferType alt
        -- TODO: this is a hack; we are accessing the expression out-of-sync with the position
        -- Currently, we reset `optionsPerPos` at the beginning of `delabPatterns` to avoid
        -- incorrectly considering annotations.
        withTheReader SubExpr ({ · with expr := ty }) $
          usingNames st.varNames[idx]! do
            withAppFnArgs (pure #[]) (fun pats => do pure $ pats.push (← delab))
where
  usingNames {α} (varNames : Array Name) (x : DelabM α) : DelabM α :=
    usingNamesAux 0 varNames x
  usingNamesAux {α} (i : Nat) (varNames : Array Name) (x : DelabM α) : DelabM α :=
    if i < varNames.size then
      withBindingBody varNames[i]! <| usingNamesAux (i+1) varNames x
    else
      x

/-- Skip `numParams` binders, and execute `x varNames` where `varNames` contains the new binder names. -/
private partial def skippingBinders {α} (numParams : Nat) (x : Array Name → DelabM α) : DelabM α :=
  loop numParams #[]
where
  loop : Nat → Array Name → DelabM α
    | 0,   varNames => x varNames
    | n+1, varNames => do
      let rec visitLambda : DelabM α := do
        let varName := (← getExpr).bindingName!.eraseMacroScopes
        -- Pattern variables cannot shadow each other
        if varNames.contains varName then
          let varName := (← getLCtx).getUnusedName varName
          withBindingBody varName do
            loop n (varNames.push varName)
        else
          withBindingBodyUnusedName fun id => do
            loop n (varNames.push id.getId)
      let e ← getExpr
      if e.isLambda then
        visitLambda
      else
        -- eta expand `e`
        let e ← forallTelescopeReducing (← inferType e) fun xs _ => do
          if xs.size == 1 && (← inferType xs[0]!).isConstOf ``Unit then
            -- `e` might be a thunk create by the dependent pattern matching compiler, and `xs[0]` may not even be a pattern variable.
            -- If it is a pattern variable, it doesn't look too bad to use `()` instead of the pattern variable.
            -- If it becomes a problem in the future, we should modify the dependent pattern matching compiler, and make sure
            -- it adds an annotation to distinguish these two cases.
            mkLambdaFVars xs (mkApp e (mkConst ``Unit.unit))
          else
            mkLambdaFVars xs (mkAppN e xs)
        withTheReader SubExpr (fun ctx => { ctx with expr := e }) visitLambda

/--
  Delaborate applications of "matchers" such as
  ```
  List.map.match_1 : {α : Type _} →
    (motive : List α → Sort _) →
      (x : List α) → (Unit → motive List.nil) → ((a : α) → (as : List α) → motive (a :: as)) → motive x
  ```
-/
@[builtin_delab app]
def delabAppMatch : Delab := whenPPOption getPPNotation <| whenPPOption getPPMatch do
  -- incrementally fill `AppMatchState` from arguments
  let st ← withAppFnArgs
    (do
      let (Expr.const c us) ← getExpr | failure
      let (some info) ← getMatcherInfo? c | failure
      let matcherTy ← instantiateTypeLevelParams (← getConstInfo c) us
      return { matcherTy, info : AppMatchState })
    (fun st => do
      if st.params.size < st.info.numParams then
        return { st with params := st.params.push (← getExpr) }
      else if st.motive.isNone then
        -- store motive argument separately
        let lamMotive ← getExpr
        let piMotive ← lambdaTelescope lamMotive fun xs body => mkForallFVars xs body
        -- TODO: pp.analyze has not analyzed `piMotive`, only `lamMotive`
        -- Thus the binder types won't have any annotations
        let piStx ← withTheReader SubExpr (fun cfg => { cfg with expr := piMotive }) delab
        let named ← getPPOption getPPAnalysisNamedArg
        return { st with motive := (piStx, lamMotive), motiveNamed := named }
      else if st.discrs.size < st.info.numDiscrs then
        let idx := st.discrs.size
        let discr ← delab
        if let some hName := st.info.discrInfos[idx]!.hName? then
          -- TODO: we should check whether the corresponding binder name, matches `hName`.
          -- If it does not we should pretty print this `match` as a regular application.
          return { st with discrs := st.discrs.push (← `(matchDiscr| $(mkIdent hName) : $discr)) }
        else
          return { st with discrs := st.discrs.push (← `(matchDiscr| $discr:term)) }
      else if st.rhss.size < st.info.altNumParams.size then
        /- We save the variables names here to be able to implement safe_shadowing.
           The pattern delaboration must use the names saved here. -/
        let (varNames, rhs) ← skippingBinders st.info.altNumParams[st.rhss.size]! fun varNames => do
          let rhs ← delab
          return (varNames, rhs)
        return { st with rhss := st.rhss.push rhs, varNames := st.varNames.push varNames }
      else
        return { st with moreArgs := st.moreArgs.push (← delab) })

  if st.discrs.size < st.info.numDiscrs || st.rhss.size < st.info.altNumParams.size then
    -- underapplied
    failure

  match st.discrs, st.rhss with
  | #[discr], #[] =>
    let stx ← `(nomatch $discr)
    return Syntax.mkApp stx st.moreArgs
  | _,        #[] => failure
  | _,        _   =>
    let pats ← delabPatterns st
    let stx ← do
      let (piStx, lamMotive) := st.motive.get!
      let opts ← getOptions
      -- TODO: disable the match if other implicits are needed?
      if ← pure st.motiveNamed <||> shouldShowMotive lamMotive opts then
        `(match (motive := $piStx) $[$st.discrs:matchDiscr],* with $[| $pats,* => $st.rhss]*)
      else
        `(match $[$st.discrs:matchDiscr],* with $[| $pats,* => $st.rhss]*)
    return Syntax.mkApp stx st.moreArgs

/--
Delaborates applications of the form `letFun v (fun x => b)` as `let_fun x := v; b`.
-/
@[builtin_delab app.letFun]
def delabLetFun : Delab := whenPPOption getPPNotation <| withOverApp 4 do
  let e ← getExpr
  guard <| e.getAppNumArgs == 4
  let Expr.lam n _ b _ := e.appArg! | failure
  let n ← getUnusedName n b
  let stxV ← withAppFn <| withAppArg delab
  let (stxN, stxB) ← withAppArg <| withBindingBody' n (mkAnnotatedIdent n) fun stxN => return (stxN, ← delab)
  if ← getPPOption getPPLetVarTypes <||> getPPOption getPPAnalysisLetVarType then
    let stxT ← SubExpr.withNaryArg 0 delab
    `(let_fun $stxN : $stxT := $stxV; $stxB)
  else
    `(let_fun $stxN := $stxV; $stxB)

@[builtin_delab mdata]
def delabMData : Delab := do
  if let some _ := inaccessible? (← getExpr) then
    let s ← withMDataExpr delab
    if (← read).inPattern then
      `(.($s)) -- We only include the inaccessible annotation when we are delaborating patterns
    else
      return s
  else if let some _ := isLHSGoal? (← getExpr) then
    withMDataExpr <| withAppFn <| withAppArg <| delab
  else
    withMDataOptions delab

/--
Check for a `Syntax.ident` of the given name anywhere in the tree.
This is usually a bad idea since it does not check for shadowing bindings,
but in the delaborator we assume that bindings are never shadowed.
-/
partial def hasIdent (id : Name) : Syntax → Bool
  | Syntax.ident _ _ id' _ => id == id'
  | Syntax.node _ _ args   => args.any (hasIdent id)
  | _                      => false

/--
Return `true` iff current binder should be merged with the nested
binder, if any, into a single binder group:
* both binders must have same binder info and domain
* they cannot be inst-implicit (`[a b : A]` is not valid syntax)
* `pp.binderTypes` must be the same value for both terms
* prefer `fun a b` over `fun (a b)`
-/
private def shouldGroupWithNext : DelabM Bool := do
  let e ← getExpr
  let ppEType ← getPPOption (getPPBinderTypes e)
  let go (e' : Expr) := do
    let ppE'Type ← withBindingBody `_ $ getPPOption (getPPBinderTypes e)
    pure $ e.binderInfo == e'.binderInfo &&
      e.bindingDomain! == e'.bindingDomain! &&
      e'.binderInfo != BinderInfo.instImplicit &&
      ppEType == ppE'Type &&
      (e'.binderInfo != BinderInfo.default || ppE'Type)
  match e with
  | Expr.lam _ _     e'@(Expr.lam _ _ _ _) _     => go e'
  | Expr.forallE _ _ e'@(Expr.forallE _ _ _ _) _ => go e'
  | _ => pure false
where
  getPPBinderTypes (e : Expr) :=
    if e.isForall then getPPPiBinderTypes else getPPFunBinderTypes

private partial def delabBinders (delabGroup : Array Syntax → Syntax → Delab) : optParam (Array Syntax) #[] → Delab
  -- Accumulate names (`Syntax.ident`s with position information) of the current, unfinished
  -- binder group `(d e ...)` as determined by `shouldGroupWithNext`. We cannot do grouping
  -- inside-out, on the Syntax level, because it depends on comparing the Expr binder types.
  | curNames => do
    if ← shouldGroupWithNext then
      -- group with nested binder => recurse immediately
      withBindingBodyUnusedName fun stxN => delabBinders delabGroup (curNames.push stxN)
    else
      -- don't group => delab body and prepend current binder group
      let (stx, stxN) ← withBindingBodyUnusedName fun stxN => return (← delab, stxN)
      delabGroup (curNames.push stxN) stx

@[builtin_delab lam]
def delabLam : Delab :=
  delabBinders fun curNames stxBody => do
    let e ← getExpr
    let stxT ← withBindingDomain delab
    let ppTypes ← getPPOption getPPFunBinderTypes
    let usedDownstream := curNames.any (fun n => hasIdent n.getId stxBody)

    -- leave lambda implicit if possible
    -- TODO: for now we just always block implicit lambdas when delaborating. We can revisit.
    -- Note: the current issue is that it requires state, i.e. if *any* previous binder was implicit,
    -- it doesn't seem like we can leave a subsequent binder implicit.
    let blockImplicitLambda := true
    /-
    let blockImplicitLambda := expl ||
      e.binderInfo == BinderInfo.default ||
      -- Note: the following restriction fixes many issues with roundtripping,
      -- but this condition may still not be perfectly in sync with the elaborator.
      e.binderInfo == BinderInfo.instImplicit ||
      Elab.Term.blockImplicitLambda stxBody ||
      usedDownstream
    -/

    if !blockImplicitLambda then
      pure stxBody
    else
      let defaultCase (_ : Unit) : Delab := do
        if ppTypes then
          -- "default" binder group is the only one that expects binder names
          -- as a term, i.e. a single `Syntax.ident` or an application thereof
          let stxCurNames ←
            if curNames.size > 1 then
              `($(curNames.get! 0) $(curNames.eraseIdx 0)*)
            else
              pure $ curNames.get! 0;
          `(funBinder| ($stxCurNames : $stxT))
        else
          pure curNames.back  -- here `curNames.size == 1`
      let group ← match e.binderInfo, ppTypes with
        | BinderInfo.default,        _      => defaultCase ()
        | BinderInfo.implicit,       true   => `(funBinder| {$curNames* : $stxT})
        | BinderInfo.implicit,       false  => `(funBinder| {$curNames*})
        | BinderInfo.strictImplicit, true   => `(funBinder| ⦃$curNames* : $stxT⦄)
        | BinderInfo.strictImplicit, false  => `(funBinder| ⦃$curNames*⦄)
        | BinderInfo.instImplicit,   _     =>
          if usedDownstream then `(funBinder| [$curNames.back : $stxT])  -- here `curNames.size == 1`
          else  `(funBinder| [$stxT])
      let (binders, stxBody) :=
        match stxBody with
        | `(fun $binderGroups* => $stxBody) => (#[group] ++ binderGroups, stxBody)
        | _                                 => (#[group], stxBody)
      if ← getPPOption getPPUnicodeFun then
        `(fun $binders* ↦ $stxBody)
      else
        `(fun $binders* => $stxBody)

/--
Similar to `delabBinders`, but tracking whether `forallE` is dependent or not.

See issue #1571
-/
private partial def delabForallBinders (delabGroup : Array Syntax → Bool → Syntax → Delab) (curNames : Array Syntax := #[]) (curDep := false) : Delab := do
  let dep := !(← getExpr).isArrow
  if !curNames.isEmpty && dep != curDep then
    -- don't group
    delabGroup curNames curDep (← delab)
  else
    let curDep := dep
    if ← shouldGroupWithNext then
      -- group with nested binder => recurse immediately
      withBindingBodyUnusedName fun stxN => delabForallBinders delabGroup (curNames.push stxN) curDep
    else
      -- don't group => delab body and prepend current binder group
      let (stx, stxN) ← withBindingBodyUnusedName fun stxN => return (← delab, stxN)
      delabGroup (curNames.push stxN) curDep stx

@[builtin_delab forallE]
def delabForall : Delab := do
  delabForallBinders fun curNames dependent stxBody => do
    let e ← getExpr
    let prop ← try isProp e catch _ => pure false
    let stxT ← withBindingDomain delab
    let group ← match e.binderInfo with
    | BinderInfo.implicit       => `(bracketedBinderF|{$curNames* : $stxT})
    | BinderInfo.strictImplicit => `(bracketedBinderF|⦃$curNames* : $stxT⦄)
    -- here `curNames.size == 1`
    | BinderInfo.instImplicit   => `(bracketedBinderF|[$curNames.back : $stxT])
    | _                         =>
      -- NOTE: non-dependent arrows are available only for the default binder info
      if dependent then
        if prop && !(← getPPOption getPPPiBinderTypes) then
          return ← `(∀ $curNames:ident*, $stxBody)
        else
          `(bracketedBinderF|($curNames* : $stxT))
      else
        return ← curNames.foldrM (fun _ stxBody => `($stxT → $stxBody)) stxBody
    if prop then
      match stxBody with
      | `(∀ $groups*, $stxBody) => `(∀ $group $groups*, $stxBody)
      | _                       => `(∀ $group, $stxBody)
    else
      `($group:bracketedBinder → $stxBody)

@[builtin_delab letE]
def delabLetE : Delab := do
  let Expr.letE n t v b _ ← getExpr | unreachable!
  let n ← getUnusedName n b
  let stxV ← descend v 1 delab
  let (stxN, stxB) ← withLetDecl n t v fun fvar => do
    let b := b.instantiate1 fvar
    return (← mkAnnotatedIdent n fvar, ← descend b 2 delab)
  if ← getPPOption getPPLetVarTypes <||> getPPOption getPPAnalysisLetVarType then
    let stxT ← descend t 0 delab
    `(let $stxN : $stxT := $stxV; $stxB)
  else `(let $stxN := $stxV; $stxB)

@[builtin_delab app.Char.ofNat]
def delabChar : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 1
  let .lit (.natVal n) := e.appArg! | failure
  return quote (Char.ofNat n)

@[builtin_delab lit]
def delabLit : Delab := do
  let Expr.lit l ← getExpr | unreachable!
  match l with
  | Literal.natVal n =>
    if ← getPPOption getPPNatLit then
      `(nat_lit $(quote n))
    else
      return quote n
  | Literal.strVal s => return quote s

/--
Core function that delaborates a natural number (an `OfNat.ofNat` literal).
-/
def delabOfNatCore (showType : Bool := false) : Delab := do
  let .app (.app (.app (.const ``OfNat.ofNat ..) _) (.lit (.natVal n))) _ ← getExpr | failure
  let stx ← annotateTermInfo <| quote n
  if showType then
    let ty ← withNaryArg 0 delab
    `(($stx : $ty))
  else
    return stx

/--
Core function that delaborates a negative integer literal (a `Neg.neg` applied to `OfNat.ofNat`).
-/
def delabNegIntCore (showType : Bool := false) : Delab := do
  guard <| (← getExpr).isAppOfArity ``Neg.neg 3
  let n ← withAppArg delabOfNatCore
  let stx ← annotateTermInfo (← `(- $n))
  if showType then
    let ty ← withNaryArg 0 delab
    `(($stx : $ty))
  else
    return stx

/--
Core function that delaborates a rational literal that is the division of an integer literal
by a natural number literal.
The division must be homogeneous for it to count as a rational literal.
-/
def delabDivRatCore (showType : Bool := false) : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``HDiv.hDiv 6
  guard <| e.getArg! 0 == e.getArg! 1
  guard <| e.getArg! 0 == e.getArg! 2
  let p ← withAppFn <| withAppArg <| (delabOfNatCore <|> delabNegIntCore)
  let q ← withAppArg <| delabOfNatCore
  let stx ← annotateTermInfo (← `($p / $q))
  if showType then
    let ty ← withNaryArg 0 delab
    `(($stx : $ty))
  else
    return stx

/--
Delaborates an `OfNat.ofNat` literal.
`@OfNat.ofNat _ n _` ~> `n`.
-/
@[builtin_delab app.OfNat.ofNat]
def delabOfNat : Delab := whenPPOption getPPCoercions <| withOverApp 3 do
  delabOfNatCore (showType := (← getPPOption getPPNumericTypes))

/--
Delaborates the negative of an `OfNat.ofNat` literal.
`-@OfNat.ofNat _ n _` ~> `-n`
-/
@[builtin_delab app.Neg.neg]
def delabNeg : Delab := whenPPOption getPPCoercions do
  delabNegIntCore (showType := (← getPPOption getPPNumericTypes))

/--
Delaborates a rational number literal.
`@OfNat.ofNat _ n _ / @OfNat.ofNat _ m` ~> `n / m`
and `-@OfNat.ofNat _ n _ / @OfNat.ofNat _ m` ~> `-n / m`
-/
@[builtin_delab app.HDiv.hDiv]
def delabHDiv : Delab := whenPPOption getPPCoercions do
  delabDivRatCore (showType := (← getPPOption getPPNumericTypes))

-- `@OfDecimal.ofDecimal _ _ m s e` ~> `m*10^(sign * e)` where `sign == 1` if `s = false` and `sign = -1` if `s = true`
@[builtin_delab app.OfScientific.ofScientific]
def delabOfScientific : Delab := whenPPOption getPPCoercions <| withOverApp 5 do
  let expr ← getExpr
  guard <| expr.getAppNumArgs == 5
  let .lit (.natVal m) ← pure (expr.getArg! 2) | failure
  let .lit (.natVal e) ← pure (expr.getArg! 4) | failure
  let s ← match expr.getArg! 3 with
    | Expr.const ``Bool.true _  => pure true
    | Expr.const ``Bool.false _ => pure false
    | _ => failure
  let str  := toString m
  if s && e == str.length then
    return Syntax.mkScientificLit ("0." ++ str)
  else if s && e < str.length then
    let mStr := str.extract 0 ⟨str.length - e⟩
    let eStr := str.extract ⟨str.length - e⟩ ⟨str.length⟩
    return Syntax.mkScientificLit (mStr ++ "." ++ eStr)
  else
    return Syntax.mkScientificLit (str ++ "e" ++ (if s then "-" else "") ++ toString e)

/--
Delaborate a projection primitive. These do not usually occur in
user code, but are pretty-printed when e.g. `#print`ing a projection
function.
-/
@[builtin_delab proj]
def delabProj : Delab := do
  let Expr.proj _ idx _ ← getExpr | unreachable!
  let e ← withProj delab
  -- not perfectly authentic: elaborates to the `idx`-th named projection
  -- function (e.g. `e.1` is `Prod.fst e`), which unfolds to the actual
  -- `proj`.
  let idx := Syntax.mkLit fieldIdxKind (toString (idx + 1));
  `($(e).$idx:fieldIdx)

/--
This delaborator tries to elide functions which are known coercions.
For example, `Int.ofNat` is a coercion, so instead of printing `ofNat n` we just print `↑n`,
and when re-parsing this we can (usually) recover the specific coercion being used.
-/
@[builtin_delab app]
def coeDelaborator : Delab := whenPPOption getPPCoercions do
  let e ← getExpr
  let .const declName _ := e.getAppFn | failure
  let some info ← Meta.getCoeFnInfo? declName | failure
  let n := e.getAppNumArgs
  withOverApp info.numArgs do
    match info.type with
    | .coe => `(↑$(← withNaryArg info.coercee delab))
    | .coeFun =>
      if n = info.numArgs then
        `(⇑$(← withNaryArg info.coercee delab))
      else
        withNaryArg info.coercee delab
    | .coeSort => `(↥$(← withNaryArg info.coercee delab))

@[builtin_delab app.dite]
def delabDIte : Delab := whenPPOption getPPNotation <| withOverApp 5 do
  -- Note: we keep this as a delaborator for now because it actually accesses the expression.
  guard $ (← getExpr).getAppNumArgs == 5
  let c ← withAppFn $ withAppFn $ withAppFn $ withAppArg delab
  let (t, h) ← withAppFn $ withAppArg $ delabBranch none
  let (e, _) ← withAppArg $ delabBranch h
  `(if $(mkIdent h):ident : $c then $t else $e)
where
  delabBranch (h? : Option Name) : DelabM (Syntax × Name) := do
    let e ← getExpr
    guard e.isLambda
    let h ← match h? with
      | some h => return (← withBindingBody h delab, h)
      | none   => withBindingBodyUnusedName fun h => do
        return (← delab, h.getId)

@[builtin_delab app.cond]
def delabCond : Delab := whenPPOption getPPNotation <| withOverApp 4 do
  guard $ (← getExpr).getAppNumArgs == 4
  let c ← withAppFn $ withAppFn $ withAppArg delab
  let t ← withAppFn $ withAppArg delab
  let e ← withAppArg delab
  `(bif $c then $t else $e)

@[builtin_delab app.namedPattern]
def delabNamedPattern : Delab := do
  -- Note: we keep this as a delaborator because it accesses the DelabM context
  guard (← read).inPattern
  guard $ (← getExpr).getAppNumArgs == 4
  let x ← withAppFn $ withAppFn $ withAppArg delab
  let p ← withAppFn $ withAppArg delab
  -- TODO: we should hide `h` if it has an inaccessible name and is not used in the rhs
  let h ← withAppArg delab
  guard x.raw.isIdent
  `($x:ident@$h:ident:$p:term)

-- Sigma and PSigma delaborators
def delabSigmaCore (sigma : Bool) : Delab := whenPPOption getPPNotation do
  guard $ (← getExpr).getAppNumArgs == 2
  guard $ (← getExpr).appArg!.isLambda
  withAppArg do
    let α ← withBindingDomain delab
    let bodyExpr := (← getExpr).bindingBody!
    withBindingBodyUnusedName fun n => do
      let b ← delab
      if bodyExpr.hasLooseBVars then
        if sigma then `(($n:ident : $α) × $b) else `(($n:ident : $α) ×' $b)
      else
        if sigma then `((_ : $α) × $b) else `((_ : $α) ×' $b)

@[builtin_delab app.Sigma]
def delabSigma : Delab := delabSigmaCore (sigma := true)

@[builtin_delab app.PSigma]
def delabPSigma : Delab := delabSigmaCore (sigma := false)

partial def delabDoElems : DelabM (List Syntax) := do
  let e ← getExpr
  if e.isAppOfArity ``Bind.bind 6 then
    -- Bind.bind.{u, v} : {m : Type u → Type v} → [self : Bind m] → {α β : Type u} → m α → (α → m β) → m β
    let α := e.getAppArgs[2]!
    let ma ← withAppFn $ withAppArg delab
    withAppArg do
      match (← getExpr) with
      | Expr.lam _ _ body _ =>
        withBindingBodyUnusedName fun n => do
          if body.hasLooseBVars then
            prependAndRec `(doElem|let $n:term ← $ma:term)
          else if α.isConstOf ``Unit || α.isConstOf ``PUnit then
            prependAndRec `(doElem|$ma:term)
          else
            prependAndRec `(doElem|let _ ← $ma:term)
      | _ => failure
  else if e.isLet then
    let Expr.letE n t v b _ ← getExpr | unreachable!
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delab
    withLetDecl n t v fun fvar =>
      let b := b.instantiate1 fvar
      descend b 2 $
        prependAndRec `(doElem|let $(mkIdent n) : $stxT := $stxV)
  else if e.isLetFun then
    -- letFun.{u, v} : {α : Sort u} → {β : α → Sort v} → (v : α) → ((x : α) → β x) → β v
    let stxT ← withNaryArg 0 delab
    let stxV ← withNaryArg 2 delab
    withAppArg do
      match (← getExpr) with
      | Expr.lam .. =>
        withBindingBodyUnusedName fun n => do
          prependAndRec `(doElem|have $n:term : $stxT := $stxV)
      | _ => failure
  else
    let stx ← delab
    return [← `(doElem|$stx:term)]
  where
    prependAndRec x : DelabM _ := List.cons <$> x <*> delabDoElems

@[builtin_delab app.Bind.bind]
def delabDo : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``Bind.bind 6
  let elems ← delabDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

def reifyName : Expr → DelabM Name
  | .const ``Lean.Name.anonymous .. => return Name.anonymous
  | .app (.app (.const ``Lean.Name.str ..) n) (.lit (.strVal s)) => return (← reifyName n).mkStr s
  | .app (.app (.const ``Lean.Name.num ..) n) (.lit (.natVal i)) => return (← reifyName n).mkNum i
  | _ => failure

@[builtin_delab app.Lean.Name.str]
def delabNameMkStr : Delab := whenPPOption getPPNotation do
  let n ← reifyName (← getExpr)
  -- not guaranteed to be a syntactically valid name, but usually more helpful than the explicit version
  return mkNode ``Lean.Parser.Term.quotedName #[Syntax.mkNameLit s!"`{n}"]

@[builtin_delab app.Lean.Name.num]
def delabNameMkNum : Delab := delabNameMkStr

open Parser Command Term in
@[run_builtin_parser_attribute_hooks]
-- use `termParser` instead of `declId` so we can reuse `delabConst`
def declSigWithId := leading_parser termParser maxPrec >> declSig

private unsafe def evalSyntaxConstantUnsafe (env : Environment) (opts : Options) (constName : Name) : ExceptT String Id Syntax :=
  env.evalConstCheck Syntax opts ``Syntax constName

@[implemented_by evalSyntaxConstantUnsafe]
private opaque evalSyntaxConstant (env : Environment) (opts : Options) (constName : Name) : ExceptT String Id Syntax := throw ""

/--
Pretty-prints a constant `c` as `c.{<levels>} <params> : <type>`.

If `universes` is `false`, then the universe level parameters are omitted.
-/
partial def delabConstWithSignature (universes : Bool := true) : Delab := do
  let e ← getExpr
  -- use virtual expression node of arity 2 to separate name and type info
  let idStx ← descend e 0 <|
    withOptions (pp.universes.set · universes |> (pp.fullNames.set · true)) <|
      delabConst
  descend (← inferType e) 1 <|
    delabParams {} idStx #[]
where
  /--
  For types in the signature, we want to be sure pi binder types are pretty printed.
  -/
  delabTy : DelabM Term := withOptions (pp.piBinderTypes.set · true) delab
  /-
  Similar to `delabBinders`, but does not uniquify binder names (since for named arguments we want to know the name),
  and it always merges binder groups when possible.
  Once it reaches a binder with an inaccessible name, or a name that has already been used,
  the remaining binders appear in pi types after the `:` of the declaration.
  -/
  delabParams (bindingNames : NameSet) (idStx : Ident) (groups : TSyntaxArray ``bracketedBinder) := do
    let e ← getExpr
    if e.isForall && e.binderInfo.isInstImplicit && e.bindingName!.hasMacroScopes then
      -- Assumption: this instance can be found by instance search, so it does not need to be named.
      -- The oversight here is that this inaccessible name can appear in the pretty printed expression.
      -- We could check to see whether the instance appears in the type and avoid omitting the instance name,
      -- but this would be the usual case.
      let group ← withBindingDomain do `(bracketedBinderF|[$(← delabTy)])
      withBindingBody e.bindingName! <| delabParams bindingNames idStx (groups.push group)
    else if e.isForall && !e.bindingName!.hasMacroScopes && !bindingNames.contains e.bindingName! then
      delabParamsAux bindingNames idStx groups #[]
    else
      let type ← delabTy
      `(declSigWithId| $idStx:ident $groups* : $type)
  /--
  Inner loop for `delabParams`, collecting binders.
  Invariants:
  - The current expression is a forall.
  - It has a name that's not inaccessible.
  - It has a name that hasn't been used yet.
  -/
  delabParamsAux (bindingNames : NameSet) (idStx : Ident) (groups : TSyntaxArray ``bracketedBinder) (curIds : Array Ident) := do
    let e@(.forallE n d e' i) ← getExpr | unreachable!
    let bindingNames := bindingNames.insert n
    let stxN := mkIdent n
    let curIds := curIds.push ⟨stxN⟩
    if shouldGroupWithNext bindingNames e e' then
      withBindingBody n <| delabParamsAux bindingNames idStx groups curIds
    else
      let group ← withBindingDomain do
        match i with
        | .implicit       => `(bracketedBinderF|{$curIds* : $(← delabTy)})
        | .strictImplicit => `(bracketedBinderF|⦃$curIds* : $(← delabTy)⦄)
        | .instImplicit   => `(bracketedBinderF|[$stxN : $(← delabTy)])
        | _ =>
          if d.isOptParam then
            `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := $(← withAppArg delabTy)))
          else if let some (.const tacticDecl _) := d.getAutoParamTactic? then
            let tacticSyntax ← ofExcept <| evalSyntaxConstant (← getEnv) (← getOptions) tacticDecl
            `(bracketedBinderF|($curIds* : $(← withAppFn <| withAppArg delabTy) := by $tacticSyntax))
          else
            `(bracketedBinderF|($curIds* : $(← delabTy)))
      withBindingBody n <| delabParams bindingNames idStx (groups.push group)
  /-
  Given the forall `e` with body `e'`, determines if the binder from `e'` (if it is a forall) should be grouped with `e`'s binder.
  -/
  shouldGroupWithNext (bindingNames : NameSet) (e e' : Expr) : Bool :=
    e'.isForall &&
    -- At the first sign of an inaccessible name, stop merging binders:
    !e'.bindingName!.hasMacroScopes &&
    -- If it's a name that has already been used, stop merging binders:
    !bindingNames.contains e'.bindingName! &&
    e.binderInfo == e'.binderInfo &&
    e.bindingDomain! == e'.bindingDomain! &&
    -- Inst implicits can't be grouped:
    e'.binderInfo != BinderInfo.instImplicit

end Lean.PrettyPrinter.Delaborator
