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

def delabMVarAux (m : MVarId) : DelabM Term := do
  let mkMVarPlaceholder : DelabM Term := `(?_)
  let mkMVar (n : Name) : DelabM Term := `(?$(mkIdent n))
  withTypeAscription (cond := ← getPPOption getPPMVarsWithType) do
    if ← getPPOption getPPMVars then
      match (← m.getDecl).userName with
      | .anonymous =>
        if ← getPPOption getPPMVarsAnonymous then
          mkMVar <| m.name.replacePrefix `_uniq `m
        else
          mkMVarPlaceholder
      | n => mkMVar n
    else
      mkMVarPlaceholder

@[builtin_delab mvar]
def delabMVar : Delab := do
  let Expr.mvar n ← getExpr | unreachable!
  delabMVarAux n

@[builtin_delab sort]
def delabSort : Delab := do
  let Expr.sort l ← getExpr | unreachable!
  match l with
  | Level.zero => `(Prop)
  | Level.succ .zero => `(Type)
  | _ =>
    let mvars ← getPPOption getPPMVarsLevels
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
    let mvars ← getPPOption getPPMVarsLevels
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
    /- Note that we don't flatten anonymous constructor notation. Only a complete such notation receives TermInfo,
       and flattening would cause the flattened-in notation to lose its TermInfo.
       Potentially it would be justified to flatten anonymous constructor notation when the terms are
       from the same type family (think `Sigma`), but for now users can write a custom delaborator in such instances. -/
    return ← withTypeAscription (cond := (← withType <| getPPOption getPPStructureInstanceType)) do
      `(⟨$[$(stx[1].getArgs)],*⟩)
  let args := e.getAppArgs
  let fieldVals := args.extract s.numParams args.size
  for h : idx in [:fieldNames.size] do
    let fieldName := fieldNames[idx]
    if (← getPPOption getPPStructureInstancesFlatten) && (Lean.isSubobjectField? env s.induct fieldName).isSome then
      match stx[1][idx] with
      | `({ $fields',* $[: $_]?}) =>
        -- We have found a subobject field that itself is printed with structure instance notation.
        -- Scavenge its fields.
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
  There are some kinds of expressions that cause issues with field notation, so we prevent using it in these cases.
  -/
  let obj := e.getArg! idx
  --  `(2).fn` is unlikely to elaborate.
  if obj.isRawNatLit || obj.isAppOfArity ``OfNat.ofNat 3 || obj.isAppOfArity ``OfScientific.ofScientific 5 then
    return none
  -- `(?m).fn` is unlikely to elaborate. https://github.com/leanprover/lean4/issues/5993
  -- We also exclude metavariable applications (these are delayed assignments for example)
  if obj.getAppFn.isMVar then
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

-- TODO(kmill): make sure that we only strip projections so long as it doesn't change how it elaborates.
-- This affects `withoutParentProjections` as well.

/-- Strips parent projections from `s`. Assumes that the current SubExpr is the same as the one used when delaborating `s`. -/
private partial def stripParentProjections (s : Term) : DelabM Term :=
  match s with
  | `($x.$f:ident) => do
    if let some field ← try parentProj? false (← getExpr) catch _ => pure none then
      if f.getId == field then
        withAppArg <| stripParentProjections x
      else
        return s
    else
      return s
  | _ => return s

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

/-- Records how a particular argument to a function is delaborated, in non-explicit mode. -/
inductive AppImplicitArg
  /-- An argument to skip, like an implicit argument. -/
  | skip
  /-- A regular argument. -/
  | regular (s : Term)
  /-- A regular argument that, if it comes as the last argument, may be omitted. -/
  | optional (name : Name) (s : Term)
  /-- It's a named argument. Named arguments inhibit applying unexpanders. -/
  | named (s : TSyntax ``Parser.Term.namedArgument)
  deriving Inhabited

/-- Whether unexpanding is allowed with this argument. -/
def AppImplicitArg.canUnexpand : AppImplicitArg → Bool
  | .regular .. | .optional .. | .skip => true
  | .named .. => false

/-- If the argument has associated syntax, returns it. -/
def AppImplicitArg.syntax? : AppImplicitArg → Option Syntax
  | .skip => none
  | .regular s => s
  | .optional _ s => s
  | .named s => s

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
  let (fnStx, args') ←
    withBoundedAppFnArgs numArgs
      (do return ((← delabHead), Array.mkEmpty numArgs))
      (fun (fnStx, args) => return (fnStx, args.push (← mkArg paramKinds[args.size]!)))

  -- Strip off optional arguments. We save the original `args'` for structure instance notation
  let args := args'.popWhile (· matches .optional ..)

  -- App unexpanders
  if ← pure unexpand <&&> getPPOption getPPNotation then
    -- Try using an app unexpander for a prefix of the arguments.
    if let some stx ← (some <$> tryAppUnexpanders fnStx args) <|> pure none then
      return stx

  -- Structure instance notation
  if ← pure (unexpand && args'.all (·.canUnexpand)) <&&> getPPOption getPPStructureInstances then
    -- Try using the structure instance unexpander.
    let stx := Syntax.mkApp fnStx (args'.filterMap (·.syntax?))
    if let some stx ← (some <$> unexpandStructureInstance stx) <|> pure none then
      return stx

  -- Field notation
  if let some (fieldIdx, field) := field? then
    if h : fieldIdx < args.size then
      let obj? : Option Term ← do
        let arg := args[fieldIdx]
        if let .regular s := arg then
          withNaryArg fieldIdx <| some <$> stripParentProjections s
        else
          pure none
      if let some obj := obj? then
        let isFirst := args[0:fieldIdx].all (· matches .skip)
        -- Clear the `obj` argument from `args`.
        let args' := args.set! fieldIdx .skip
        let mut head : Term ← `($obj.$(mkIdent field))
        if isFirst then
          -- If the object is the first argument (after some implicit arguments),
          -- we can annotate `obj.field` with the prefix of the application
          -- that includes all the implicit arguments immediately before and after `obj`.
          let objArity := args'.findIdx? (fun a => !(a matches .skip)) |>.getD args'.size
          head ← withBoundedAppFn (numArgs - objArity) <| annotateTermInfo <| head
        return Syntax.mkApp head (args'.filterMap (·.syntax?))

  -- Normal application
  return Syntax.mkApp fnStx (args.filterMap (·.syntax?))
where
  mkNamedArg (name : Name) : DelabM AppImplicitArg :=
    return .named <| ← `(Parser.Term.namedArgument| ($(mkIdent name) := $(← delab)))
  /--
  Delaborates the current argument.
  The argument `remainingArgs` is the number of arguments in the application after this one.
  -/
  mkArg (param : ParamKind) : DelabM AppImplicitArg := do
    let arg ← getExpr
    if ← getPPOption getPPAnalysisSkip then return .skip
    else if ← getPPOption getPPAnalysisHole then return .regular (← `(_))
    else if ← getPPOption getPPAnalysisNamedArg then
      mkNamedArg param.name
    else if param.defVal.isSome && param.defVal.get! == arg then
      -- Assumption: `useAppExplicit` has already detected whether it is ok to omit this argument, if it is the last one.
      -- We will later remove all optional arguments from the end.
      return .optional param.name (← delab)
    else if param.bInfo.isExplicit then
      return .regular (← delab)
    else if ← pure (param.name == `motive) <&&> shouldShowMotive arg (← getOptions) then
      mkNamedArg param.name
    else
      return .skip
  /--
  Runs the given unexpanders, returning the resulting syntax if any are applicable, and otherwise fails.
  -/
  tryUnexpand (fs : List Unexpander) (stx : Syntax) : DelabM Syntax := do
    fs.firstM fun f =>
      match f stx |>.run .missing |>.run () with
      | EStateM.Result.ok stx _ => return stx
      | _ => failure
  /--
  If the expression is a candidate for app unexpanders,
  try applying an app unexpander using some prefix of the arguments, longest prefix first.
  This function makes sure that the unexpanded syntax is annotated and given TermInfo so that it is hoverable in the InfoView.
  -/
  tryAppUnexpanders (fnStx : Term) (args : Array AppImplicitArg) : Delab := do
    let .const c _ := (← getExpr).getAppFn.consumeMData | unreachable!
    let fs := appUnexpanderAttribute.getValues (← getEnv) c
    if fs.isEmpty then failure
    let rec go (i : Nat) (implicitArgs : Nat) (argStxs : Array Syntax) : DelabM Term := do
      match i with
      | 0 =>
        let stx ← tryUnexpand fs fnStx
        return Syntax.mkApp (← annotateTermInfo stx) (args.filterMap (·.syntax?))
      | i' + 1 =>
        if args[i']!.syntax?.isSome then
          (do let stx ← tryUnexpand fs <| Syntax.mkApp fnStx argStxs
              let argStxs' := args.extract i args.size |>.filterMap (·.syntax?)
              return Syntax.mkApp (← annotateTermInfo stx) argStxs')
          <|> withBoundedAppFn (implicitArgs + 1) (go i' 0 argStxs.pop)
        else
          go i' (implicitArgs + 1) argStxs
    let maxUnexpand := args.findIdx? (!·.canUnexpand) |>.getD args.size
    withBoundedAppFn (args.size - maxUnexpand) <|
      go maxUnexpand 0 (args.extract 0 maxUnexpand |>.filterMap (·.syntax?))

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

  if h : numArgs < paramKinds.size then
    let nextParam := paramKinds[numArgs]

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

@[builtin_delab app]
def delabDelayedAssignedMVar : Delab := whenNotPPOption getPPMVarsDelayed do
  let .mvar mvarId := (← getExpr).getAppFn | failure
  let some decl ← getDelayedMVarAssignment? mvarId | failure
  withOverApp decl.fvars.size do
    let args := (← getExpr).getAppArgs
    -- Only delaborate using decl.mvarIdPending if the delayed mvar is applied to fvars
    guard <| args.all Expr.isFVar
    delabMVarAux decl.mvarIdPending

/-- State for `delabAppMatch` and helpers. -/
structure AppMatchState where
  info        : MatcherInfo
  /-- The `matcherTy` instantiated with universe levels and the matcher parameters, with a position at the type of
  this application prefix. -/
  matcherTy : SubExpr
  /-- The motive, with the pi type version delaborated and the original expression version.
  Once `AppMatchState` is complete, this is not `none`. -/
  motive      : Option (Term × Expr) := none
  /-- Whether `pp.analysis.namedArg` was set for the motive argument. -/
  motiveNamed : Bool := false
  /-- The delaborated discriminants, without `h :` annotations. -/
  discrs      : Array Term := #[]
  /-- The collection of names used for the `h :` discriminant annotations, in order.
  Uniquified names are constructed after the first phase. -/
  hNames?     : Array (Option Name) := #[]
  /-- Lambda subexpressions for each alternate. -/
  alts        : Array SubExpr := #[]
  /-- For each match alternative, the names to use for the pattern variables.
  Each ends with `hNames?.filterMap id` exactly. -/
  varNames    : Array (Array Name) := #[]
  /-- The delaborated right-hand sides for each match alternative. -/
  rhss        : Array Term := #[]

/--
Skips `numParams` binders, and execute `x varNames` where `varNames` contains the new binder names.
The `hNames` array is used for the last params.
Helper for `delabAppMatch`.
-/
private partial def skippingBinders {α} (numParams : Nat) (hNames : Array Name) (x : Array Name → DelabM α) : DelabM α := do
  loop 0 #[]
where
  loop (i : Nat) (varNames : Array Name) : DelabM α := do
    let rec visitLambda : DelabM α := do
      let varName := (← getExpr).bindingName!.eraseMacroScopes
      if numParams - hNames.size ≤ i then
        -- It is an "h annotation", so use the one we have already chosen.
        let varName := hNames[i + hNames.size - numParams]!
        withBindingBody varName do
          loop (i + 1) (varNames.push varName)
      else if varNames.contains varName then
        -- Pattern variables must not shadow each other, so ensure a unique name
        let varName := (← getLCtx).getUnusedName varName
        withBindingBody varName do
          loop (i + 1) (varNames.push varName)
      else
        withBindingBodyUnusedName fun id => do
          loop (i + 1) (varNames.push id.getId)
    if i < numParams then
      let e ← getExpr
      if e.isLambda then
        visitLambda
      else
        -- Eta expand `e`
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
    else x varNames

/--
Delaborates applications of "matchers" such as
```
List.map.match_1 : {α : Type _} →
  (motive : List α → Sort _) →
    (x : List α) → (Unit → motive List.nil) → ((a : α) → (as : List α) → motive (a :: as)) → motive x
```
-/
@[builtin_delab app]
partial def delabAppMatch : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| whenPPOption getPPMatch do
  -- Check that this is a matcher, and then set up overapplication.
  let Expr.const c us := (← getExpr).getAppFn | failure
  let some info ← getMatcherInfo? c | failure
  withOverApp info.arity do
    -- First pass visiting the match application. Incrementally fills `AppMatchState`,
    -- collecting information needed to delaborate the patterns and RHSs.
    -- No need to visit the parameters themselves.
    let st : AppMatchState ← withBoundedAppFnArgs (1 + info.numDiscrs + info.numAlts)
      (do
        let params := (← getExpr).getAppArgs
        let matcherTy : SubExpr :=
          { expr := ← instantiateForall (← instantiateTypeLevelParams (← getConstInfo c) us) params
            pos := (← getPos).pushType }
        guard <| ← isDefEq matcherTy.expr (← inferType (← getExpr))
        return { info, matcherTy })
      (fun st => do
        if st.motive.isNone then
          -- A motive for match notation is a type, so need to delaborate the lambda motive as a pi type.
          let lamMotive ← getExpr
          let piMotive ← lambdaTelescope lamMotive fun xs body => mkForallFVars xs body
          -- TODO: pp.analyze has not analyzed `piMotive`, only `lamMotive`
          -- Thus the binder types won't have any annotations.
          -- Though, by using the same position we can use the body annotations
          let piStx ← withTheReader SubExpr (fun cfg => { cfg with expr := piMotive }) delab
          let named ← getPPOption getPPAnalysisNamedArg
          return { st with motive := (piStx, lamMotive), motiveNamed := named }
        else if st.discrs.size < st.info.numDiscrs then
          return { st with discrs := st.discrs.push (← delab) }
        else if st.alts.size < st.info.numAlts then
          return { st with alts := st.alts.push (← readThe SubExpr) }
        else
          panic! "impossible, number of arguments does not match arity")

    -- Second pass, create names for the h parameters, come up with pattern variable names,
    -- and delaborate the RHSs.
    -- We need to create dummy variables for the `h :` annotation variables first because they
    -- come *last* in each alternative.
    let st ← withDummyBinders (st.info.discrInfos.map (·.hName?)) (← getExpr) fun hNames? => do
      let hNames := hNames?.filterMap id
      let mut st := {st with hNames? := hNames?}
      for i in [0:st.alts.size] do
        st ← withTheReader SubExpr (fun _ => st.alts[i]!) do
          -- We save the variables names here to be able to implement safe shadowing.
          -- The pattern delaboration must use the names saved here.
          skippingBinders st.info.altNumParams[i]! hNames fun varNames => do
            let rhs ← delab
            return { st with rhss := st.rhss.push rhs, varNames := st.varNames.push varNames }
      return st

    if st.rhss.isEmpty then
      `(nomatch $(st.discrs),*)
    else
      -- Third pass, delaborate patterns.
      -- Extracts arguments of motive applications from the matcher type.
      -- For the example in the docstring, yields `#[#[([])], #[(a::as)]]`.
      let pats ← withReader (fun ctx => { ctx with inPattern := true, subExpr := st.matcherTy }) do
        -- Need to reduce since there can be `let`s that are lifted into the matcher type
        forallTelescopeReducing (← getExpr) fun afterParams _ => do
          -- Skip motive and discriminators
          let alts := Array.ofSubarray afterParams[1 + st.discrs.size:]
          -- Visit minor premises
          alts.mapIdxM fun idx alt => do
            let altTy ← inferType alt
            withTheReader SubExpr (fun ctx =>
                { ctx with expr := altTy, pos := ctx.pos.pushNthBindingDomain (1 + st.discrs.size + idx) }) do
              usingNames st.varNames[idx]! <|
                withAppFnArgs (pure #[]) fun pats => return pats.push (← delab)
      -- Finally, assemble
      let discrs ← (st.hNames?.zip st.discrs).mapM fun (hName?, discr) =>
        match hName? with
        | none => `(matchDiscr| $discr:term)
        | some hName => `(matchDiscr| $(mkIdent hName) : $discr)
      let (piStx, lamMotive) := st.motive.get!
      let opts ← getOptions
      -- TODO: disable the match if other implicits are needed?
      if ← pure st.motiveNamed <||> shouldShowMotive lamMotive opts then
        `(match (motive := $piStx) $[$discrs:matchDiscr],* with $[| $pats,* => $st.rhss]*)
      else
        `(match $[$discrs:matchDiscr],* with $[| $pats,* => $st.rhss]*)
where
  /-- Adds hNames to the local context to reserve their names and runs `m` in that context. -/
  withDummyBinders {α : Type} (hNames? : Array (Option Name)) (body : Expr)
      (m : Array (Option Name) → DelabM α) (acc : Array (Option Name) := #[]) : DelabM α := do
    let i := acc.size
    if i < hNames?.size then
      if let some name := hNames?[i]! then
        let n' ← getUnusedName name body
        withLocalDecl n' .default (.sort levelZero) (kind := .implDetail) fun _ =>
          withDummyBinders hNames? body m (acc.push n')
      else
        withDummyBinders hNames? body m (acc.push none)
    else
      m acc

  usingNames {α} (varNames : Array Name) (x : DelabM α) (i : Nat := 0) : DelabM α :=
    if h : i < varNames.size then
      withBindingBody varNames[i] <| usingNames varNames x (i+1)
    else
      x

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
    let usedDownstream := curNames.any (fun n => stxBody.hasIdent n.getId)

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
          pure curNames.back!  -- here `curNames.size == 1`
      let group ← match e.binderInfo, ppTypes with
        | BinderInfo.default,        _      => defaultCase ()
        | BinderInfo.implicit,       true   => `(funBinder| {$curNames* : $stxT})
        | BinderInfo.implicit,       false  => `(funBinder| {$curNames*})
        | BinderInfo.strictImplicit, true   => `(funBinder| ⦃$curNames* : $stxT⦄)
        | BinderInfo.strictImplicit, false  => `(funBinder| ⦃$curNames*⦄)
        | BinderInfo.instImplicit,   _     =>
          if usedDownstream then `(funBinder| [$curNames.back! : $stxT])  -- here `curNames.size == 1`
          else  `(funBinder| [$stxT])
      let (binders, stxBody) :=
        match stxBody with
        | `(fun $binderGroups* => $stxBody) => (#[group] ++ binderGroups, stxBody)
        | _                                 => (#[group], stxBody)
      if ← getPPOption getPPUnicodeFun then
        `(fun $binders* ↦ $stxBody)
      else
        `(fun $binders* => $stxBody)

/-- Don't do any renaming for forall binders, but do add fresh macro scopes when there is shadowing. -/
private def ppPiPreserveNames := `pp.piPreserveNames
/-- Causes non-dependent foralls to print with binder names. -/
private def ppPiBinderNames := `pp.piBinderNames

/--
Similar to `delabBinders`, but tracking whether `forallE` is dependent or not.

See issue #1571
-/
private partial def delabForallBinders (delabGroup : Array Syntax → Bool → Syntax → Delab) (curNames : Array Syntax := #[]) (curDep := false) : Delab := do
  -- Logic note: wanting to print with binder names is equivalent to pretending the forall is dependent.
  let dep := !(← getExpr).isArrow || (← getOptionsAtCurrPos).get ppPiBinderNames false
  if !curNames.isEmpty && dep != curDep then
    -- don't group
    delabGroup curNames curDep (← delab)
  else
    let preserve := (← getOptionsAtCurrPos).get ppPiPreserveNames false
    let curDep := dep
    if ← shouldGroupWithNext then
      -- group with nested binder => recurse immediately
      withBindingBodyUnusedName (preserveName := preserve) fun stxN => delabForallBinders delabGroup (curNames.push stxN) curDep
    else
      -- don't group => delab body and prepend current binder group
      let (stx, stxN) ← withBindingBodyUnusedName (preserveName := preserve) fun stxN => return (← delab, stxN)
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
    | BinderInfo.instImplicit   => `(bracketedBinderF|[$curNames.back! : $stxT])
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
def delabOfNat : Delab := do
  let showType ← getPPOption getPPNumericTypes
  whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions <| withOverApp 3 do
    delabOfNatCore (showType := ← pure showType <||> getPPOption getPPNumericTypes)

/--
Delaborates the negative of an `OfNat.ofNat` literal.
`-@OfNat.ofNat _ n _` ~> `-n`
-/
@[builtin_delab app.Neg.neg]
def delabNeg : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions do
  delabNegIntCore (showType := (← getPPOption getPPNumericTypes))

/--
Delaborates a rational number literal.
`@OfNat.ofNat _ n _ / @OfNat.ofNat _ m` ~> `n / m`
and `-@OfNat.ofNat _ n _ / @OfNat.ofNat _ m` ~> `-n / m`
-/
@[builtin_delab app.HDiv.hDiv]
def delabHDiv : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions do
  delabDivRatCore (showType := (← getPPOption getPPNumericTypes))

-- `@OfDecimal.ofDecimal _ _ m s e` ~> `m*10^(sign * e)` where `sign == 1` if `s = false` and `sign = -1` if `s = true`
@[builtin_delab app.OfScientific.ofScientific]
def delabOfScientific : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPCoercions <| withOverApp 5 do
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
  if (← getPPOption getPPExplicit) && info.coercee != 0 then
    -- Approximation: the only implicit arguments come before the coercee
    failure
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
def delabDIte : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 5 do
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
def delabCond : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
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
def delabSigmaCore (sigma : Bool) : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
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

-- PProd and MProd value delaborator
-- (like pp_using_anonymous_constructor but flattening nested tuples)

def delabPProdMkCore (mkName : Name) : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).getAppNumArgs == 4
  let a ← withAppFn <| withAppArg delab
  let b ← withAppArg <| delab
  if (← getExpr).appArg!.isAppOfArity mkName 4 then
    if let `(⟨$xs,*⟩) := b then
      return ← `(⟨$a, $xs,*⟩)
  `(⟨$a, $b⟩)

@[builtin_delab app.PProd.mk]
def delabPProdMk : Delab := delabPProdMkCore ``PProd.mk

@[builtin_delab app.MProd.mk]
def delabMProdMk : Delab := delabPProdMkCore ``MProd.mk

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
def delabDo : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``Bind.bind 6
  let elems ← delabDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

/-- Delaborates a function application of the form `f ... x (fun _ : Unit => y)`. -/
def delabLazyBinop (arity : Nat) (k : Term → Term → DelabM Term) : DelabM Term :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp arity do
    let y ← withAppArg do
      let b := (← getExpr).beta #[mkConst ``Unit.unit]
      withTheReader SubExpr (fun s => {s with pos := s.pos.pushBindingBody, expr := b}) delab
    let x ← withAppFn <| withAppArg delab
    k x y

@[builtin_delab app.HOrElse.hOrElse]
def delabHOrElse : Delab := delabLazyBinop 6 (fun x y => `($x <|> $y))

@[builtin_delab app.HAndThen.hAndThen]
def delabHAndThen : Delab := delabLazyBinop 6 (fun x y => `($x >> $y))

@[builtin_delab app.Seq.seq]
def delabSeq : Delab := delabLazyBinop 6 (fun x y => `($x <*> $y))

@[builtin_delab app.SeqLeft.seqLeft]
def delabSeqLeft : Delab := delabLazyBinop 6 (fun x y => `($x <* $y))

@[builtin_delab app.SeqRight.seqRight]
def delabSeqRight : Delab := delabLazyBinop 6 (fun x y => `($x *> $y))

@[builtin_delab app.Lean.Name.str,
  builtin_delab app.Lean.Name.mkStr1, builtin_delab app.Lean.Name.mkStr2, builtin_delab app.Lean.Name.mkStr3, builtin_delab app.Lean.Name.mkStr4,
  builtin_delab app.Lean.Name.mkStr5, builtin_delab app.Lean.Name.mkStr6, builtin_delab app.Lean.Name.mkStr7, builtin_delab app.Lean.Name.mkStr8]
def delabNameMkStr : Delab := whenPPOption getPPNotation do
  let some n := (← getExpr).name? | failure
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
    else if e.isForall && (!e.isArrow || !(e.bindingName!.hasMacroScopes || bindingNames.contains e.bindingName!)) then
      delabParamsAux bindingNames idStx groups #[]
    else
      let (opts', e') ← processSpine {} (← readThe SubExpr)
      withReader (fun ctx => {ctx with optionsPerPos := opts', subExpr := { ctx.subExpr with expr := e' }}) do
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
    let n ← if bindingNames.contains n then withFreshMacroScope <| MonadQuotation.addMacroScope n else pure n
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
    (!e'.isArrow ||
      -- At the first sign of an inaccessible name, stop merging binders:
    !(e'.bindingName!.hasMacroScopes ||
      -- If it's a name that has already been used, stop merging binders:
      bindingNames.contains e'.bindingName!)) &&
    e.binderInfo == e'.binderInfo &&
    e.bindingDomain! == e'.bindingDomain! &&
    -- Inst implicits can't be grouped:
    e'.binderInfo != BinderInfo.instImplicit
  /--
  Go through rest of type, alpha renaming and setting options along the spine.
  -/
  processSpine (opts : OptionsPerPos) (subExpr : SubExpr) : MetaM (OptionsPerPos × Expr) := do
    if let .forallE n t b bi := subExpr.expr then
      let used := (← getLCtx).usesUserName n
      withLocalDecl n bi t fun fvar => do
        let (opts, b') ← processSpine opts { expr := b.instantiate1 fvar, pos := subExpr.pos.pushBindingBody }
        let b' := b'.abstract #[fvar]
        let opts := opts.insertAt subExpr.pos ppPiPreserveNames true
        if n.hasMacroScopes then
          return (opts, .forallE n t b' bi)
        else if !used then
          let opts := opts.insertAt subExpr.pos ppPiBinderNames true
          return (opts, .forallE n t b' bi)
        else
          let n' ← withFreshMacroScope <| MonadQuotation.addMacroScope n
          return (opts, .forallE n' t b' bi)
    else
      return (opts, subExpr.expr)

end Lean.PrettyPrinter.Delaborator
