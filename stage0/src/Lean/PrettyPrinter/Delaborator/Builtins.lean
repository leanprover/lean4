/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

import Lean.PrettyPrinter.Delaborator.Basic
import Lean.Parser

namespace Lean.PrettyPrinter.Delaborator
open Lean.Meta
open Lean.Parser.Term

@[builtinDelab fvar]
def delabFVar : Delab := do
let Expr.fvar id _ ← getExpr | unreachable!
try
  let l ← getLocalDecl id
  pure $ mkIdent l.userName
catch _ =>
  -- loose free variable, use internal name
  pure $ mkIdent id

-- loose bound variable, use pseudo syntax
@[builtinDelab bvar]
def delabBVar : Delab := do
  let Expr.bvar idx _ ← getExpr | unreachable!
  pure $ mkIdent $ Name.mkSimple $ "#" ++ toString idx

@[builtinDelab mvar]
def delabMVar : Delab := do
  let Expr.mvar n _ ← getExpr | unreachable!
  let n := n.replacePrefix `_uniq `m
  `(?$(mkIdent n))

@[builtinDelab sort]
def delabSort : Delab := do
  let Expr.sort l _ ← getExpr | unreachable!
  match l with
  | Level.zero _ => `(Prop)
  | Level.succ (Level.zero _) _ => `(Type)
  | _ => match l.dec with
    | some l' => `(Type $(Level.quote l' maxPrec!))
    | none    => `(Sort $(Level.quote l maxPrec!))

-- find shorter names for constants, in reverse to Lean.Elab.ResolveName

private def unresolveQualifiedName (ns : Name) (c : Name) : DelabM Name := do
  let c' := c.replacePrefix ns Name.anonymous;
  let env ← getEnv
  guard $ c' != c && !c'.isAnonymous && (!c'.isAtomic || !isProtected env c)
  pure c'

private def unresolveUsingNamespace (c : Name) : Name → DelabM Name
  | ns@(Name.str p _ _) => unresolveQualifiedName ns c <|> unresolveUsingNamespace c p
  | _ => failure

private def unresolveOpenDecls (c : Name) : List OpenDecl → DelabM Name
  | [] => failure
  | OpenDecl.simple ns exs :: openDecls =>
    let c' := c.replacePrefix ns Name.anonymous
    if c' != c && exs.elem c' then unresolveOpenDecls c openDecls
    else
      unresolveQualifiedName ns c <|> unresolveOpenDecls c openDecls
  | OpenDecl.explicit openedId resolvedId :: openDecls =>
    guard (c == resolvedId) *> pure openedId <|> unresolveOpenDecls c openDecls

-- NOTE: not a registered delaborator, as `const` is never called (see [delab] description)
def delabConst : Delab := do
  let Expr.const c ls _ ← getExpr | unreachable!
  let c ← if (← getPPOption getPPFullNames) then pure c else
    let ctx ← read
    let env ← getEnv
    let as := getRevAliases env c
    -- might want to use a more clever heuristic such as selecting the shortest alias...
    let c := as.headD c
    unresolveUsingNamespace c ctx.currNamespace <|> unresolveOpenDecls c ctx.openDecls <|> pure c
  let c ← if (← getPPOption getPPPrivateNames) then pure c else pure $ (privateToUserName? c).getD c
  let ppUnivs ← getPPOption getPPUniverses
  if ls.isEmpty || !ppUnivs then
    pure $ mkIdent c
  else
    `($(mkIdent c).{$[$(ls.toArray.map quote)],*})

inductive ParamKind where
  | explicit
  -- combines implicit params, optParams, and autoParams
  | implicit (defVal : Option Expr)

/-- Return array with n-th element set to kind of n-th parameter of `e`. -/
def getParamKinds (e : Expr) : MetaM (Array ParamKind) := do
  let t ← inferType e
  forallTelescopeReducing t fun params _ =>
    params.mapM fun param => do
      let l ← getLocalDecl param.fvarId!
      match l.type.getOptParamDefault? with
      | some val => pure $ ParamKind.implicit val
      | _ =>
        if l.type.isAutoParam || !l.binderInfo.isExplicit then
          pure $ ParamKind.implicit none
        else
          pure ParamKind.explicit

@[builtinDelab app]
def delabAppExplicit : Delab := do
  let (fnStx, argStxs) ← withAppFnArgs
    (do
      let fn ← getExpr
      let stx ← if fn.isConst then delabConst else delab
      let paramKinds ← liftM <| getParamKinds fn <|> pure #[]
      let stx ← if paramKinds.any (fun | ParamKind.explicit => false | _ => true) = true then `(@$stx) else pure stx
      pure (stx, #[]))
    (fun ⟨fnStx, argStxs⟩ => do
      let argStx ← delab
      pure (fnStx, argStxs.push argStx))
  Syntax.mkApp fnStx argStxs

@[builtinDelab app]
def delabAppImplicit : Delab := whenNotPPOption getPPExplicit do
  let (fnStx, _, argStxs) ← withAppFnArgs
    (do
      let fn ← getExpr
      let stx ← if fn.isConst then delabConst else delab
      let paramKinds ← liftM (getParamKinds fn <|> pure #[])
      pure (stx, paramKinds.toList, #[]))
    (fun (fnStx, paramKinds, argStxs) => do
      let arg ← getExpr;
      let implicit : Bool := match paramKinds with -- TODO: check why we need `: Bool` here
        | [ParamKind.implicit (some v)] => !v.hasLooseBVars && v == arg
        | ParamKind.implicit none :: _  => true
        | _                             => false
      if implicit then
        pure (fnStx, paramKinds.tailD [], argStxs)
      else do
        let argStx ← delab
        pure (fnStx, paramKinds.tailD [], argStxs.push argStx))
  Syntax.mkApp fnStx argStxs

@[builtinDelab app]
def delabAppWithUnexpander : Delab := whenPPOption getPPNotation do
  let Expr.const c _ _ ← pure (← getExpr).getAppFn | failure
  let stx ← delabAppImplicit
  match stx with
  | `($cPP:ident $args*) => do
    let some (f::_) ← pure <| (appUnexpanderAttribute.ext.getState (← getEnv)).table.find? c
      | pure stx
    let EStateM.Result.ok stx _ ← f stx |>.run ()
      | pure stx
    pure stx
  | _ => pure stx

/-- State for `delabAppMatch` and helpers. -/
structure AppMatchState where
  info      : MatcherInfo
  matcherTy : Expr
  params    : Array Expr := #[]
  hasMotive : Bool := false
  discrs    : Array Syntax := #[]
  varNames  : Array (Array Name) := #[]
  rhss      : Array Syntax := #[]
  -- additional arguments applied to the result of the `match` expression
  moreArgs  : Array Syntax := #[]
/--
  Extract arguments of motive applications from the matcher type.
  For the example below: `#[#[`([])], #[`(a::as)]]` -/
private partial def delabPatterns (st : AppMatchState) : DelabM (Array (Array Syntax)) := do
  let ty ← instantiateForall st.matcherTy st.params
  forallTelescope ty fun params _ => do
    -- skip motive and discriminators
    let alts := Array.ofSubarray $ params[1 + st.discrs.size:]
    alts.mapIdxM fun idx alt => do
      let ty ← inferType alt
      withReader ({ · with expr := ty }) $
        usingNames st.varNames[idx] do
          withAppFnArgs (pure #[]) (fun pats => do pure $ pats.push (← delab))
where
  usingNames {α} (varNames : Array Name) (x : DelabM α) : DelabM α :=
    usingNamesAux 0 varNames x
  usingNamesAux {α} (i : Nat) (varNames : Array Name) (x : DelabM α) : DelabM α :=
    if i < varNames.size then
      withBindingBody varNames[i] <| usingNamesAux (i+1) varNames x
    else
      x

/-- Skip `numParams` binders, and execute `x varNames` where `varNames` contains the new binder names. -/
private def skippingBinders {α} (numParams : Nat) (x : Array Name → DelabM α) : DelabM α :=
  loop numParams #[]
where
  loop : Nat → Array Name → DelabM α
    | 0,   varNames => x varNames
    | n+1, varNames => do
      let varName ← (← getExpr).bindingName!.eraseMacroScopes
      -- Pattern variables cannot shadow each other
      if varNames.contains varName then
        let varName := (← getLCtx).getUnusedName varName
        loop n (varNames.push varName)
      else
        withBindingBodyUnusedName fun id => do
          loop n (varNames.push id.getId)

/--
  Delaborate applications of "matchers" such as
  ```
  List.map.match_1 : {α : Type _} →
    (motive : List α → Sort _) →
      (x : List α) → (Unit → motive List.nil) → ((a : α) → (as : List α) → motive (a :: as)) → motive x
  ```
-/
@[builtinDelab app]
def delabAppMatch : Delab := whenPPOption getPPNotation do
  -- incrementally fill `AppMatchState` from arguments
  let st ← withAppFnArgs
    (do
      let (Expr.const c us _) ← getExpr | failure
      let (some info) ← getMatcherInfo? c | failure
      { matcherTy := (← getConstInfo c).instantiateTypeLevelParams us, info := info : AppMatchState })
    (fun st => do
      if st.params.size < st.info.numParams then
        pure { st with params := st.params.push (← getExpr) }
      else if !st.hasMotive then
        -- discard motive argument
        pure { st with hasMotive := true }
      else if st.discrs.size < st.info.numDiscrs then
        pure { st with discrs := st.discrs.push (← delab) }
      else if st.rhss.size < st.info.altNumParams.size then
        /- We save the variables names here to be able to implemente safe_shadowing.
           The pattern delaboration must use the names saved here. -/
        let (varNames, rhs) ← skippingBinders st.info.altNumParams[st.rhss.size] fun varNames => do
          let rhs ← delab
          return (varNames, rhs)
        pure { st with rhss := st.rhss.push rhs, varNames := st.varNames.push varNames }
      else
        pure { st with moreArgs := st.moreArgs.push (← delab) })

  if st.discrs.size < st.info.numDiscrs || st.rhss.size < st.info.altNumParams.size then
    -- underapplied
    failure

  match st.discrs, st.rhss with
  | #[discr], #[] =>
    let stx ← `(nomatch $discr)
    Syntax.mkApp stx st.moreArgs
  | _,        #[] => failure
  | _,        _   =>
    let pats ← delabPatterns st
    let stx ← `(match $[$st.discrs:term],* with $[| $pats,* => $st.rhss]*)
    Syntax.mkApp stx st.moreArgs

@[builtinDelab mdata]
def delabMData : Delab := do
  -- only interpret `pp.` values by default
  let Expr.mdata m _ _ ← getExpr | unreachable!
  let mut posOpts := (← read).optionsPerPos
  let mut inaccessible := false
  let pos := (← read).pos
  for (k, v) in m do
    if (`pp).isPrefixOf k then
      let opts := posOpts.find? pos |>.getD {}
      posOpts := posOpts.insert pos (opts.insert k v)
    if k == `inaccessible then
      inaccessible := true
  withReader ({ · with optionsPerPos := posOpts }) do
    let s ← withMDataExpr delab
    if inaccessible then
      `(.($s))
    else
      pure s

/--
Check for a `Syntax.ident` of the given name anywhere in the tree.
This is usually a bad idea since it does not check for shadowing bindings,
but in the delaborator we assume that bindings are never shadowed.
-/
partial def hasIdent (id : Name) : Syntax → Bool
  | Syntax.ident _ _ id' _ => id == id'
  | Syntax.node _ args     => args.any (hasIdent id)
  | _                      => false

/--
Return `true` iff current binder should be merged with the nested
binder, if any, into a single binder group:
* both binders must have same binder info and domain
* they cannot be inst-implicit (`[a b : A]` is not valid syntax)
* `pp.binder_types` must be the same value for both terms
* prefer `fun a b` over `fun (a b)`
-/
private def shouldGroupWithNext : DelabM Bool := do
  let e ← getExpr
  let ppEType ← getPPOption getPPBinderTypes;
  let go (e' : Expr) := do
    let ppE'Type ← withBindingBody `_ $ getPPOption getPPBinderTypes
    pure $ e.binderInfo == e'.binderInfo &&
      e.bindingDomain! == e'.bindingDomain! &&
      e'.binderInfo != BinderInfo.instImplicit &&
      ppEType == ppE'Type &&
      (e'.binderInfo != BinderInfo.default || ppE'Type)
  match e with
  | Expr.lam _ _     e'@(Expr.lam _ _ _ _) _     => go e'
  | Expr.forallE _ _ e'@(Expr.forallE _ _ _ _) _ => go e'
  | _ => pure false

private partial def delabBinders (delabGroup : Array Syntax → Syntax → Delab) : optParam (Array Syntax) #[] → Delab
  -- Accumulate names (`Syntax.ident`s with position information) of the current, unfinished
  -- binder group `(d e ...)` as determined by `shouldGroupWithNext`. We cannot do grouping
  -- inside-out, on the Syntax level, because it depends on comparing the Expr binder types.
  | curNames => do
    if (← shouldGroupWithNext) then
      -- group with nested binder => recurse immediately
      withBindingBodyUnusedName fun stxN => delabBinders delabGroup (curNames.push stxN)
    else
      -- don't group => delab body and prepend current binder group
      let (stx, stxN) ← withBindingBodyUnusedName fun stxN => do (← delab, stxN)
      delabGroup (curNames.push stxN) stx

@[builtinDelab lam]
def delabLam : Delab :=
  delabBinders fun curNames stxBody => do
    let e ← getExpr
    let stxT ← withBindingDomain delab
    let ppTypes ← getPPOption getPPBinderTypes
    let expl ← getPPOption getPPExplicit
    -- leave lambda implicit if possible
    let blockImplicitLambda := expl ||
      e.binderInfo == BinderInfo.default ||
      Elab.Term.blockImplicitLambda stxBody ||
      curNames.any (fun n => hasIdent n.getId stxBody);
    if !blockImplicitLambda then
      pure stxBody
    else
      let group ← match e.binderInfo, ppTypes with
        | BinderInfo.default,     true   =>
          -- "default" binder group is the only one that expects binder names
          -- as a term, i.e. a single `Syntax.ident` or an application thereof
          let stxCurNames ←
            if curNames.size > 1 then
              `($(curNames.get! 0) $(curNames.eraseIdx 0)*)
            else
              pure $ curNames.get! 0;
          `(funBinder| ($stxCurNames : $stxT))
        | BinderInfo.default,     false  => pure curNames.back  -- here `curNames.size == 1`
        | BinderInfo.implicit,    true   => `(funBinder| {$curNames* : $stxT})
        | BinderInfo.implicit,    false  => `(funBinder| {$curNames*})
        | BinderInfo.instImplicit, _     => `(funBinder| [$curNames.back : $stxT])  -- here `curNames.size == 1`
        | _                      , _     => unreachable!;
      match stxBody with
      | `(fun $binderGroups* => $stxBody) => `(fun $group $binderGroups* => $stxBody)
      | _                                 => `(fun $group => $stxBody)

@[builtinDelab forallE]
def delabForall : Delab :=
  delabBinders fun curNames stxBody => do
    let e ← getExpr
    let prop ← try isProp e catch _ => false
    let stxT ← withBindingDomain delab
    let group ← match e.binderInfo with
    | BinderInfo.default      =>
      -- heuristic: use non-dependent arrows only if possible for whole group to avoid
      -- noisy mix like `(α : Type) → Type → (γ : Type) → ...`.
      let dependent := curNames.any $ fun n => hasIdent n.getId stxBody
      -- NOTE: non-dependent arrows are available only for the default binder info
      if dependent then
        if prop && !(← getPPOption getPPBinderTypes) then
          return ← `(∀ $curNames:ident*, $stxBody)
        else
          `(bracketedBinderF|($curNames* : $stxT))
      else
        return ← curNames.foldrM (fun _ stxBody => `($stxT → $stxBody)) stxBody
    | BinderInfo.implicit     => `(bracketedBinderF|{$curNames* : $stxT})
    -- here `curNames.size == 1`
    | BinderInfo.instImplicit => `(bracketedBinderF|[$curNames.back : $stxT])
    | _                       => unreachable!
    if prop then
      match stxBody with
      | `(∀ $groups*, $stxBody) => `(∀ $group $groups*, $stxBody)
      | _                       => `(∀ $group, $stxBody)
    else
      `($group:bracketedBinder → $stxBody)

@[builtinDelab letE]
def delabLetE : Delab := do
  let Expr.letE n t v b _ ← getExpr | unreachable!
  let n ← getUnusedName n b
  let stxT ← descend t 0 delab
  let stxV ← descend v 1 delab
  let stxB ← withLetDecl n t v fun fvar =>
    let b := b.instantiate1 fvar
    descend b 2 delab
  `(let $(mkIdent n) : $stxT := $stxV; $stxB)

@[builtinDelab lit]
def delabLit : Delab := do
  let Expr.lit l _ ← getExpr | unreachable!
  match l with
  | Literal.natVal n => pure $ quote n
  | Literal.strVal s => pure $ quote s

-- `@OfNat.ofNat _ n _` ~> `n`
@[builtinDelab app.OfNat.ofNat]
def delabOfNat : Delab := whenPPOption getPPCoercions do
  let (Expr.app (Expr.app _ (Expr.lit (Literal.natVal n) _) _) _ _) ← getExpr | failure
  return quote n

-- `@OfDecimal.ofDecimal _ _ m s e` ~> `m*10^(sign * e)` where `sign == 1` if `s = false` and `sign = -1` if `s = true`
@[builtinDelab app.OfScientific.ofScientific]
def delabOfScientific : Delab := whenPPOption getPPCoercions do
  let expr ← getExpr
  guard <| expr.getAppNumArgs == 5
  let Expr.lit (Literal.natVal m) _ ← pure (expr.getArg! 2) | failure
  let Expr.lit (Literal.natVal e) _ ← pure (expr.getArg! 4) | failure
  let s ← match expr.getArg! 3 with
    | Expr.const `Bool.true _ _  => pure true
    | Expr.const `Bool.false _ _ => pure false
    | _ => failure
  let str  := toString m
  if s && e == str.length then
    return Syntax.mkScientificLit ("0." ++ str)
  else if s && e < str.length then
    let mStr := str.extract 0 (str.length - e)
    let eStr := str.extract (str.length - e) str.length
    return Syntax.mkScientificLit (mStr ++ "." ++ eStr)
  else
    return Syntax.mkScientificLit (str ++ "e" ++ (if s then "-" else "") ++ toString e)

/--
Delaborate a projection primitive. These do not usually occur in
user code, but are pretty-printed when e.g. `#print`ing a projection
function.
-/
@[builtinDelab proj]
def delabProj : Delab := do
  let Expr.proj _ idx _ _ ← getExpr | unreachable!
  let e ← withProj delab
  -- not perfectly authentic: elaborates to the `idx`-th named projection
  -- function (e.g. `e.1` is `Prod.fst e`), which unfolds to the actual
  -- `proj`.
  let idx := Syntax.mkLit fieldIdxKind (toString (idx + 1));
  `($(e).$idx:fieldIdx)

/-- Delaborate a call to a projection function such as `Prod.fst`. -/
@[builtinDelab app]
def delabProjectionApp : Delab := whenPPOption getPPStructureProjections $ do
  let e@(Expr.app fn _ _) ← getExpr | failure
  let Expr.const c@(Name.str _ f _) _ _ ← pure fn.getAppFn | failure
  let env ← getEnv
  let some info ← pure $ env.getProjectionFnInfo? c | failure
  -- can't use with classes since the instance parameter is implicit
  guard $ !info.fromClass
  -- projection function should be fully applied (#struct params + 1 instance parameter)
  -- TODO: support over-application
  guard $ e.getAppNumArgs == info.nparams + 1
  -- If pp.explicit is true, and the structure has parameters, we should not
  -- use field notation because we will not be able to see the parameters.
  let expl ← getPPOption getPPExplicit
  guard $ !expl || info.nparams == 0
  let appStx ← withAppArg delab
  `($(appStx).$(mkIdent f):ident)

@[builtinDelab app]
def delabStructureInstance : Delab := whenPPOption getPPStructureInstances do
  let env ← getEnv
  let e ← getExpr
  let some s ← pure $ e.isConstructorApp? env | failure
  guard $ isStructure env s.induct;
  /- If implicit arguments should be shown, and the structure has parameters, we should not
     pretty print using { ... }, because we will not be able to see the parameters. -/
  let explicit ← getPPOption getPPExplicit
  guard !(explicit && s.numParams > 0)
  let fieldNames := getStructureFields env s.induct
  let (_, fields) ← withAppFnArgs (pure (0, #[])) fun ⟨idx, fields⟩ => do
      if idx < s.numParams then
        pure (idx + 1, fields)
      else
        let val ← delab
        let field ← `(structInstField|$(mkIdent <| fieldNames.get! (idx - s.numParams)):ident := $val)
        pure (idx + 1, fields.push field)
  let lastField := fields[fields.size - 1]
  let fields := fields.pop
  let ty ←
    if (← getPPOption getPPStructureInstanceType) then
      let ty ← inferType e
      -- `ty` is not actually part of `e`, but since `e` must be an application or constant, we know that
      -- index 2 is unused.
      pure <| some (← descend ty 2 delab)
    else pure <| none
  `({ $[$fields, ]* $lastField $[: $ty]? })

@[builtinDelab app.Prod.mk]
def delabTuple : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard $ e.getAppNumArgs == 4
  let a ← withAppFn $ withAppArg delab
  let b ← withAppArg delab
  match b with
  | `(($b, $bs,*)) => `(($a, $b, $bs,*))
  | _              => `(($a, $b))

-- abbrev coe {α : Sort u} {β : Sort v} (a : α) [CoeT α a β] : β
@[builtinDelab app.coe]
def delabCoe : Delab := whenPPOption getPPCoercions do
  let e ← getExpr
  guard $ e.getAppNumArgs >= 4
  -- delab as application, then discard function
  let stx ← delabAppImplicit
  match stx with
  | `($fn $arg)   => arg
  | `($fn $args*) => `($(args.get! 0) $(args.eraseIdx 0)*)
  | _             => failure

-- abbrev coeFun {α : Sort u} {γ : α → Sort v} (a : α) [CoeFun α γ] : γ a
@[builtinDelab app.coeFun]
def delabCoeFun : Delab := delabCoe

@[builtinDelab app.List.nil]
def delabNil : Delab := whenPPOption getPPNotation do
  guard $ (← getExpr).getAppNumArgs == 1
  `([])

@[builtinDelab app.List.cons]
def delabConsList : Delab := whenPPOption getPPNotation do
  guard $ (← getExpr).getAppNumArgs == 3
  let x ← withAppFn (withAppArg delab)
  match (← withAppArg delab) with
  | `([])      => `([$x])
  | `([$xs,*]) => `([$x, $xs,*])
  | _          => failure

@[builtinDelab app.List.toArray]
def delabListToArray : Delab := whenPPOption getPPNotation do
  guard $ (← getExpr).getAppNumArgs == 2
  match (← withAppArg delab) with
  | `([$xs,*]) => `(#[$xs,*])
  | _         => failure

@[builtinDelab app.ite]
def delabIte : Delab := whenPPOption getPPNotation do
  guard $ (← getExpr).getAppNumArgs == 5
  let c ← withAppFn $ withAppFn $ withAppFn $ withAppArg delab
  let t ← withAppFn $ withAppArg delab
  let e ← withAppArg delab
  `(if $c then $t else $e)

@[builtinDelab app.dite]
def delabDIte : Delab := whenPPOption getPPNotation do
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

@[builtinDelab app.namedPattern]
def delabNamedPattern : Delab := do
  guard $ (← getExpr).getAppNumArgs == 3
  let x ← withAppFn $ withAppArg delab
  let p ← withAppArg delab
  guard x.isIdent
  `($x:ident@$p:term)

partial def delabDoElems : DelabM (List Syntax) := do
  let e ← getExpr
  if e.isAppOfArity `Bind.bind 6 then
    -- Bind.bind.{u, v} : {m : Type u → Type v} → [self : Bind m] → {α β : Type u} → m α → (α → m β) → m β
    let ma ← withAppFn $ withAppArg delab
    withAppArg do
      match (← getExpr) with
      | Expr.lam _ _ body _ =>
        withBindingBodyUnusedName fun n => do
          if body.hasLooseBVars then
            prependAndRec `(doElem|let $n:term ← $ma)
          else
            prependAndRec `(doElem|$ma:term)
      | _ => delabAndRet
  else if e.isLet then
    let Expr.letE n t v b _ ← getExpr | unreachable!
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delab
    withLetDecl n t v fun fvar =>
      let b := b.instantiate1 fvar
      descend b 2 $
        prependAndRec `(doElem|let $(mkIdent n) : $stxT := $stxV)
  else
    delabAndRet
  where
    prependAndRec x : DelabM _ := List.cons <$> x <*> delabDoElems
    delabAndRet : DelabM _ := do let stx ← delab; [←`(doElem|$stx:term)]

@[builtinDelab app.Bind.bind]
def delabDo : Delab := whenPPOption getPPNotation do
  unless (← getExpr).isAppOfArity `Bind.bind 6 do
    failure
  let elems ← delabDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(do $items:doSeqItem*)

@[builtinDelab app.sorryAx]
def delabSorryAx : Delab := whenPPOption getPPNotation do
  unless (← getExpr).isAppOfArity ``sorryAx 2 do
    failure
  `(sorry)

end Lean.PrettyPrinter.Delaborator
