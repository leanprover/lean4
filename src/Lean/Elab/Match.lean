/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExprWhere
import Lean.Meta.Match.Match
import Lean.Meta.GeneralizeVars
import Lean.Meta.ForEachExpr
import Lean.Elab.BindersUtil
import Lean.Elab.PatternVar
import Lean.Elab.Quotation.Precheck
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Term
open Meta
open Lean.Parser.Term

private def expandSimpleMatch (stx : Syntax) (discr : Term) (lhsVar : Ident) (rhs : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let newStx ← `(let $lhsVar := $discr; $rhs)
  withMacroExpansion stx newStx <| elabTerm newStx expectedType?

private def mkUserNameFor (e : Expr) : TermElabM Name := do
  match e with
  /- Remark: we use `mkFreshUserName` to make sure we don't add a variable to the local context that can be resolved to `e`. -/
  | .fvar fvarId => mkFreshUserName (← fvarId.getUserName)
  | _            => mkFreshBinderName


/--
   Remark: if the discriminat is `Systax.missing`, we abort the elaboration of the `match`-expression.
   This can happen due to error recovery. Example
   ```
   example : (p ∨ p) → p := fun h => match
   ```
   If we don't abort, the elaborator loops because we will keep trying to expand
   ```
   match
   ```
   into
   ```
   let d := <Syntax.missing>; match
   ```
   Recall that `Syntax.setArg stx i arg` is a no-op when `i` is out-of-bounds. -/
def isAtomicDiscr (discr : Syntax) : TermElabM Bool := do
  match discr with
  | `($_:ident)  => pure true
  | `(@$_:ident) => pure true
  | `(?$_:ident) => pure true
  | _ => if discr.isMissing then throwAbortTerm else pure false

-- See expandNonAtomicDiscrs?
private def elabAtomicDiscr (discr : Syntax) : TermElabM Expr := do
  let term := discr[1]
  elabTerm term none

structure Discr where
  expr : Expr
  /-- `some h` if discriminant is annotated with the `h : ` notation. -/
  h?  : Option Syntax := none
  deriving Inhabited

structure ElabMatchTypeAndDiscrsResult where
  discrs    : Array Discr
  matchType : Expr
  /-- `true` when performing dependent elimination. We use this to decide whether we optimize the "match unit" case.
     See `isMatchUnit?`. -/
  isDep     : Bool
  alts      : Array MatchAltView

private partial def elabMatchTypeAndDiscrs (discrStxs : Array Syntax) (matchOptMotive : Syntax) (matchAltViews : Array MatchAltView) (expectedType : Expr)
      : TermElabM ElabMatchTypeAndDiscrsResult := do
  if matchOptMotive.isNone then
    elabDiscrs 0 #[]
  else
    -- motive := leading_parser atomic ("(" >> nonReservedSymbol "motive" >> " := ") >> termParser >> ")"
    let matchTypeStx := matchOptMotive[0][3]
    let matchType ← elabType matchTypeStx
    let (discrs, isDep) ← elabDiscrsWitMatchType matchType
    return { discrs := discrs, matchType := matchType, isDep := isDep, alts := matchAltViews }
where
  /-- Easy case: elaborate discriminant when the match-type has been explicitly provided by the user.  -/
  elabDiscrsWitMatchType (matchType : Expr) : TermElabM (Array Discr × Bool) := do
    let mut discrs := #[]
    let mut i := 0
    let mut matchType := matchType
    let mut isDep := false
    for discrStx in discrStxs do
      i := i + 1
      matchType ← whnf matchType
      match matchType with
      | Expr.forallE _ d b _ =>
        let discr ← fullApproxDefEq <| elabTermEnsuringType discrStx[1] d
        trace[Elab.match] "discr #{i} {discr} : {d}"
        if b.hasLooseBVars then
          isDep := true
        matchType := b.instantiate1 discr
        discrs := discrs.push { expr := discr }
      | _ =>
        throwError "invalid motive provided to match-expression, function type with arity #{discrStxs.size} expected"
    return (discrs, isDep)

  markIsDep (r : ElabMatchTypeAndDiscrsResult) :=
    { r with isDep := true }

  /-- Elaborate discriminants inferring the match-type -/
  elabDiscrs (i : Nat) (discrs : Array Discr) : TermElabM ElabMatchTypeAndDiscrsResult := do
    if h : i < discrStxs.size then
      let discrStx := discrStxs.get ⟨i, h⟩
      let discr     ← elabAtomicDiscr discrStx
      let discr     ← instantiateMVars discr
      let userName ← mkUserNameFor discr
      let h? := if discrStx[0].isNone then none else some discrStx[0][0]
      let discrs := discrs.push { expr := discr, h? }
      let mut result ← elabDiscrs (i + 1) discrs
      let matchTypeBody ← kabstract result.matchType discr
      if matchTypeBody.hasLooseBVars then
        result := markIsDep result
      /-
        We use `transform (usedLetOnly := true)` to eliminate unnecessary let-expressions.
        This transformation was added to address issue #1155, and avoid an unnecessary dependency.
        In issue #1155, `discrType` was of the form `let _discr := OfNat.ofNat ... 0 ?m; ...`, and not removing
        the unnecessary `let-expr` was introducing an artificial dependency to `?m`.
        TODO: make sure that even when this kind of artificial dependency occurs we catch it before sending
        the term to the kernel.
      -/
      let discrType ← transform (usedLetOnly := true) (← instantiateMVars (← inferType discr))
      let matchType := Lean.mkForall userName BinderInfo.default discrType matchTypeBody
      return { result with matchType }
    else
      return { discrs, alts := matchAltViews, isDep := false, matchType := expectedType }

def expandMacrosInPatterns (matchAlts : Array MatchAltView) : MacroM (Array MatchAltView) := do
  matchAlts.mapM fun matchAlt => do
    let patterns ← matchAlt.patterns.mapM expandMacros
    pure { matchAlt with patterns := patterns }

private def getMatchGeneralizing? : Syntax → Option Bool
  | `(match (generalizing := true)  $[$motive]? $_discrs,* with $_alts:matchAlt*) => some true
  | `(match (generalizing := false) $[$motive]? $_discrs,* with $_alts:matchAlt*) => some false
  | _ => none

/-- Given `stx` a match-expression, return its alternatives. -/
private def getMatchAlts : Syntax → Array MatchAltView
  | `(match $[$gen]? $[$motive]? $_discrs,* with $alts:matchAlt*) =>
    alts.filterMap fun alt => match alt with
      | `(matchAltExpr| | $patterns,* => $rhs) => some {
          ref      := alt,
          patterns := patterns,
          rhs      := rhs
        }
      | _ => none
  | _ => #[]

@[builtin_term_elab inaccessible] def elabInaccessible : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[1] expectedType?
  return mkInaccessible e

open Lean.Elab.Term.Quotation in
@[builtin_quot_precheck Lean.Parser.Term.match] def precheckMatch : Precheck
  | `(match $[$discrs:term],* with $[| $[$patss],* => $rhss]*) => do
    discrs.forM precheck
    for (pats, rhs) in patss.zip rhss do
      let vars ← try
        getPatternsVars pats
      catch | _ => return  -- can happen in case of pattern antiquotations
      Quotation.withNewLocals (getPatternVarNames vars) <| precheck rhs
  | _ => throwUnsupportedSyntax

/-- We convert the collected `PatternVar`s intro `PatternVarDecl` -/
structure PatternVarDecl where
  fvarId : FVarId

private partial def withPatternVars {α} (pVars : Array PatternVar) (k : Array PatternVarDecl → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (decls : Array PatternVarDecl) (userNames : Array Name) := do
    if h : i < pVars.size then
      let var := pVars.get ⟨i, h⟩
      let type ← mkFreshTypeMVar
      withLocalDecl var.getId BinderInfo.default type fun x =>
        loop (i+1) (decls.push { fvarId := x.fvarId! }) (userNames.push Name.anonymous)
    else
      k decls
  loop 0 #[] #[]

/-!
Remark: when performing dependent pattern matching, we often had to write code such as

```lean
def Vec.map' (f : α → β) (xs : Vec α n) : Vec β n :=
  match n, xs with
  | _, nil       => nil
  | _, cons a as => cons (f a) (map' f as)
```
We had to include `n` and the `_`s because the type of `xs` depends on `n`.
Moreover, `nil` and `cons a as` have different types.
This was quite tedious. So, we have implemented an automatic "discriminant refinement procedure".
The procedure is based on the observation that we get a type error whenenver we forget to include `_`s
and the indices a discriminant depends on. So, we catch the exception, check whether the type of the discriminant
is an indexed family, and add their indices as new discriminants.

The current implementation, adds indices as they are found, and does not
try to "sort" the new discriminants.

If the refinement process fails, we report the original error message.
-/

/-- Auxiliary structure for storing an type mismatch exception when processing the
   pattern #`idx` of some alternative. -/
structure PatternElabException where
  ex          : Exception
  patternIdx  : Nat -- Discriminant that sh
  pathToIndex : List Nat -- Path to the problematic inductive type index that produced the type mismatch

/--
  This method is part of the "discriminant refinement" procedure. It in invoked when the
  type of the `pattern` does not match the expected type. The expected type is based on the
  motive computed using the `match` discriminants.
  It tries to compute a path to an index of the discriminant type.
  For example, suppose the user has written
  ```
  inductive Mem (a : α) : List α → Prop where
    | head {as} : Mem a (a::as)
    | tail {as} : Mem a as → Mem a (a'::as)

  infix:50 " ∈ " => Mem

  example (a b : Nat) (h : a ∈ [b]) : b = a :=
  match h with
  | Mem.head => rfl
  ```
  The motive for the match is `a ∈ [b] → b = a`, and get a type mismatch between the type
  of `Mem.head` and `a ∈ [b]`. This procedure return the path `[2, 1]` to the index `b`.
  We use it to produce the following refinement
  ```
  example (a b : Nat) (h : a ∈ [b]) : b = a :=
  match b, h with
  | _, Mem.head => rfl
  ```
  which produces the new motive `(x : Nat) →  a ∈ [x] → x = a`
  After this refinement step, the `match` is elaborated successfully.

  This method relies on the fact that the dependent pattern matcher compiler solves equations
  between indices of indexed inductive families.
  The following kinds of equations are supported by this compiler:
  - `x = t`
  - `t = x`
  - `ctor ... = ctor ...`

  where `x` is a free variable, `t` is an arbitrary term, and `ctor` is constructor.
  Our procedure ensures that "information" is not lost, and will *not* succeed in an
  example such as
  ```
  example (a b : Nat) (f : Nat → Nat) (h : f a ∈ [f b]) : f b = f a :=
    match h with
    | Mem.head => rfl
  ```
  and will not add `f b` as a new discriminant. We may add an option in the future to
  enable this more liberal form of refinement.
-/
private partial def findDiscrRefinementPath (pattern : Expr) (expected : Expr) : OptionT MetaM (List Nat) := do
  goType (← instantiateMVars (← inferType pattern)) expected
where
  checkCompatibleApps (t d : Expr) : OptionT MetaM Unit := do
    guard d.isApp
    guard <| t.getAppNumArgs == d.getAppNumArgs
    let tFn := t.getAppFn
    let dFn := d.getAppFn
    guard <| tFn.isConst && dFn.isConst
    guard (← isDefEq tFn dFn)

  -- Visitor for inductive types
  goType (t d : Expr) : OptionT MetaM (List Nat) := do
    let t ← whnf t
    let d ← whnf d
    checkCompatibleApps t d
    matchConstInduct t.getAppFn (fun _ => failure) fun info _ => do
      let tArgs := t.getAppArgs
      let dArgs := d.getAppArgs
      for i in [:info.numParams] do
        let tArg := tArgs[i]!
        let dArg := dArgs[i]!
        unless (← isDefEq tArg dArg) do
          return i :: (← goType tArg dArg)
      for i in [info.numParams : tArgs.size] do
        let tArg := tArgs[i]!
        let dArg := dArgs[i]!
        unless (← isDefEq tArg dArg) do
          return i :: (← goIndex tArg dArg)
      failure

  -- Visitor for indexed families
  goIndex (t d : Expr) : OptionT MetaM (List Nat) := do
    let t ← whnfD t
    let d ← whnfD d
    if t.isFVar || d.isFVar then
      return [] -- Found refinement path
    else
      checkCompatibleApps t d
      matchConstCtor t.getAppFn (fun _ => failure) fun info _ => do
        let tArgs := t.getAppArgs
        let dArgs := d.getAppArgs
        for i in [:info.numParams] do
          let tArg := tArgs[i]!
          let dArg := dArgs[i]!
          unless (← isDefEq tArg dArg) do
            failure
        for i in [info.numParams : tArgs.size] do
          let tArg := tArgs[i]!
          let dArg := dArgs[i]!
          unless (← isDefEq tArg dArg) do
            return i :: (← goIndex tArg dArg)
        failure

private partial def eraseIndices (type : Expr) : MetaM Expr := do
  let type' ← whnfD type
  matchConstInduct type'.getAppFn (fun _ => return type) fun info _ => do
    let args := type'.getAppArgs
    let params ← args[:info.numParams].toArray.mapM eraseIndices
    let result := mkAppN type'.getAppFn params
    let resultType ← inferType result
    let (newIndices, _, _) ←  forallMetaTelescopeReducing resultType (some (args.size - info.numParams))
    return mkAppN result newIndices

private def withPatternElabConfig (x : TermElabM α) : TermElabM α :=
  withoutErrToSorry <| withReader (fun ctx => { ctx with inPattern := true }) <| x

private def elabPatterns (patternStxs : Array Syntax) (matchType : Expr) : ExceptT PatternElabException TermElabM (Array Expr × Expr) :=
  withReader (fun ctx => { ctx with implicitLambda := false }) do
    let mut patterns  := #[]
    let mut matchType := matchType
    for idx in [:patternStxs.size] do
      let patternStx := patternStxs[idx]!
      matchType ← whnf matchType
      match matchType with
      | Expr.forallE _ d b _ =>
        let pattern ← do
          let s ← saveState
          try
            liftM <| withSynthesize <| withPatternElabConfig <| elabTermEnsuringType patternStx d
          catch ex : Exception =>
            restoreState s
            match (← liftM <| commitIfNoErrors? <| withPatternElabConfig do elabTermAndSynthesize patternStx (← eraseIndices d)) with
            | some pattern =>
              match (← findDiscrRefinementPath pattern d |>.run) with
              | some path =>
                restoreState s
                -- Wrap the type mismatch exception for the "discriminant refinement" feature.
                throwThe PatternElabException { ex := ex, patternIdx := idx, pathToIndex := path }
              | none => restoreState s; throw ex
            | none => throw ex
        matchType := b.instantiate1 pattern
        patterns  := patterns.push pattern
      | _ => throwError "unexpected match type"
    return (patterns, matchType)

open Meta.Match (Pattern Pattern.var Pattern.inaccessible Pattern.ctor Pattern.as Pattern.val Pattern.arrayLit AltLHS MatcherResult)

namespace ToDepElimPattern

private def throwInvalidPattern (e : Expr) : MetaM α :=
  throwError "invalid pattern {indentExpr e}"

structure State where
  patternVars : Array Expr := #[]

structure Context where
  /--
    When visiting an assigned metavariable, if it has an user-name. We save it here.
    We want to preserve these user-names when generating new pattern variables. -/
  userName : Name := Name.anonymous
  /--
    Pattern variables that were explicitly provided by the user.
    Recall that implicit parameters and `_` are elaborated as metavariables, and then converted into pattern variables
    by the `normalize` procedure.
  -/
  explicitPatternVars : Array FVarId := #[]

abbrev M := ReaderT Context $ StateRefT State TermElabM

/-- Return true iff `e` is an explicit pattern variable provided by the user. -/
def isExplicitPatternVar (e : Expr) : M Bool := do
  if e.isFVar then
    return (← read).explicitPatternVars.any (· == e.fvarId!)
  else
    return false

/--
  Helper function for "saving" the user name associated with `mvarId` (if it is not "anonymous") before visiting `x`
  The auto generalization feature will uses synthetic holes to preserve the name of the free variable included during generalization.
  For example, if we are generalizing a free variable `bla`, we add the synthetic hole `?bla` for the pattern. We use synthetic hole
  because we don't know whether `?bla` will become an inaccessible pattern or not.
  The `withMVar` method makes sure we don't "lose" this name when `isDefEq` perform assignments of the form `?bla := ?m` where `?m` has no user name.
  This can happen, for example, when the user provides a `_` pattern, or for implicit fields.
-/
private def withMVar (mvarId : MVarId) (x : M α) : M α := do
  let localDecl ← getMVarDecl mvarId
  if !localDecl.userName.isAnonymous && (← read).userName.isAnonymous then
    withReader (fun ctx => { ctx with userName := localDecl.userName }) x
  else
    x

/--
  Creating a mapping containing `b ↦ e'` where `patternWithRef e' = some (stx, b)`,
  and `e'` is a subterm of `e`.

  This is a helper function for `whnfPreservingPatternRef`. -/
private def mkPatternRefMap (e : Expr) : ExprMap Expr :=
  runST go
where
  go (σ) : ST σ (ExprMap Expr) := do
   let map : ST.Ref σ (ExprMap Expr) ← ST.mkRef {}
   e.forEachWhere isPatternWithRef fun e => do
     let some (_, b) := patternWithRef? e | unreachable!
     map.modify (·.insert b e)
   map.get

/--
  Try to restore `Syntax` ref information stored in `map` after
  applying `whnf` at `whnfPreservingPatternRef`.
  It assumes `map` has been constructed using `mkPatternRefMap`.
-/
private def applyRefMap (e : Expr) (map : ExprMap Expr) : Expr :=
  e.replace fun e =>
    match patternWithRef? e with
    | some _ => some e -- stop `e` already has annotation
    | none => match map.find? e with
      | some eWithRef => some eWithRef -- stop `e` found annotation
      | none => none -- continue

/--
  Applies `whnf` but tries to preserve `PatternWithRef` information.
  This is a bit hackish, but it is necessary for providing proper
  jump-to-definition information in examples such as
  ```
  def f (x : Nat) : Nat :=
    match x with
    | 0 => 1
    | y + 1 => y
  ```
  Without this trick, the `PatternWithRef` is lost for the `y` at the pattern `y+1`.
-/
private def whnfPreservingPatternRef (e : Expr) : MetaM Expr := do
  let eNew ← whnf e
  if eNew.isConstructorApp (← getEnv) then
    return eNew
  else
    return applyRefMap eNew (mkPatternRefMap e)

/--
  Normalize the pattern and collect all patterns variables (explicit and implicit).
  This method is the one that decides where the inaccessible annotations must be inserted.
  The pattern variables are both free variables (for explicit pattern variables) and metavariables (for implicit ones).
  Recall that `mkLambdaFVars` now allows us to abstract both free variables and metavariables.
-/
partial def normalize (e : Expr) : M Expr := do
  match inaccessible? e with
  | some e => processInaccessible e
  | none =>
  match patternWithRef? e with
  | some (ref, e) => return mkPatternWithRef (← normalize e) ref
  | none =>
    match e.arrayLit? with
    | some (α, lits) => mkArrayLit α (← lits.mapM normalize)
    | none =>
      if let some e := Match.isNamedPattern? e then
        let x := e.getArg! 1
        let p := e.getArg! 2
        let h := e.getArg! 3
        unless x.consumeMData.isFVar && h.consumeMData.isFVar do
          throwError "unexpected occurrence of auxiliary declaration 'namedPattern'"
        addVar x
        let p ← normalize p
        addVar h
        return mkApp4 e.getAppFn (e.getArg! 0) x p h
      else if isMatchValue e then
        return e
      else if e.isFVar then
        if (← isExplicitPatternVar e) then
          processVar e
        else
          return mkInaccessible e
      else if e.getAppFn.isMVar then
        let eNew ← instantiateMVars e
        if eNew != e then
          withMVar e.getAppFn.mvarId! <| normalize eNew
        else if e.isMVar then
          withMVar e.mvarId! <| processVar e
        else
          throwInvalidPattern e
      else
        let eNew ← whnfPreservingPatternRef e
        if eNew != e then
          normalize eNew
        else
          matchConstCtor e.getAppFn
            (fun _ => return mkInaccessible (← eraseInaccessibleAnnotations (← instantiateMVars e)))
            (fun v _ => do
              let args := e.getAppArgs
              unless args.size == v.numParams + v.numFields do
                throwInvalidPattern e
              let params := args.extract 0 v.numParams
              let params ← params.mapM fun p => instantiateMVars p
              let fields := args.extract v.numParams args.size
              let fields ← fields.mapM normalize
              return mkAppN e.getAppFn (params ++ fields))
where
  addVar (e : Expr) : M Unit := do
    let e ← erasePatternRefAnnotations e
    unless (← get).patternVars.contains e do
      modify fun s => { s with patternVars := s.patternVars.push e }

  processVar (e : Expr) : M Expr := do
    let e' ← erasePatternRefAnnotations e
    if (← get).patternVars.contains e' then
      return mkInaccessible (← eraseInaccessibleAnnotations e)
    else
      if e'.isMVar then
        e'.mvarId!.setTag (← read).userName
      modify fun s => { s with patternVars := s.patternVars.push e' }
      return e

  processInaccessible (e : Expr) : M Expr := do
    let e' ← erasePatternRefAnnotations e
    match e' with
    | Expr.fvar _ =>
      if (← isExplicitPatternVar e') then
        processVar e
      else
        return mkInaccessible e
    | _ =>
      if e'.getAppFn.isMVar then
        let eNew ← instantiateMVars e'
        if eNew != e' then
          withMVar e'.getAppFn.mvarId! <| processInaccessible eNew
        else if e'.isMVar then
          withMVar e'.mvarId! <| processVar e'
        else
          throwInvalidPattern e
      else
        return mkInaccessible (← eraseInaccessibleAnnotations (← instantiateMVars e))

/--
  Auxiliary function for combining the `matchType` and all patterns into a single expression.
  We use it before we abstract all patterns variables. -/
private partial def packMatchTypePatterns (matchType : Expr) (ps : Array Expr) : MetaM Expr :=
  ps.foldlM (init := matchType) fun result p => mkAppM ``PProd.mk #[result, p]

/-- The inverse of `packMatchTypePatterns`. -/
private partial def unpackMatchTypePatterns (p : Expr) : Expr × Array Expr :=
  if p.isAppOf ``PProd.mk then
    let (matchType, ps) := unpackMatchTypePatterns (p.getArg! 2)
    (matchType, ps.push (p.getArg! 3))
  else
    (p, #[])

/--
  Convert a (normalized) pattern encoded as an `Expr` into a `Pattern`.
  This method assumes that `e` has been normalized and the explicit and implicit (i.e., metavariables) pattern variables have
  already been abstracted and converted back into new free variables.
 -/
private partial def toPattern (e : Expr) : MetaM Pattern := do
  match inaccessible? e with
  | some e => return Pattern.inaccessible e
  | none =>
    match e.arrayLit? with
    | some (α, lits) => return Pattern.arrayLit α (← lits.mapM toPattern)
    | none =>
      if let some e := Match.isNamedPattern? e then
        let p ← toPattern <| e.getArg! 2
        match e.getArg! 1, e.getArg! 3 with
        | Expr.fvar x, Expr.fvar h => return Pattern.as x p h
        | _,           _           => throwError "unexpected occurrence of auxiliary declaration 'namedPattern'"
      else if isMatchValue e then
        return Pattern.val e
      else if e.isFVar then
        return Pattern.var e.fvarId!
      else
        matchConstCtor e.getAppFn (fun _ => unreachable!) fun v us => do
          let args := e.getAppArgs
          let params := args.extract 0 v.numParams
          let params ← params.mapM fun p => instantiateMVars p
          let fields := args.extract v.numParams args.size
          let fields ← fields.mapM toPattern
          return Pattern.ctor v.name us params.toList fields.toList

structure TopSort.State where
  visitedFVars : FVarIdSet := {}
  visitedMVars : MVarIdSet := {}
  result       : Array Expr := #[]

abbrev TopSortM := StateRefT TopSort.State TermElabM

/--
  Topological sort. We need it because inaccessible patterns may contain pattern variables that are declared later.
  That is, processing patterns from left to right to do not guarantee that the pattern variables are collected in the
  "right" order. "Right" here means pattern `x` must occur before pattern `y` if `y`s type depends on `x`.
-/
private partial def topSort (patternVars : Array Expr) : TermElabM (Array Expr) := do
  let (_, s) ← patternVars.mapM visit |>.run {}
  return s.result
where
  visit (e : Expr) : TopSortM Unit := do
    match e with
    | Expr.proj _ _ e      => visit e
    | Expr.forallE _ d b _ => visit d; visit b
    | Expr.lam _ d b _     => visit d; visit b
    | Expr.letE _ t v b _  => visit t; visit v; visit b
    | Expr.app f a         => visit f; visit a
    | Expr.mdata _ b       => visit b
    | Expr.mvar mvarId     =>
      let v ← instantiateMVars e
      if !v.isMVar then
        visit v
      else if patternVars.contains e then
        unless (← get).visitedMVars.contains mvarId do
          modify fun s => { s with visitedMVars := s.visitedMVars.insert mvarId }
          let mvarDecl ← getMVarDecl mvarId
          visit mvarDecl.type
          modify fun s => { s with result := s.result.push e }
    | Expr.fvar fvarId    =>
      if patternVars.contains e then
        unless (← get).visitedFVars.contains fvarId do
          modify fun s => { s with visitedFVars := s.visitedFVars.insert fvarId }
          visit (← fvarId.getType)
          modify fun s => { s with result := s.result.push e }
    | _ => return ()

/--
  Save pattern information in the info tree, and remove `patternWithRef?` annotations.
-/
partial def savePatternInfo (p : Expr) : TermElabM Expr :=
  go p |>.run false
where
  /-- The `Bool` context is true iff we are inside of an "inaccessible" pattern. -/
  go (p : Expr) : ReaderT Bool TermElabM Expr := do
    match p with
    | .forallE n d b bi  => withLocalDecl n bi (← go d) fun x => do mkForallFVars #[x] (← go (b.instantiate1 x))
    | .lam n d b bi      => withLocalDecl n bi (← go d) fun x => do mkLambdaFVars #[x] (← go (b.instantiate1 x))
    | .letE n t v b ..  => withLetDecl n (← go t) (← go v) fun x => do mkLetFVars #[x] (← go (b.instantiate1 x))
    | .app f a          => return mkApp (← go f) (← go a)
    | .proj _ _ b       => return p.updateProj! (← go b)
    | .mdata k b        =>
      if inaccessible? p |>.isSome then
        return mkMData k (← withReader (fun _ => false) (go b))
      else if let some (stx, p) := patternWithRef? p then
        Elab.withInfoContext' (go p) fun p => do
          /- If `p` is a free variable and we are not inside of an "inaccessible" pattern, this `p` is a binder. -/
          mkTermInfo Name.anonymous stx p (isBinder := p.isFVar && !(← read))
      else
        return mkMData k (← go b)
    | _ => return p

/--
  Main method for `withDepElimPatterns`.
  - `PatternVarDecls`: are the explicit pattern variables provided by the user.
  - `ps`: are the patterns provided by the user.
  - `matchType`: the expected typ for this branch. It depends on the explicit pattern variables and the implicit ones that are still represented as metavariables,
     and are found by this function.
  - `k` is the continuation that is executed in an updated local context with the all pattern variables (explicit and implicit). Note that, `patternVarDecls` are all
     replaced since they may depend on implicit pattern variables (i.e., metavariables) that are converted into new free variables by this method.
 -/
partial def main (patternVarDecls : Array PatternVarDecl) (ps : Array Expr) (matchType : Expr) (k : Array LocalDecl → Array Pattern → Expr → TermElabM α) : TermElabM α := do
  let explicitPatternVars := patternVarDecls.map fun decl => decl.fvarId
  let (ps, s) ← ps.mapM normalize |>.run { explicitPatternVars } |>.run {}
  let patternVars ← topSort s.patternVars
  trace[Elab.match] "patternVars after topSort: {patternVars}"
  for explicit in explicitPatternVars do
    unless patternVars.any (· == mkFVar explicit) do
      withInPattern do
        throwError "invalid patterns, `{mkFVar explicit}` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching{indentD (MessageData.joinSep (ps.toList.map (MessageData.ofExpr .)) m!"\n\n")}"
  let packed ← pack patternVars ps matchType
  trace[Elab.match] "packed: {packed}"
  let lctx := explicitPatternVars.foldl (init := (← getLCtx)) fun lctx d => lctx.erase d
  withTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) do
    check packed
    unpack packed fun patternVars patterns matchType => do
      let localDecls ← patternVars.mapM fun x => x.fvarId!.getDecl
      trace[Elab.match] "patternVars: {patternVars}, matchType: {matchType}"
      k localDecls (← patterns.mapM fun p => toPattern p) matchType
where
  pack (patternVars : Array Expr) (ps : Array Expr) (matchType : Expr) : MetaM Expr := do
    /-
     Recall that some of the `patternVars` are metavariables without a user facing name.
     Thus, this method tries to infer names for them using `ps` before performing the `mkLambdaFVars` abstraction.
     Let `?m` be a metavariable in `patternVars` without a user facing name.
     The heuristic uses the patterns `ps`. We traverse the patterns from right to left searching for applications
     `f ... ?m`. The name for the corresponding `f`-parameter is used to name `?m`.
     We search from right to left to make sure we visit a pattern before visiting its indices. Example:
     ```
     #[@List.cons α i ?m, @HList.cons α β i ?m a as, @Member.head α i ?m]
     ```
    -/
    let setMVarsAt (e : Expr) : StateRefT (Array MVarId) MetaM Unit := do
      let mvarIds ← setMVarUserNamesAt (← erasePatternRefAnnotations e) patternVars
      modify (· ++ mvarIds)
    let go : StateRefT (Array MVarId) MetaM Expr := do
      try
        for p in ps.reverse do
          setMVarsAt p
        mkLambdaFVars patternVars (← packMatchTypePatterns matchType ps) (binderInfoForMVars := BinderInfo.default)
      finally
        resetMVarUserNames (← get)
    go |>.run' #[]

  unpack (packed : Expr) (k : (patternVars : Array Expr) → (patterns : Array Expr) → (matchType : Expr) → TermElabM α) : TermElabM α :=
    let rec go (packed : Expr) (patternVars : Array Expr) : TermElabM α := do
      match packed with
      | .lam n d b _ =>
        withLocalDeclD n (← erasePatternRefAnnotations (← eraseInaccessibleAnnotations d)) fun patternVar =>
          go (b.instantiate1 patternVar) (patternVars.push patternVar)
      | _ =>
        let (matchType, patterns) := unpackMatchTypePatterns packed
        let matchType ← erasePatternRefAnnotations (← eraseInaccessibleAnnotations matchType)
        let patterns ← patterns.mapM (savePatternInfo ·)
        k patternVars patterns matchType
    go packed #[]

end ToDepElimPattern

def withDepElimPatterns (patternVarDecls : Array PatternVarDecl) (ps : Array Expr) (matchType : Expr) (k : Array LocalDecl → Array Pattern → Expr → TermElabM α) : TermElabM α := do
  ToDepElimPattern.main patternVarDecls ps matchType k

private def withElaboratedLHS {α} (ref : Syntax) (patternVarDecls : Array PatternVarDecl) (patternStxs : Array Syntax) (matchType : Expr)
    (k : AltLHS → Expr → TermElabM α) : ExceptT PatternElabException TermElabM α := do
  let (patterns, matchType) ← withSynthesize <| elabPatterns patternStxs matchType
  id (α := TermElabM α) do
    trace[Elab.match] "patterns: {patterns}"
    withDepElimPatterns patternVarDecls patterns matchType fun localDecls patterns matchType => do
      k { ref := ref, fvarDecls := localDecls.toList, patterns := patterns.toList } matchType

/--
  Try to clear the free variables in `toClear` and auxiliary discriminants, and then execute `k` in the updated local context.
  If `type` or another local variables depends on a free variable in `toClear`, then it is not cleared.
-/
private def withToClear (toClear : Array FVarId) (type : Expr) (k : TermElabM α) : TermElabM α := do
  if toClear.isEmpty then
    k
  else
    let toClear ← sortFVarIds toClear
    trace[Elab.match] ">> toClear {toClear.map mkFVar}"
    let mut lctx ← getLCtx
    let mut localInsts ← getLocalInstances
    for fvarId in toClear.reverse do
      if !(← dependsOn type fvarId) then
        if !(← lctx.anyM fun localDecl => pure (localDecl.fvarId != fvarId) <&&> localDeclDependsOn localDecl fvarId) then
          lctx := lctx.erase fvarId
          localInsts := localInsts.filter fun localInst => localInst.fvar.fvarId! != fvarId
    withLCtx lctx localInsts k

/--
  Generate equalities `h : discr = pattern` for discriminants annotated with `h :`.
  We use these equalities to elaborate the right-hand-side of a `match` alternative.
-/
private def withEqs (discrs : Array Discr) (patterns : List Pattern) (k : Array Expr → TermElabM α) : TermElabM α := do
  go 0 patterns #[]
where
  go (i : Nat) (ps : List Pattern) (eqs : Array Expr) : TermElabM α := do
    match ps with
    | [] => k eqs
    | p::ps =>
      if h : i < discrs.size then
        let discr := discrs.get ⟨i, h⟩
        if let some h := discr.h? then
          withLocalDeclD h.getId (← mkEqHEq discr.expr (← p.toExpr)) fun eq => do
            addTermInfo' h eq (isBinder := true)
            go (i+1) ps (eqs.push eq)
        else
          go (i+1) ps eqs
      else
        k eqs

/--
  Elaborate the `match` alternative `alt` using the given `matchType`.
  The array `toClear` contains variables that must be cleared before elaborating the `rhs` because
  they have been generalized/refined.
-/
private def elabMatchAltView (discrs : Array Discr) (alt : MatchAltView) (matchType : Expr) (toClear : Array FVarId) : ExceptT PatternElabException TermElabM (AltLHS × Expr) := withRef alt.ref do
    let (patternVars, alt) ← collectPatternVars alt
    trace[Elab.match] "patternVars: {patternVars}"
    withPatternVars patternVars fun patternVarDecls => do
      withElaboratedLHS alt.ref patternVarDecls alt.patterns matchType fun altLHS matchType =>
        withEqs discrs altLHS.patterns fun eqs =>
          withLocalInstances altLHS.fvarDecls do
            trace[Elab.match] "elabMatchAltView: {matchType}"
            -- connect match-generalized pattern fvars, which are a suffix of `latLHS.fvarDecls`,
            -- to their original fvars (independently of whether they were cleared successfully) in the info tree
            for (fvar, baseId) in altLHS.fvarDecls.toArray.reverse.zip toClear.reverse do
              pushInfoLeaf <| .ofFVarAliasInfo { id := fvar.fvarId, baseId, userName := fvar.userName }
            let matchType ← instantiateMVars matchType
            -- If `matchType` is of the form `@m ...`, we create a new metavariable with the current scope.
            -- This improves the effectiveness of the `isDefEq` default approximations
            let matchType' ← if matchType.getAppFn.isMVar then mkFreshTypeMVar else pure matchType
            withToClear toClear matchType' do
              let rhs ← elabTermEnsuringType alt.rhs matchType'
              -- We use all approximations to ensure the auxiliary type is defeq to the original one.
              unless (← fullApproxDefEq <| isDefEq matchType' matchType) do
                throwError "type mistmatch, alternative {← mkHasTypeButIsExpectedMsg matchType' matchType}"
              let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr ++ eqs
              let rhs ← if xs.isEmpty then pure <| mkSimpleThunk rhs else mkLambdaFVars xs rhs
              trace[Elab.match] "rhs: {rhs}"
              return (altLHS, rhs)

/--
  Collect problematic index for the "discriminant refinement feature". This method is invoked
  when we detect a type mismatch at a pattern #`idx` of some alternative. -/
private partial def getIndexToInclude? (discr : Expr) (pathToIndex : List Nat) : TermElabM (Option Expr) := do
  go (← inferType discr) pathToIndex |>.run
where
  go (e : Expr) (path : List Nat) : OptionT MetaM Expr := do
    match path with
    | [] => return e
    | i::path =>
      let e ← whnfD e
      guard <| e.isApp && i < e.getAppNumArgs
      go (e.getArg! i) path

structure GeneralizeResult where
  discrs    : Array Discr
  /-- `FVarId`s of the variables that have been generalized. We store them to clear after in each branch. -/
  toClear   : Array FVarId := #[]
  matchType : Expr
  altViews  : Array MatchAltView
  refined   : Bool := false

/--
  "Generalize" variables that depend on the discriminants.

  Remarks and limitations:
  - We currently do not generalize let-decls.
  - We abort generalization if the new `matchType` is type incorrect.
  - Only discriminants that are free variables are considered during specialization.
  - We "generalize" by adding new discriminants and pattern variables. We do not "clear" the generalized variables,
    but they become inaccessible since they are shadowed by the patterns variables. We assume this is ok since
    this is the exact behavior users would get if they had written it by hand. Recall there is no `clear` in term mode.
-/
private def generalize (discrs : Array Discr) (matchType : Expr) (altViews : Array MatchAltView) (generalizing? : Option Bool) : TermElabM GeneralizeResult := do
  let gen := if let some g := generalizing? then g else true
  if !gen then
    return { discrs, matchType, altViews }
  else
    let discrExprs := discrs.map (·.expr)
    /- let-decls are currently being ignored by the generalizer. -/
    let ysFVarIds ← getFVarsToGeneralize discrExprs (ignoreLetDecls := true)
    if ysFVarIds.isEmpty then
      return { discrs, matchType, altViews }
    else
      let ys := ysFVarIds.map mkFVar
      let matchType' ← forallBoundedTelescope matchType discrs.size fun ds type => do
        let type ← mkForallFVars ys type
        let (discrs', ds') := Array.unzip <| Array.zip discrExprs ds |>.filter fun (di, _) => di.isFVar
        let type := type.replaceFVars discrs' ds'
        mkForallFVars ds type
      if (← isTypeCorrect matchType') then
        let discrs := discrs ++  ys.map fun y => { expr := y : Discr }
        let altViews ← altViews.mapM fun altView => do
          let patternVars ← getPatternsVars altView.patterns
          -- We traverse backwards because we want to keep the most recent names.
          -- For example, if `ys` contains `#[h, h]`, we want to make sure `mkFreshUsername is applied to the first `h`,
          -- since it is already shadowed by the second.
          let ysUserNames ← ys.foldrM (init := #[]) fun ys ysUserNames => do
            let yDecl ← ys.fvarId!.getDecl
            let mut yUserName := yDecl.userName
            if ysUserNames.contains yUserName then
              yUserName ← mkFreshUserName yUserName
            -- Explicitly provided pattern variables shadow `y`
            else if patternVars.any fun x => x.getId == yUserName then
              yUserName ← mkFreshUserName yUserName
            return ysUserNames.push yUserName
          let ysIds ← ysUserNames.reverse.mapM fun n => return mkIdentFrom (← getRef) n
          return { altView with patterns := altView.patterns ++ ysIds }
        return { discrs, toClear := ysFVarIds, matchType := matchType', altViews, refined := true }
      else
        return { discrs, matchType, altViews }


private partial def elabMatchAltViews (generalizing? : Option Bool) (discrs : Array Discr) (matchType : Expr) (altViews : Array MatchAltView) : TermElabM (Array Discr × Expr × Array (AltLHS × Expr) × Bool) := do
  loop discrs #[] matchType altViews none
where
  /--
    "Discriminant refinement" main loop.
    `first?` contains the first error message we found before updated the `discrs`. -/
  loop (discrs : Array Discr) (toClear : Array FVarId) (matchType : Expr) (altViews : Array MatchAltView) (first? : Option (SavedState × Exception))
      : TermElabM (Array Discr × Expr × Array (AltLHS × Expr) × Bool) := do
    let s ← saveState
    let { discrs := discrs', toClear := toClear', matchType := matchType', altViews := altViews', refined } ← generalize discrs matchType altViews generalizing?
    match (← altViews'.mapM (fun altView => elabMatchAltView discrs' altView matchType' (toClear ++ toClear')) |>.run) with
    | Except.ok alts => return (discrs', matchType', alts, first?.isSome || refined)
    | Except.error { patternIdx := patternIdx, pathToIndex := pathToIndex, ex := ex } =>
      let discr := discrs[patternIdx]!
      let some index ← getIndexToInclude? discr.expr pathToIndex
        | throwEx (← updateFirst first? ex)
      trace[Elab.match] "index to include: {index}"
      if (← discrs.anyM fun discr => isDefEq discr.expr index) then
        throwEx (← updateFirst first? ex)
      let first ← updateFirst first? ex
      s.restore (restoreInfo := true)
      let indices ← collectDeps #[index] (discrs.map (·.expr))
      let matchType ← try
        updateMatchType indices matchType
      catch _ => throwEx first
      let ref ← getRef
      trace[Elab.match] "new indices to add as discriminants: {indices}"
      let wildcards ← indices.mapM fun index => do
        if index.isFVar then
          let localDecl ← index.fvarId!.getDecl
          if localDecl.userName.hasMacroScopes then
            return mkHole ref
          else
            let id := mkIdentFrom ref localDecl.userName
            `(?$id)
        else
          return mkHole ref
      let altViews  := altViews.map fun altView => { altView with patterns := wildcards ++ altView.patterns }
      let indDiscrs ← indices.mapM fun i => do
        match discr.h? with
        | none => return { expr := i : Discr }
        | some h =>
          -- If the discriminant that introduced this index is annotated with `h : discr`, then we should annotate the new discriminant too.
          let h := mkIdentFrom h (← mkFreshUserName `h)
          return { expr := i, h? := h : Discr }
      let discrs    := indDiscrs ++ discrs
      let indexFVarIds := indices.filterMap fun | .fvar fvarId .. => some fvarId | _  => none
      loop discrs (toClear ++ indexFVarIds) matchType altViews first

  throwEx {α} (p : SavedState × Exception) : TermElabM α := do
    p.1.restore (restoreInfo := true); throw p.2

  updateFirst (first? : Option (SavedState × Exception)) (ex : Exception) : TermElabM (SavedState × Exception) := do
    match first? with
    | none       => return (← saveState, ex)
    | some first => return first

  containsFVar (es : Array Expr) (fvarId : FVarId) : Bool :=
    es.any fun e => e.isFVar && e.fvarId! == fvarId

  /-- Update `indices` by including any free variable `x` s.t.
     - Type of some `discr` depends on `x`.
     - Type of `x` depends on some free variable in `indices`.

     If we don't include these extra variables in indices, then
     `updateMatchType` will generate a type incorrect term.
     For example, suppose `discr` contains `h : @HEq α a α b`, and
     `indices` is `#[α, b]`, and `matchType` is `@HEq α a α b → B`.
     `updateMatchType indices matchType` produces the type
     `(α' : Type) → (b : α') → @HEq α' a α' b → B` which is type incorrect
     because we have `a : α`.
     The method `collectDeps` will include `a` into `indices`.

     This method does not handle dependencies among non-free variables.
     We rely on the type checking method `check` at `updateMatchType`.

     Remark: `indices : Array Expr` does not need to be an array anymore.
     We should cleanup this code, and use `index : Expr` instead.
   -/
  collectDeps (indices : Array Expr) (discrs : Array Expr) : TermElabM (Array Expr) := do
    let mut s : CollectFVars.State := {}
    for discr in discrs do
      s := collectFVars s (← instantiateMVars (← inferType discr))
    let (indicesFVar, indicesNonFVar) := indices.split Expr.isFVar
    let indicesFVar := indicesFVar.map Expr.fvarId!
    let mut toAdd := #[]
    for fvarId in s.fvarSet.toList do
      unless containsFVar discrs fvarId || containsFVar indices fvarId do
        let localDecl ← fvarId.getDecl
        for indexFVarId in indicesFVar do
          if (← localDeclDependsOn localDecl indexFVarId) then
            toAdd := toAdd.push fvarId
    let indicesFVar ← sortFVarIds (indicesFVar ++ toAdd)
    return indicesFVar.map mkFVar ++ indicesNonFVar

  updateMatchType (indices : Array Expr) (matchType : Expr) : TermElabM Expr := do
    let matchType ← indices.foldrM (init := matchType) fun index matchType => do
      let indexType ← inferType index
      let matchTypeBody ← kabstract matchType index
      let userName ← mkUserNameFor index
      return Lean.mkForall userName BinderInfo.default indexType matchTypeBody
    check matchType
    return matchType


def mkMatcher (input : Meta.Match.MkMatcherInput) : TermElabM MatcherResult :=
  Meta.Match.mkMatcher input

register_builtin_option match.ignoreUnusedAlts : Bool := {
  defValue := false
  descr := "if true, do not generate error if an alternative is not used"
}

def reportMatcherResultErrors (altLHSS : List AltLHS) (result : MatcherResult) : TermElabM Unit := do
  unless result.counterExamples.isEmpty do
    withHeadRefOnly <| logError m!"missing cases:\n{Meta.Match.counterExamplesToMessageData result.counterExamples}"
    return ()
  unless match.ignoreUnusedAlts.get (← getOptions) || result.unusedAltIdxs.isEmpty do
    let mut i := 0
    for alt in altLHSS do
      if result.unusedAltIdxs.contains i then
        withRef alt.ref do
          logError "redundant alternative"
      i := i + 1

/--
  If `altLHSS + rhss` is encoding `| PUnit.unit => rhs[0]`, return `rhs[0]`
  Otherwise, return none.
-/
private def isMatchUnit? (altLHSS : List Match.AltLHS) (rhss : Array Expr) : MetaM (Option Expr) := do
  assert! altLHSS.length == rhss.size
  match altLHSS with
  | [ { fvarDecls := [], patterns := [ Pattern.ctor `PUnit.unit .. ], .. } ] =>
    /- Recall that for alternatives of the form `| PUnit.unit => rhs`, `rhss[0]` is of the form `fun _ : Unit => b`. -/
    match rhss[0]! with
    | Expr.lam _ _ b _ => return if b.hasLooseBVars then none else b
    | _ => return none
  | _ => return none

private def elabMatchAux (generalizing? : Option Bool) (discrStxs : Array Syntax) (altViews : Array MatchAltView) (matchOptMotive : Syntax) (expectedType : Expr)
    : TermElabM Expr := do
  let mut generalizing? := generalizing?
  if !matchOptMotive.isNone then
    if generalizing? == some true then
      throwError "the '(generalizing := true)' parameter is not supported when the 'match' motive is explicitly provided"
    generalizing? := some false
  let (discrs, matchType, altLHSS, isDep, rhss) ← commitIfDidNotPostpone do
    let ⟨discrs, matchType, isDep, altViews⟩ ← elabMatchTypeAndDiscrs discrStxs matchOptMotive altViews expectedType
    let matchAlts ← liftMacroM <| expandMacrosInPatterns altViews
    trace[Elab.match] "matchType: {matchType}"
    let (discrs, matchType, alts, refined) ← elabMatchAltViews generalizing? discrs matchType matchAlts
    let isDep := isDep || refined
    /-
     We should not use `synthesizeSyntheticMVarsNoPostponing` here. Otherwise, we will not be
     able to elaborate examples such as:
     ```
     def f (x : Nat) : Option Nat := none

     def g (xs : List (Nat × Nat)) : IO Unit :=
     xs.forM fun x =>
       match f x.fst with
       | _ => pure ()
     ```
     If `synthesizeSyntheticMVarsNoPostponing`, the example above fails at `x.fst` because
     the type of `x` is only available after we process the last argument of `List.forM`.

     We apply pending default types to make sure we can process examples such as
     ```
     let (a, b) := (0, 0)
     ```
    -/
    synthesizeSyntheticMVarsUsingDefault
    let rhss := alts.map Prod.snd
    let matchType ← instantiateMVars matchType
    let altLHSS ← alts.toList.mapM fun alt => do
      let altLHS ← Match.instantiateAltLHSMVars alt.1
      /- Remark: we try to postpone before throwing an error.
         The combinator `commitIfDidNotPostpone` ensures we backtrack any updates that have been performed.
         The quick-check `waitExpectedTypeAndDiscrs` minimizes the number of scenarios where we have to postpone here.
         Here is an example that passes the `waitExpectedTypeAndDiscrs` test, but postpones here.
         ```
          def bad (ps : Array (Nat × Nat)) : Array (Nat × Nat) :=
            (ps.filter fun (p : Prod _ _) =>
              match p with
              | (x, y) => x == 0)
            ++
            ps
         ```
         When we try to elaborate `fun (p : Prod _ _) => ...` for the first time, we haven't propagated the type of `ps` yet
         because `Array.filter` has type `{α : Type u_1} → (α → Bool) → (as : Array α) → optParam Nat 0 → optParam Nat (Array.size as) → Array α`
         However, the partial type annotation `(p : Prod _ _)` makes sure we succeed at the quick-check `waitExpectedTypeAndDiscrs`.
      -/
      withRef altLHS.ref do
        for d in altLHS.fvarDecls do
          if d.hasExprMVar then
            tryPostpone
            withExistingLocalDecls altLHS.fvarDecls do
              runPendingTacticsAt d.type
              if (← instantiateMVars d.type).hasExprMVar then
                throwMVarError m!"invalid match-expression, type of pattern variable '{d.toExpr}' contains metavariables{indentExpr d.type}"
        for p in altLHS.patterns do
          if (← Match.instantiatePatternMVars p).hasExprMVar then
            tryPostpone
            withExistingLocalDecls altLHS.fvarDecls do
              throwMVarError m!"invalid match-expression, pattern contains metavariables{indentExpr (← p.toExpr)}"
        pure altLHS
    return (discrs, matchType, altLHSS, isDep, rhss)
  if let some r ← if isDep then pure none else isMatchUnit? altLHSS rhss then
    return r
  else
    let numDiscrs := discrs.size
    let matcherName ← mkAuxName `match
    let matcherResult ← mkMatcher { matcherName, matchType, discrInfos := discrs.map fun discr => { hName? := discr.h?.map (·.getId) }, lhss := altLHSS }
    reportMatcherResultErrors altLHSS matcherResult
    matcherResult.addMatcher
    let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
    let r := mkApp matcherResult.matcher motive
    let r := mkAppN r (discrs.map (·.expr))
    let r := mkAppN r rhss
    trace[Elab.match] "result: {r}"
    return r

-- leading_parser "match " >> optional generalizingParam >> optional motive >> sepBy1 matchDiscr ", " >> " with " >> ppDedent matchAlts

private def getDiscrs (matchStx : Syntax) : Array Syntax :=
  matchStx[3].getSepArgs

private def getMatchOptMotive (matchStx : Syntax) : Syntax :=
  matchStx[2]

open TSyntax.Compat in
private def expandNonAtomicDiscrs? (matchStx : Syntax) : TermElabM (Option Syntax) :=
  let matchOptMotive := getMatchOptMotive matchStx
  if matchOptMotive.isNone then do
    let discrs := getDiscrs matchStx
    let allLocal ← discrs.allM fun discr => isAtomicDiscr discr[1]
    if allLocal then
      return none
    else
      let rec loop (discrs : List Syntax) (discrsNew : Array Syntax)  := do
        match discrs with
        | [] =>
          let discrs := Syntax.mkSep discrsNew (mkAtomFrom matchStx ", ")
          pure (matchStx.setArg 3 discrs)
        | discr :: discrs =>
          -- Recall that
          -- matchDiscr := leading_parser optional (ident >> ":") >> termParser
          let term := discr[1]
          if (← isAtomicDiscr term) then
            loop discrs (discrsNew.push discr)
          else
            withFreshMacroScope do
              let discrNew := discr.setArg 1 (← `(?x))
              let r ← loop discrs (discrsNew.push discrNew)
              `(let_mvar% ?x := $term; $r)
      return some (← loop discrs.toList #[])
  else
    -- We do not pull non atomic discriminants when match type is provided explicitly by the user
    return none

private def waitExpectedType (expectedType? : Option Expr) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
    | some expectedType => pure expectedType
    | none              => mkFreshTypeMVar

private def tryPostponeIfDiscrTypeIsMVar (matchStx : Syntax) : TermElabM Unit := do
  -- We don't wait for the discriminants types when match type is provided by user
  if getMatchOptMotive matchStx |>.isNone then
    let discrs := getDiscrs matchStx
    for discr in discrs do
      let term := discr[1]
      let d ← elabTerm term none
      let dType ← inferType d
      trace[Elab.match] "discr {d} : {← instantiateMVars dType}"
      tryPostponeIfMVar dType

/--
We (try to) elaborate a `match` only when the expected type is available.
If the `matchType` has not been provided by the user, we also try to postpone elaboration if the type
of a discriminant is not available. That is, it is of the form `(?m ...)`.
We use `expandNonAtomicDiscrs?` to make sure all discriminants are metavariables,
so that they are not elaborated twice.
This is a standard trick we use in the elaborator, and it is also used to elaborate structure instances.
Suppose, we are trying to elaborate
```
match g x with
  | ... => ...
```
`expandNonAtomicDiscrs?` converts it intro
```
let_mvar% ?discr := g x
match ?discr with
  | ... => ...
```

This elaboration technique is needed to elaborate terms such as:
```lean
xs.filter fun (a, b) => a > b
```
which are syntax sugar for
```lean
List.filter (fun p => match p with | (a, b) => a > b) xs
```
When we visit `match p with | (a, b) => a > b`, we don't know the type of `p` yet.
-/
private def waitExpectedTypeAndDiscrs (matchStx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar expectedType?
  tryPostponeIfDiscrTypeIsMVar matchStx
  match expectedType? with
  | some expectedType => return expectedType
  | none              => mkFreshTypeMVar

/--
```
leading_parser "match " >> optional generalizingParam >> optional motive >> sepBy1 matchDiscr ", " >> " with " >> ppDedent matchAlts
```
Remark the `optIdent` must be `none` at `matchDiscr`. They are expanded by `expandMatchDiscr?`.
-/
private def elabMatchCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let expectedType   ← waitExpectedTypeAndDiscrs stx expectedType?
  let discrStxs      := (getDiscrs stx).map fun d => d
  let gen?           := getMatchGeneralizing? stx
  let altViews       := getMatchAlts stx
  let matchOptMotive := getMatchOptMotive stx
  elabMatchAux gen? discrStxs altViews matchOptMotive expectedType

private def isPatternVar (stx : Syntax) : TermElabM Bool := do
  match (← resolveId? stx "pattern") with
  | none   => return isAtomicIdent stx
  | some f => match f with
    | Expr.const fName _ =>
      match (← getEnv).find? fName with
      | some (ConstantInfo.ctorInfo _) => return false
      | some _                         => return !hasMatchPatternAttribute (← getEnv) fName
      | _                              => return isAtomicIdent stx
    | _ => return isAtomicIdent stx
where
  isAtomicIdent (stx : Syntax) : Bool :=
    stx.isIdent && stx.getId.eraseMacroScopes.isAtomic

@[builtin_term_elab «match»] def elabMatch : TermElab := fun stx expectedType? => do
  match stx with
  | `(match $discr:term with | $y:ident => $rhs) =>
     if (← isPatternVar y) then expandSimpleMatch stx discr y rhs expectedType? else elabMatchDefault stx expectedType?
  | _ => elabMatchDefault stx expectedType?
where
  elabMatchDefault (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
    match (← liftMacroM <| expandMatchAlts? stx) with
    | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
    | none =>
    match (← expandNonAtomicDiscrs? stx) with
    | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
    | none =>
      let discrs         := getDiscrs stx
      let matchOptMotive := getMatchOptMotive stx
      if !matchOptMotive.isNone && discrs.any fun d => !d[0].isNone then
        throwErrorAt matchOptMotive "match motive should not be provided when discriminants with equality proofs are used"
      elabMatchCore stx expectedType?

builtin_initialize
  registerTraceClass `Elab.match

-- leading_parser:leadPrec "nomatch " >> termParser
@[builtin_term_elab «nomatch»] def elabNoMatch : TermElab := fun stx expectedType? => do
  match stx with
  | `(nomatch $discrExpr) =>
    if (← isAtomicDiscr discrExpr) then
      let expectedType ← waitExpectedType expectedType?
      let discr := mkNode ``Lean.Parser.Term.matchDiscr #[mkNullNode, discrExpr]
      elabMatchAux none #[discr] #[] mkNullNode expectedType
    else
      let stxNew ← `(let_mvar% ?x := $discrExpr; nomatch ?x)
      withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
