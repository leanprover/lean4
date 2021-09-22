/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectFVars
import Lean.Meta.Match.MatchPatternAttr
import Lean.Meta.Match.Match
import Lean.Meta.SortLocalDecls
import Lean.Meta.GeneralizeVars
import Lean.Elab.SyntheticMVars
import Lean.Elab.Arg
import Lean.Parser.Term
import Lean.Elab.PatternVar

namespace Lean.Elab.Term
open Meta
open Lean.Parser.Term

private def expandSimpleMatch (stx discr lhsVar rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let newStx ← `(let $lhsVar := $discr; $rhs)
  withMacroExpansion stx newStx <| elabTerm newStx expectedType?

private def mkUserNameFor (e : Expr) : TermElabM Name := do
  match e with
  /- Remark: we use `mkFreshUserName` to make sure we don't add a variable to the local context that can be resolved to `e`. -/
  | Expr.fvar fvarId _ => mkFreshUserName ((← getLocalDecl fvarId).userName)
  | _                  => mkFreshBinderName

/-- Return true iff `n` is an auxiliary variable created by `expandNonAtomicDiscrs?` -/
def isAuxDiscrName (n : Name) : Bool :=
  n.hasMacroScopes && n.eraseMacroScopes == `_discr

/--
   We treat `@x` as atomic to avoid unnecessary extra local declarations from being
   inserted into the local context. Recall that `expandMatchAltsIntoMatch` uses `@` modifier.
   Thus this is kind of discriminant is quite common.

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
def isAtomicDiscr? (discr : Syntax) : TermElabM (Option Expr) := do
  match discr with
  | `($x:ident)  => isLocalIdent? x
  | `(@$x:ident) => isLocalIdent? x
  | _ => if discr.isMissing then throwAbortTerm else return none

-- See expandNonAtomicDiscrs?
private def elabAtomicDiscr (discr : Syntax) : TermElabM Expr := do
  let term := discr[1]
  match (← isAtomicDiscr? term) with
  | some e@(Expr.fvar fvarId _) =>
    let localDecl ← getLocalDecl fvarId
    if !isAuxDiscrName localDecl.userName then
      return e -- it is not an auxiliary local created by `expandNonAtomicDiscrs?`
    else
      instantiateMVars localDecl.value
  | _ => throwErrorAt discr "unexpected discriminant"

structure ElabMatchTypeAndDiscrsResult where
  discrs    : Array Expr
  matchType : Expr
  /- `true` when performing dependent elimination. We use this to decide whether we optimize the "match unit" case.
     See `isMatchUnit?`. -/
  isDep     : Bool
  alts      : Array MatchAltView

private partial def elabMatchTypeAndDiscrs (discrStxs : Array Syntax) (matchOptType : Syntax) (matchAltViews : Array MatchAltView) (expectedType : Expr)
      : TermElabM ElabMatchTypeAndDiscrsResult := do
    let numDiscrs := discrStxs.size
    if matchOptType.isNone then
      elabDiscrs 0 #[]
    else
      let matchTypeStx := matchOptType[0][1]
      let matchType ← elabType matchTypeStx
      let (discrs, isDep) ← elabDiscrsWitMatchType matchType expectedType
      return { discrs := discrs, matchType := matchType, isDep := isDep, alts := matchAltViews }
  where
    /- Easy case: elaborate discriminant when the match-type has been explicitly provided by the user.  -/
    elabDiscrsWitMatchType (matchType : Expr) (expectedType : Expr) : TermElabM (Array Expr × Bool) := do
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
          matchType ← b.instantiate1 discr
          discrs := discrs.push discr
        | _ =>
          throwError "invalid type provided to match-expression, function type with arity #{discrStxs.size} expected"
      return (discrs, isDep)

    markIsDep (r : ElabMatchTypeAndDiscrsResult) :=
      { r with isDep := true }

    /- Elaborate discriminants inferring the match-type -/
    elabDiscrs (i : Nat) (discrs : Array Expr) : TermElabM ElabMatchTypeAndDiscrsResult := do
      if h : i < discrStxs.size then
        let discrStx := discrStxs.get ⟨i, h⟩
        let discr     ← elabAtomicDiscr discrStx
        let discr     ← instantiateMVars discr
        let discrType ← inferType discr
        let discrType ← instantiateMVars discrType
        let discrs    := discrs.push discr
        let userName ← mkUserNameFor discr
        if discrStx[0].isNone then
          let mut result ← elabDiscrs (i + 1) discrs
          let matchTypeBody ← kabstract result.matchType discr
          if matchTypeBody.hasLooseBVars then
            result := markIsDep result
          return { result with matchType := Lean.mkForall userName BinderInfo.default discrType matchTypeBody }
        else
          let discrs := discrs.push (← mkEqRefl discr)
          let result ← elabDiscrs (i + 1) discrs
          let result := markIsDep result
          let identStx := discrStx[0][0]
          withLocalDeclD userName discrType fun x => do
            let eqType ← mkEq discr x
            withLocalDeclD identStx.getId eqType fun h => do
              let matchTypeBody ← kabstract result.matchType discr
              let matchTypeBody := matchTypeBody.instantiate1 x
              let matchType ← mkForallFVars #[x, h] matchTypeBody
              return { result with
                matchType := matchType
                alts      := result.alts.map fun altView => { altView with patterns := altView.patterns.insertAt (i+1) identStx }
              }
      else
        return { discrs, alts := matchAltViews, isDep := false, matchType := expectedType }

def expandMacrosInPatterns (matchAlts : Array MatchAltView) : MacroM (Array MatchAltView) := do
  matchAlts.mapM fun matchAlt => do
    let patterns ← matchAlt.patterns.mapM expandMacros
    pure { matchAlt with patterns := patterns }

private def getMatchGeneralizing? : Syntax → Option Bool
  | `(match (generalizing := true)  $discrs,* $[: $ty?]? with $alts:matchAlt*) => some true
  | `(match (generalizing := false) $discrs,* $[: $ty?]? with $alts:matchAlt*) => some false
  | _ => none

/- Given `stx` a match-expression, return its alternatives. -/
private def getMatchAlts : Syntax → Array MatchAltView
  | `(match $[$gen]? $discrs,* $[: $ty?]? with $alts:matchAlt*) =>
    alts.filterMap fun alt => match alt with
      | `(matchAltExpr| | $patterns,* => $rhs) => some {
          ref      := alt,
          patterns := patterns,
          rhs      := rhs
        }
      | _ => none
  | _ => #[]

builtin_initialize Parser.registerBuiltinNodeKind `MVarWithIdKind

open Meta.Match (mkInaccessible inaccessible?)

/--
  The elaboration function for `Syntax` created using `mkMVarSyntax`.
  It just converts the metavariable id wrapped by the Syntax into an `Expr`. -/
@[builtinTermElab MVarWithIdKind] def elabMVarWithIdKind : TermElab := fun stx expectedType? =>
  return mkInaccessible <| mkMVar (getMVarSyntaxMVarId stx)

@[builtinTermElab inaccessible] def elabInaccessible : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[1] expectedType?
  return mkInaccessible e

open Lean.Elab.Term.Quotation in
@[builtinQuotPrecheck Lean.Parser.Term.match] def precheckMatch : Precheck
  | `(match $[$discrs:term],* with $[| $[$patss],* => $rhss]*) => do
    discrs.forM precheck
    for (pats, rhs) in patss.zip rhss do
      let vars ←
        try
          getPatternsVars pats
        catch
          | _ => return  -- can happen in case of pattern antiquotations
      Quotation.withNewLocals (getPatternVarNames vars) <| precheck rhs
  | _ => throwUnsupportedSyntax

/- We convert the collected `PatternVar`s intro `PatternVarDecl` -/
inductive PatternVarDecl where
  /- For `anonymousVar`, we create both a metavariable and a free variable. The free variable is used as an assignment for the metavariable
     when it is not assigned during pattern elaboration. -/
  | anonymousVar (mvarId : MVarId) (fvarId : FVarId)
  | localVar     (fvarId : FVarId)

private partial def withPatternVars {α} (pVars : Array PatternVar) (k : Array PatternVarDecl → TermElabM α) : TermElabM α :=
  let rec loop (i : Nat) (decls : Array PatternVarDecl) := do
    if h : i < pVars.size then
      match pVars.get ⟨i, h⟩ with
      | PatternVar.anonymousVar mvarId =>
        let type ← mkFreshTypeMVar
        let userName ← mkFreshBinderName
        withLocalDecl userName BinderInfo.default type fun x =>
          loop (i+1) (decls.push (PatternVarDecl.anonymousVar mvarId x.fvarId!))
      | PatternVar.localVar userName   =>
        let type ← mkFreshTypeMVar
        withLocalDecl userName BinderInfo.default type fun x =>
          loop (i+1) (decls.push (PatternVarDecl.localVar x.fvarId!))
    else
      /- We must create the metavariables for `PatternVar.anonymousVar` AFTER we create the new local decls using `withLocalDecl`.
         Reason: their scope must include the new local decls since some of them are assigned by typing constraints. -/
      decls.forM fun decl => match decl with
        | PatternVarDecl.anonymousVar mvarId fvarId => do
          let type ← inferType (mkFVar fvarId)
          discard <| mkFreshExprMVarWithId mvarId type
        | _ => pure ()
      k decls
  loop 0 #[]

/-
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

/- Auxiliary structure for storing an type mismatch exception when processing the
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
    trace[Meta.debug] "type {t} =?= {d}"
    let t ← whnf t
    let d ← whnf d
    checkCompatibleApps t d
    matchConstInduct t.getAppFn (fun _ => failure) fun info _ => do
      let tArgs := t.getAppArgs
      let dArgs := d.getAppArgs
      for i in [:info.numParams] do
        let tArg := tArgs[i]
        let dArg := dArgs[i]
        unless (← isDefEq tArg dArg) do
          return i :: (← goType tArg dArg)
      for i in [info.numParams : tArgs.size] do
        let tArg := tArgs[i]
        let dArg := dArgs[i]
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
      trace[Meta.debug] "index {t} =?= {d}"
      checkCompatibleApps t d
      matchConstCtor t.getAppFn (fun _ => failure) fun info _ => do
        let tArgs := t.getAppArgs
        let dArgs := d.getAppArgs
        for i in [:info.numParams] do
          let tArg := tArgs[i]
          let dArg := dArgs[i]
          unless (← isDefEq tArg dArg) do
            failure
        for i in [info.numParams : tArgs.size] do
          let tArg := tArgs[i]
          let dArg := dArgs[i]
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

private def elabPatterns (patternStxs : Array Syntax) (matchType : Expr) : ExceptT PatternElabException TermElabM (Array Expr × Expr) :=
  withReader (fun ctx => { ctx with implicitLambda := false }) do
    let mut patterns  := #[]
    let mut matchType := matchType
    for idx in [:patternStxs.size] do
      let patternStx := patternStxs[idx]
      matchType ← whnf matchType
      match matchType with
      | Expr.forallE _ d b _ =>
        let pattern ← do
          let s ← saveState
          try
            liftM <| withSynthesize <| withoutErrToSorry <| elabTermEnsuringType patternStx d
          catch ex : Exception =>
            restoreState s
            match (← liftM <| commitIfNoErrors? <| withoutErrToSorry do elabTermAndSynthesize patternStx (← eraseIndices d)) with
            | some pattern =>
              match (← findDiscrRefinementPath pattern d |>.run) with
              | some path =>
                trace[Meta.debug] "refinement path: {path}"
                restoreState s
                -- Wrap the type mismatch exception for the "discriminant refinement" feature.
                throwThe PatternElabException { ex := ex, patternIdx := idx, pathToIndex := path }
              | none => restoreState s; throw ex
            | none => throw ex
        matchType := b.instantiate1 pattern
        patterns  := patterns.push pattern
      | _ => throwError "unexpected match type"
    return (patterns, matchType)

def finalizePatternDecls (patternVarDecls : Array PatternVarDecl) : TermElabM (Array LocalDecl) := do
  let mut decls := #[]
  for pdecl in patternVarDecls do
    match pdecl with
    | PatternVarDecl.localVar fvarId =>
      let decl ← getLocalDecl fvarId
      let decl ← instantiateLocalDeclMVars decl
      decls := decls.push decl
    | PatternVarDecl.anonymousVar mvarId fvarId =>
       let e ← instantiateMVars (mkMVar mvarId);
       trace[Elab.match] "finalizePatternDecls: mvarId: {mvarId.name} := {e}, fvar: {mkFVar fvarId}"
       match e with
       | Expr.mvar newMVarId _ =>
         /- Metavariable was not assigned, or assigned to another metavariable. So,
            we assign to the auxiliary free variable we created at `withPatternVars` to `newMVarId`. -/
         assignExprMVar newMVarId (mkFVar fvarId)
         trace[Elab.match] "finalizePatternDecls: {mkMVar newMVarId} := {mkFVar fvarId}"
         let decl ← getLocalDecl fvarId
         let decl ← instantiateLocalDeclMVars decl
         decls := decls.push decl
       | _ => pure ()
  /- We perform a topological sort (dependecies) on `decls` because the pattern elaboration process may produce a sequence where a declaration d₁ may occur after d₂ when d₂ depends on d₁. -/
  sortLocalDecls decls

open Meta.Match (Pattern Pattern.var Pattern.inaccessible Pattern.ctor Pattern.as Pattern.val Pattern.arrayLit AltLHS MatcherResult)

namespace ToDepElimPattern

structure State where
  found      : FVarIdSet := {}
  localDecls : Array LocalDecl
  newLocals  : FVarIdSet := {}

abbrev M := StateRefT State TermElabM

private def alreadyVisited (fvarId : FVarId) : M Bool := do
  let s ← get
  return s.found.contains fvarId

private def markAsVisited (fvarId : FVarId) : M Unit :=
  modify fun s => { s with found := s.found.insert fvarId }

private def throwInvalidPattern {α} (e : Expr) : M α :=
  throwError "invalid pattern {indentExpr e}"

/- Create a new LocalDecl `x` for the metavariable `mvar`, and return `Pattern.var x` -/
private def mkLocalDeclFor (mvar : Expr) : M Pattern := do
  let mvarId := mvar.mvarId!
  let s ← get
  match (← getExprMVarAssignment? mvarId) with
  | some val => return Pattern.inaccessible val
  | none =>
    let fvarId ← mkFreshFVarId
    let type   ← inferType mvar
    /- HACK: `fvarId` is not in the scope of `mvarId`
       If this generates problems in the future, we should update the metavariable declarations. -/
    assignExprMVar mvarId (mkFVar fvarId)
    let userName ← mkFreshBinderName
    let newDecl := LocalDecl.cdecl arbitrary fvarId userName type BinderInfo.default;
    modify fun s =>
      { s with
        newLocals  := s.newLocals.insert fvarId,
        localDecls :=
        match s.localDecls.findIdx? fun decl => mvar.occurs decl.type with
        | none   => s.localDecls.push newDecl -- None of the existing declarations depend on `mvar`
        | some i => s.localDecls.insertAt i newDecl }
    return Pattern.var fvarId

partial def main (e : Expr) : M Pattern := do
  let isLocalDecl (fvarId : FVarId) : M Bool := do
    return (← get).localDecls.any fun d => d.fvarId == fvarId
  let mkPatternVar (fvarId : FVarId) (e : Expr) : M Pattern := do
    if (← alreadyVisited fvarId) then
      return Pattern.inaccessible e
    else
      markAsVisited fvarId
      return Pattern.var e.fvarId!
  let mkInaccessible (e : Expr) : M Pattern := do
    match e with
    | Expr.fvar fvarId _ =>
      if (← isLocalDecl fvarId) then
        mkPatternVar fvarId e
      else
        return Pattern.inaccessible e
    | _ =>
      return Pattern.inaccessible e
  match inaccessible? e with
  | some t => mkInaccessible t
  | none =>
    match e.arrayLit? with
    | some (α, lits) =>
      return Pattern.arrayLit α (← lits.mapM main)
    | none =>
      if e.isAppOfArity `namedPattern 3 then
        let p ← main <| e.getArg! 2
        match e.getArg! 1 with
        | Expr.fvar fvarId _ => return Pattern.as fvarId p
        | _                  => throwError "unexpected occurrence of auxiliary declaration 'namedPattern'"
      else if isMatchValue e then
        return Pattern.val e
      else if e.isFVar then
        let fvarId := e.fvarId!
        unless (← isLocalDecl fvarId) do
          throwInvalidPattern e
        mkPatternVar fvarId e
      else if e.isMVar then
        mkLocalDeclFor e
      else
        let newE ← whnf e
        if newE != e then
          main newE
        else
         matchConstCtor e.getAppFn
           (fun _ => do
              if (← isProof e) then
                /- We mark nested proofs as inaccessible. This is fine due to proof irrelevance.
                   We need this feature to be able to elaborate definitions such as:
                   ```
                    def f : Fin 2 → Nat
                      | 0 => 5
                      | 1 => 45
                   ```
                -/
                return Pattern.inaccessible e
              else
                throwInvalidPattern e)
           (fun v us => do
              let args := e.getAppArgs
              unless args.size == v.numParams + v.numFields do
                throwInvalidPattern e
              let params := args.extract 0 v.numParams
              let fields := args.extract v.numParams args.size
              let fields ← fields.mapM main
              return Pattern.ctor v.name us params.toList fields.toList)

end ToDepElimPattern

def withDepElimPatterns {α} (localDecls : Array LocalDecl) (ps : Array Expr) (k : Array LocalDecl → Array Pattern → TermElabM α) : TermElabM α := do
  let (patterns, s) ← (ps.mapM ToDepElimPattern.main).run { localDecls := localDecls }
  let localDecls ← s.localDecls.mapM fun d => instantiateLocalDeclMVars d
  /- toDepElimPatterns may have added new localDecls. Thus, we must update the local context before we execute `k` -/
  let lctx ← getLCtx
  let lctx := localDecls.foldl (fun (lctx : LocalContext) d => lctx.erase d.fvarId) lctx
  let lctx := localDecls.foldl (fun (lctx : LocalContext) d => lctx.addDecl d) lctx
  withTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) do
    k localDecls patterns

private def withElaboratedLHS {α} (ref : Syntax) (patternVarDecls : Array PatternVarDecl) (patternStxs : Array Syntax) (matchType : Expr)
    (k : AltLHS → Expr → TermElabM α) : ExceptT PatternElabException TermElabM α := do
  let (patterns, matchType) ← withSynthesize <| elabPatterns patternStxs matchType
  id (α := TermElabM α) do
    let localDecls ← finalizePatternDecls patternVarDecls
    let patterns ← patterns.mapM (instantiateMVars ·)
    withDepElimPatterns localDecls patterns fun localDecls patterns =>
      k { ref := ref, fvarDecls := localDecls.toList, patterns := patterns.toList } matchType

private def elabMatchAltView (alt : MatchAltView) (matchType : Expr) : ExceptT PatternElabException TermElabM (AltLHS × Expr) := withRef alt.ref do
  let (patternVars, alt) ← collectPatternVars alt
  trace[Elab.match] "patternVars: {patternVars}"
  withPatternVars patternVars fun patternVarDecls => do
    withElaboratedLHS alt.ref patternVarDecls alt.patterns matchType fun altLHS matchType => do
      let rhs ← elabTermEnsuringType alt.rhs matchType
      let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr
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

/--
  "Generalize" variables that depend on the discriminants.

  Remarks and limitations:
  - If `matchType` is a proposition, then we generalize even when the user did not provide `(generalizing := true)`.
    Motivation: users should have control about the actual `match`-expressions in their programs.
  - We currently do not generalize let-decls.
  - We abort generalization if the new `matchType` is type incorrect.
  - Only discriminants that are free variables are considered during specialization.
  - We "generalize" by adding new discriminants and pattern variables. We do not "clear" the generalized variables,
    but they become inaccessible since they are shadowed by the patterns variables. We assume this is ok since
    this is the exact behavior users would get if they had written it by hand. Recall there is no `clear` in term mode.
-/
private def generalize (discrs : Array Expr) (matchType : Expr) (altViews : Array MatchAltView) (generalizing? : Option Bool) : TermElabM (Array Expr × Expr × Array MatchAltView × Bool) := do
  let gen ←
    match generalizing? with
    | some g => pure g
    | _ => isProp matchType
  if !gen then
    return (discrs, matchType, altViews, false)
  else
    let ysFVarIds ← getFVarsToGeneralize discrs
    /- let-decls are currently being ignored by the generalizer. -/
    let ysFVarIds ← ysFVarIds.filterM fun fvarId => return !(← getLocalDecl fvarId).isLet
    if ysFVarIds.isEmpty then
      return (discrs, matchType, altViews, false)
    else
      let ys := ysFVarIds.map mkFVar
      -- trace[Meta.debug] "ys: {ys}, discrs: {discrs}"
      let matchType' ← forallBoundedTelescope matchType discrs.size fun ds type => do
        let type ← mkForallFVars ys type
        let (discrs', ds') := Array.unzip <| Array.zip discrs ds |>.filter fun (di, d) => di.isFVar
        let type := type.replaceFVars discrs' ds'
        mkForallFVars ds type
      -- trace[Meta.debug] "matchType': {matchType'}"
      if (← isTypeCorrect matchType') then
        let discrs := discrs ++ ys
        let altViews ← altViews.mapM fun altView => do
          let patternVars ← getPatternsVars altView.patterns
          -- We traverse backwards because we want to keep the most recent names.
          -- For example, if `ys` contains `#[h, h]`, we want to make sure `mkFreshUsername is applied to the first `h`,
          -- since it is already shadowed by the second.
          let ysUserNames ← ys.foldrM (init := #[]) fun ys ysUserNames => do
            let yDecl ← getLocalDecl ys.fvarId!
            let mut yUserName := yDecl.userName
            if ysUserNames.contains yUserName then
              yUserName ← mkFreshUserName yUserName
            -- Explicitly provided pattern variables shadow `y`
            else if patternVars.any fun | PatternVar.localVar x => x == yUserName | _ => false then
              yUserName ← mkFreshUserName yUserName
            return ysUserNames.push yUserName
          let ysIds ← ysUserNames.reverse.mapM fun n => return mkIdentFrom (← getRef) n
          return { altView with patterns := altView.patterns ++ ysIds }
        return (discrs, matchType', altViews, true)
      else
        return (discrs, matchType, altViews, true)

private partial def elabMatchAltViews (generalizing? : Option Bool) (discrs : Array Expr) (matchType : Expr) (altViews : Array MatchAltView) : TermElabM (Array Expr × Expr × Array (AltLHS × Expr) × Bool) := do
  loop discrs matchType altViews none
where
  /-
    "Discriminant refinement" main loop.
    `first?` contains the first error message we found before updated the `discrs`. -/
  loop (discrs : Array Expr) (matchType : Expr) (altViews : Array MatchAltView) (first? : Option (SavedState × Exception))
      : TermElabM (Array Expr × Expr × Array (AltLHS × Expr) × Bool) := do
    let s ← saveState
    let (discrs', matchType', altViews', refined) ← generalize discrs matchType altViews generalizing?
    match (← altViews'.mapM (fun altView => elabMatchAltView altView matchType') |>.run) with
    | Except.ok alts => return (discrs', matchType', alts, first?.isSome || refined)
    | Except.error { patternIdx := patternIdx, pathToIndex := pathToIndex, ex := ex } =>
      trace[Meta.debug] "pathToIndex: {toString pathToIndex}"
      let some index ← getIndexToInclude? discrs[patternIdx] pathToIndex
        | throwEx (← updateFirst first? ex)
      trace[Meta.debug] "index: {index}"
      if (← discrs.anyM fun discr => isDefEq discr index) then
        throwEx (← updateFirst first? ex)
      let first ← updateFirst first? ex
      s.restore
      let indices ← collectDeps #[index] discrs
      let matchType ←
        try
          updateMatchType indices matchType
        catch ex =>
          throwEx first
      let altViews  ← addWildcardPatterns indices.size altViews
      let discrs    := indices ++ discrs
      loop discrs matchType altViews first

  throwEx {α} (p : SavedState × Exception) : TermElabM α := do
    p.1.restore; throw p.2

  updateFirst (first? : Option (SavedState × Exception)) (ex : Exception) : TermElabM (SavedState × Exception) := do
    match first? with
    | none       => return (← saveState, ex)
    | some first => return first

  containsFVar (es : Array Expr) (fvarId : FVarId) : Bool :=
    es.any fun e => e.isFVar && e.fvarId! == fvarId

  /- Update `indices` by including any free variable `x` s.t.
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
        let localDecl ← getLocalDecl fvarId
        let mctx ← getMCtx
        for indexFVarId in indicesFVar do
          if mctx.localDeclDependsOn localDecl indexFVarId then
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

  addWildcardPatterns (num : Nat) (altViews : Array MatchAltView) : TermElabM (Array MatchAltView) := do
    let hole := mkHole (← getRef)
    let wildcards := mkArray num hole
    return altViews.map fun altView => { altView with patterns := wildcards ++ altView.patterns }

def mkMatcher (input : Meta.Match.MkMatcherInput) : TermElabM MatcherResult :=
  Meta.Match.mkMatcher input

register_builtin_option match.ignoreUnusedAlts : Bool := {
  defValue := false
  descr := "if true, do not generate error if an alternative is not used"
}

def reportMatcherResultErrors (altLHSS : List AltLHS) (result : MatcherResult) : TermElabM Unit := do
  unless result.counterExamples.isEmpty do
    withHeadRefOnly <| logError m!"missing cases:\n{Meta.Match.counterExamplesToMessageData result.counterExamples}"
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
    match rhss[0] with
    | Expr.lam _ _ b _ => return if b.hasLooseBVars then none else b
    | _ => return none
  | _ => return none
private def elabMatchAux (generalizing? : Option Bool) (discrStxs : Array Syntax) (altViews : Array MatchAltView) (matchOptType : Syntax) (expectedType : Expr)
    : TermElabM Expr := do
  let mut generalizing? := generalizing?
  if !matchOptType.isNone then
    if generalizing? == some true then
      throwError "the '(generalizing := true)' parameter is not supported when the 'match' type is explicitly provided"
    generalizing? := some false
  let (discrs, matchType, altLHSS, isDep, rhss) ← commitIfDidNotPostpone do
    let ⟨discrs, matchType, isDep, altViews⟩ ← elabMatchTypeAndDiscrs discrStxs matchOptType altViews expectedType
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
     the type of `x` is only available after we proces the last argument of `List.forM`.

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
            withExistingLocalDecls altLHS.fvarDecls do
              tryPostpone
              throwMVarError m!"invalid match-expression, type of pattern variable '{d.toExpr}' contains metavariables{indentExpr d.type}"
        for p in altLHS.patterns do
          if p.hasExprMVar then
            withExistingLocalDecls altLHS.fvarDecls do
              tryPostpone
              throwMVarError m!"invalid match-expression, pattern contains metavariables{indentExpr (← p.toExpr)}"
        pure altLHS
    return (discrs, matchType, altLHSS, isDep, rhss)
  if let some r ← if isDep then pure none else isMatchUnit? altLHSS rhss then
    return r
  else
    let numDiscrs := discrs.size
    let matcherName ← mkAuxName `match
    let matcherResult ← mkMatcher { matcherName, matchType, numDiscrs, lhss := altLHSS }
    matcherResult.addMatcher
    let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
    reportMatcherResultErrors altLHSS matcherResult
    let r := mkApp matcherResult.matcher motive
    let r := mkAppN r discrs
    let r := mkAppN r rhss
    trace[Elab.match] "result: {r}"
    return r

private def getDiscrs (matchStx : Syntax) : Array Syntax :=
  matchStx[2].getSepArgs

private def getMatchOptType (matchStx : Syntax) : Syntax :=
  matchStx[3]

private def expandNonAtomicDiscrs? (matchStx : Syntax) : TermElabM (Option Syntax) :=
  let matchOptType := getMatchOptType matchStx;
  if matchOptType.isNone then do
    let discrs := getDiscrs matchStx;
    let allLocal ← discrs.allM fun discr => Option.isSome <$> isAtomicDiscr? discr[1]
    if allLocal then
      return none
    else
      -- We use `foundFVars` to make sure the discriminants are distinct variables.
      -- See: code for computing "matchType" at `elabMatchTypeAndDiscrs`
      let rec loop (discrs : List Syntax) (discrsNew : Array Syntax) (foundFVars : FVarIdSet) := do
        match discrs with
        | [] =>
          let discrs := Syntax.mkSep discrsNew (mkAtomFrom matchStx ", ");
          pure (matchStx.setArg 2 discrs)
        | discr :: discrs =>
          -- Recall that
          -- matchDiscr := leading_parser optional (ident >> ":") >> termParser
          let term := discr[1]
          let addAux : TermElabM Syntax := withFreshMacroScope do
            let d ← `(_discr);
            unless isAuxDiscrName d.getId do -- Use assertion?
              throwError "unexpected internal auxiliary discriminant name"
            let discrNew := discr.setArg 1 d;
            let r ← loop discrs (discrsNew.push discrNew) foundFVars
            `(let _discr := $term; $r)
          match (← isAtomicDiscr? term) with
          | some x  => if x.isFVar then loop discrs (discrsNew.push discr) (foundFVars.insert x.fvarId!) else addAux
          | none    => addAux
      return some (← loop discrs.toList #[] {})
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
  if getMatchOptType matchStx |>.isNone then
    let discrs := getDiscrs matchStx
    for discr in discrs do
      let term := discr[1]
      match (← isAtomicDiscr? term) with
      | none   => throwErrorAt discr "unexpected discriminant" -- see `expandNonAtomicDiscrs?
      | some d =>
        let dType ← inferType d
        trace[Elab.match] "discr {d} : {dType}"
        tryPostponeIfMVar dType

/-
We (try to) elaborate a `match` only when the expected type is available.
If the `matchType` has not been provided by the user, we also try to postpone elaboration if the type
of a discriminant is not available. That is, it is of the form `(?m ...)`.
We use `expandNonAtomicDiscrs?` to make sure all discriminants are local variables.
This is a standard trick we use in the elaborator, and it is also used to elaborate structure instances.
Suppose, we are trying to elaborate
```
match g x with
  | ... => ...
```
`expandNonAtomicDiscrs?` converts it intro
```
let _discr := g x
match _discr with
  | ... => ...
```
Thus, at `tryPostponeIfDiscrTypeIsMVar` we only need to check whether the type of `_discr` is not of the form `(?m ...)`.
Note that, the auxiliary variable `_discr` is expanded at `elabAtomicDiscr`.

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

/-
```
leading_parser:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
```
Remark the `optIdent` must be `none` at `matchDiscr`. They are expanded by `expandMatchDiscr?`.
-/
private def elabMatchCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let expectedType ← waitExpectedTypeAndDiscrs stx expectedType?
  let discrStxs := (getDiscrs stx).map fun d => d
  let gen?         := getMatchGeneralizing? stx
  let altViews     := getMatchAlts stx
  let matchOptType := getMatchOptType stx
  elabMatchAux gen? discrStxs altViews matchOptType expectedType

private def isPatternVar (stx : Syntax) : TermElabM Bool := do
  match (← resolveId? stx "pattern") with
  | none   => isAtomicIdent stx
  | some f => match f with
    | Expr.const fName _ _ =>
      match (← getEnv).find? fName with
      | some (ConstantInfo.ctorInfo _) => return false
      | some _                         => return !hasMatchPatternAttribute (← getEnv) fName
      | _                              => isAtomicIdent stx
    | _ => isAtomicIdent stx
where
  isAtomicIdent (stx : Syntax) : Bool :=
    stx.isIdent && stx.getId.eraseMacroScopes.isAtomic

-- leading_parser "match " >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermElab «match»] def elabMatch : TermElab := fun stx expectedType? => do
  match stx with
  | `(match $discr:term with | $y:ident => $rhs:term) =>
     if (← isPatternVar y) then expandSimpleMatch stx discr y rhs expectedType? else elabMatchDefault stx expectedType?
  | _ => elabMatchDefault stx expectedType?
where
  elabMatchDefault (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
    match (← expandNonAtomicDiscrs? stx) with
    | some stxNew => withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
    | none =>
      let discrs       := getDiscrs stx;
      let matchOptType := getMatchOptType stx;
      if !matchOptType.isNone && discrs.any fun d => !d[0].isNone then
        throwErrorAt matchOptType "match expected type should not be provided when discriminants with equality proofs are used"
      elabMatchCore stx expectedType?

builtin_initialize
  registerTraceClass `Elab.match

-- leading_parser:leadPrec "nomatch " >> termParser
@[builtinTermElab «nomatch»] def elabNoMatch : TermElab := fun stx expectedType? => do
  match stx with
  | `(nomatch $discrExpr) =>
    match (← isLocalIdent? discrExpr) with
    | some _ =>
      let expectedType ← waitExpectedType expectedType?
      let discr := Syntax.node ``Lean.Parser.Term.matchDiscr #[mkNullNode, discrExpr]
      elabMatchAux none #[discr] #[] mkNullNode expectedType
    | _ =>
      let stxNew ← `(let _discr := $discrExpr; nomatch _discr)
      withMacroExpansion stx stxNew <| elabTerm stxNew expectedType?
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
