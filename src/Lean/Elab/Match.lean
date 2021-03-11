/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatchPatternAttr
import Lean.Meta.Match.Match
import Lean.Elab.SyntheticMVars
import Lean.Elab.App
import Lean.Parser.Term

namespace Lean.Elab.Term
open Meta
open Lean.Parser.Term

/- This modules assumes "match"-expressions use the following syntax.

```lean
def matchDiscr := parser! optional (try (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> termParser

def «match» := parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
```
-/

structure MatchAltView where
  ref      : Syntax
  patterns : Array Syntax
  rhs      : Syntax
  deriving Inhabited

private def expandSimpleMatch (stx discr lhsVar rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let newStx ← `(let $lhsVar := $discr; $rhs)
  withMacroExpansion stx newStx <| elabTerm newStx expectedType?

private def expandSimpleMatchWithType (stx discr lhsVar type rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let newStx ← `(let $lhsVar : $type := $discr; $rhs)
  withMacroExpansion stx newStx <| elabTerm newStx expectedType?

private def elabDiscrsWitMatchType (discrStxs : Array Syntax) (matchType : Expr) (expectedType : Expr) : TermElabM (Array Expr × Bool) := do
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
      throwError! "invalid type provided to match-expression, function type with arity #{discrStxs.size} expected"
  pure (discrs, isDep)

private def mkUserNameFor (e : Expr) : TermElabM Name :=
  match e with
  | Expr.fvar fvarId _ => do pure (← getLocalDecl fvarId).userName
  | _                  => mkFreshBinderName

/-- Return true iff `n` is an auxiliary variable created by `expandNonAtomicDiscrs?` -/
def isAuxDiscrName (n : Name) : Bool :=
  n.hasMacroScopes && n.eraseMacroScopes == `_discr

-- See expandNonAtomicDiscrs?
private def elabAtomicDiscr (discr : Syntax) : TermElabM Expr := do
  let term := discr[1]
  match (← isLocalIdent? term) with
  | some e@(Expr.fvar fvarId _) =>
    let localDecl ← getLocalDecl fvarId
    if !isAuxDiscrName localDecl.userName then
      pure e -- it is not an auxiliary local created by `expandNonAtomicDiscrs?`
    else
      pure localDecl.value
  | _ => throwErrorAt discr "unexpected discriminant"

structure ElabMatchTypeAndDiscsResult where
  discrs    : Array Expr
  matchType : Expr
  isDep     : Bool
  alts      : Array MatchAltView

private def elabMatchTypeAndDiscrs (discrStxs : Array Syntax) (matchOptType : Syntax) (matchAltViews : Array MatchAltView) (expectedType : Expr)
    : TermElabM ElabMatchTypeAndDiscsResult := do
  let numDiscrs := discrStxs.size
  if matchOptType.isNone then
    let rec loop (i : Nat) (discrs : Array Expr) (matchType : Expr) (isDep : Bool) (matchAltViews : Array MatchAltView) := do
      match i with
      | 0   => return { discrs := discrs.reverse, matchType := matchType, isDep := isDep, alts := matchAltViews }
      | i+1 =>
        let discrStx := discrStxs[i]
        let discr ← elabAtomicDiscr discrStx
        let discr ← instantiateMVars discr
        let discrType ← inferType discr
        let discrType ← instantiateMVars discrType
        let matchTypeBody ← kabstract matchType discr
        let isDep := isDep || matchTypeBody.hasLooseBVars
        let userName ← mkUserNameFor discr
        if discrStx[0].isNone then
          loop i (discrs.push discr) (Lean.mkForall userName BinderInfo.default discrType matchTypeBody) isDep matchAltViews
        else
          let identStx := discrStx[0][0]
          withLocalDeclD userName discrType fun x => do
            let eqType ← mkEq discr x
            withLocalDeclD identStx.getId eqType fun h => do
              let matchTypeBody := matchTypeBody.instantiate1 x
              let matchType ← mkForallFVars #[x, h] matchTypeBody
              let refl ← mkEqRefl discr
              let discrs := (discrs.push refl).push discr
              let matchAltViews := matchAltViews.map fun altView =>
                { altView with patterns := altView.patterns.insertAt (i+1) identStx }
              loop i discrs matchType isDep matchAltViews
    loop discrStxs.size (discrs := #[]) (isDep := false) expectedType matchAltViews
  else
    let matchTypeStx := matchOptType[0][1]
    let matchType ← elabType matchTypeStx
    let (discrs, isDep) ← elabDiscrsWitMatchType discrStxs matchType expectedType
    return { discrs := discrs, matchType := matchType, isDep := isDep, alts := matchAltViews }

def expandMacrosInPatterns (matchAlts : Array MatchAltView) : MacroM (Array MatchAltView) := do
  matchAlts.mapM fun matchAlt => do
    let patterns ← matchAlt.patterns.mapM expandMacros
    pure { matchAlt with patterns := patterns }

/- Given `stx` a match-expression, return its alternatives. -/
private def getMatchAlts : Syntax → Array MatchAltView
  | `(match $discrs,* $[: $ty?]? with $alts:matchAlt*) =>
    alts.map fun alt => match alt with
      | `(matchAltExpr| | $patterns,* => $rhs) => {
          ref      := alt,
          patterns := patterns,
          rhs      := rhs
        }
      | _ => unreachable!
  | _ => unreachable!

/--
  Auxiliary annotation used to mark terms marked with the "inaccessible" annotation `.(t)` and
  `_` in patterns. -/
def mkInaccessible (e : Expr) : Expr :=
  mkAnnotation `_inaccessible e

def inaccessible? (e : Expr) : Option Expr :=
  annotation? `_inaccessible e

inductive PatternVar where
  | localVar     (userName : Name)
  -- anonymous variables (`_`) are encoded using metavariables
  | anonymousVar (mvarId   : MVarId)

instance : ToString PatternVar := ⟨fun
  | PatternVar.localVar x          => toString x
  | PatternVar.anonymousVar mvarId => s!"?m{mvarId}"⟩

builtin_initialize Parser.registerBuiltinNodeKind `MVarWithIdKind

/--
  Create an auxiliary Syntax node wrapping a fresh metavariable id.
  We use this kind of Syntax for representing `_` occurring in patterns.
  The metavariables are created before we elaborate the patterns into `Expr`s. -/
private def mkMVarSyntax : TermElabM Syntax := do
  let mvarId ← mkFreshId
  return Syntax.node `MVarWithIdKind #[Syntax.node mvarId #[]]

/-- Given a syntax node constructed using `mkMVarSyntax`, return its MVarId -/
private def getMVarSyntaxMVarId (stx : Syntax) : MVarId :=
  stx[0].getKind

/--
  The elaboration function for `Syntax` created using `mkMVarSyntax`.
  It just converts the metavariable id wrapped by the Syntax into an `Expr`. -/
@[builtinTermElab MVarWithIdKind] def elabMVarWithIdKind : TermElab := fun stx expectedType? =>
  return mkInaccessible <| mkMVar (getMVarSyntaxMVarId stx)

@[builtinTermElab inaccessible] def elabInaccessible : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[1] expectedType?
  return mkInaccessible e

/-
  Patterns define new local variables.
  This module collect them and preprocess `_` occurring in patterns.
  Recall that an `_` may represent anonymous variables or inaccessible terms
  that are implied by typing constraints. Thus, we represent them with fresh named holes `?x`.
  After we elaborate the pattern, if the metavariable remains unassigned, we transform it into
  a regular pattern variable. Otherwise, it becomes an inaccessible term.

  Macros occurring in patterns are expanded before the `collectPatternVars` method is executed.
  The following kinds of Syntax are handled by this module
  - Constructor applications
  - Applications of functions tagged with the `[matchPattern]` attribute
  - Identifiers
  - Anonymous constructors
  - Structure instances
  - Inaccessible terms
  - Named patterns
  - Tuple literals
  - Type ascriptions
  - Literals: num, string and char
-/
namespace CollectPatternVars

structure State where
  found     : NameSet := {}
  vars      : Array PatternVar := #[]

abbrev M := StateRefT State TermElabM

private def throwCtorExpected {α} : M α :=
  throwError "invalid pattern, constructor or constant marked with '[matchPattern]' expected"

private def getNumExplicitCtorParams (ctorVal : ConstructorVal) : TermElabM Nat :=
  forallBoundedTelescope ctorVal.type ctorVal.numParams fun ps _ => do
    let mut result := 0
    for p in ps do
      let localDecl ← getLocalDecl p.fvarId!
      if localDecl.binderInfo.isExplicit then
        result := result+1
    pure result

private def throwInvalidPattern {α} : M α :=
  throwError "invalid pattern"

/-
An application in a pattern can be

1- A constructor application
   The elaborator assumes fields are accessible and inductive parameters are not accessible.

2- A regular application `(f ...)` where `f` is tagged with `[matchPattern]`.
   The elaborator assumes implicit arguments are not accessible and explicit ones are accessible.
-/

structure Context where
  funId         : Syntax
  ctorVal?      : Option ConstructorVal -- It is `some`, if constructor application
  explicit      : Bool
  ellipsis      : Bool
  paramDecls    : Array (Name × BinderInfo) -- parameters names and binder information
  paramDeclIdx  : Nat := 0
  namedArgs     : Array NamedArg
  args          : List Arg
  newArgs       : Array Syntax := #[]
  deriving Inhabited

private def isDone (ctx : Context) : Bool :=
  ctx.paramDeclIdx ≥ ctx.paramDecls.size

private def finalize (ctx : Context) : M Syntax := do
  if ctx.namedArgs.isEmpty && ctx.args.isEmpty then
    let fStx ← `(@$(ctx.funId):ident)
    return Syntax.mkApp fStx ctx.newArgs
  else
    throwError "too many arguments"

private def isNextArgAccessible (ctx : Context) : Bool :=
  let i := ctx.paramDeclIdx
  match ctx.ctorVal? with
  | some ctorVal => i ≥ ctorVal.numParams -- For constructor applications only fields are accessible
  | none =>
    if h : i < ctx.paramDecls.size then
      -- For `[matchPattern]` applications, only explicit parameters are accessible.
      let d := ctx.paramDecls.get ⟨i, h⟩
      d.2.isExplicit
    else
      false

private def getNextParam (ctx : Context) : (Name × BinderInfo) × Context :=
  let i := ctx.paramDeclIdx
  let d := ctx.paramDecls[i]
  (d, { ctx with paramDeclIdx := ctx.paramDeclIdx + 1 })

private def processVar (idStx : Syntax) : M Syntax := do
  unless idStx.isIdent do
    throwErrorAt idStx "identifier expected"
  let id := idStx.getId
  unless id.eraseMacroScopes.isAtomic do
    throwError "invalid pattern variable, must be atomic"
  if (← get).found.contains id then
    throwError! "invalid pattern, variable '{id}' occurred more than once"
  modify fun s => { s with vars := s.vars.push (PatternVar.localVar id), found := s.found.insert id }
  return idStx

private def nameToPattern : Name → TermElabM Syntax
  | Name.anonymous => `(Name.anonymous)
  | Name.str p s _ => do let p ← nameToPattern p; `(Name.str $p $(quote s) _)
  | Name.num p n _ => do let p ← nameToPattern p; `(Name.num $p $(quote n) _)

private def quotedNameToPattern (stx : Syntax) : TermElabM Syntax :=
  match stx[0].isNameLit? with
  | some val => nameToPattern val
  | none     => throwIllFormedSyntax

partial def collect (stx : Syntax) : M Syntax := do
  match stx with
  | Syntax.node k args => withRef stx <| withFreshMacroScope do
    if k == `Lean.Parser.Term.app then
      processCtorApp stx
    else if k == `Lean.Parser.Term.anonymousCtor then
      let elems ← args[1].getArgs.mapSepElemsM collect
      return Syntax.node k (args.set! 1 <| mkNullNode elems)
    else if k == `Lean.Parser.Term.structInst then
      /-
      ```
      parser! "{" >> optional (atomic (termParser >> " with "))
                  >> manyIndent (group (structInstField >> optional ", "))
                  >> optional ".."
                  >> optional (" : " >> termParser)
                  >> " }"
      ```
      -/
      let withMod := args[1]
      unless withMod.isNone do
        throwErrorAt withMod "invalid struct instance pattern, 'with' is not allowed in patterns"
      let fields ← args[2].getArgs.mapM fun p => do
          -- p is of the form (group (structInstField >> optional ", "))
          let field := p[0]
          -- parser! structInstLVal >> " := " >> termParser
          let newVal ← collect field[2]
          let field := field.setArg 2 newVal
          pure <| field.setArg 0 field
      return Syntax.node k (args.set! 2 <| mkNullNode fields)
    else if k == `Lean.Parser.Term.hole then
      let r ← mkMVarSyntax
      modify fun s => { s with vars := s.vars.push <| PatternVar.anonymousVar <| getMVarSyntaxMVarId r }
      return r
    else if k == `Lean.Parser.Term.paren then
      let arg := args[1]
      if arg.isNone then
        return stx -- `()`
      else
        let t := arg[0]
        let s := arg[1]
        if s.isNone || s[0].getKind == `Lean.Parser.Term.typeAscription then
          -- Ignore `s`, since it empty or it is a type ascription
          let t ← collect t
          let arg := arg.setArg 0 t
          return Syntax.node k (args.set! 1 arg)
        else
          -- Tuple literal is a constructor
          let t ← collect t
          let arg := arg.setArg 0 t
          let tupleTail := s[0]
          let tupleTailElems := tupleTail[1].getArgs
          let tupleTailElems ← tupleTailElems.mapSepElemsM collect
          let tupleTail := tupleTail.setArg 1 <| mkNullNode tupleTailElems
          let s         := s.setArg 0 tupleTail
          let arg       := arg.setArg 1 s
          return Syntax.node k (args.set! 1 arg)
    else if k == `Lean.Parser.Term.explicitUniv then
      processCtor stx[0]
    else if k == `Lean.Parser.Term.namedPattern then
      /- Recall that
        def namedPattern := check... >> tparser! "@" >> termParser -/
      let id := stx[0]
      discard <| processVar id
      let pat := stx[2]
      let pat ← collect pat
      `(_root_.namedPattern $id $pat)
    else if k == `Lean.Parser.Term.inaccessible then
      return stx
    else if k == strLitKind then
      return stx
    else if k == numLitKind then
      return stx
    else if k == scientificLitKind then
      return stx
    else if k == charLitKind then
      return stx
    else if k == `Lean.Parser.Term.quotedName then
      /- Quoted names have an elaboration function associated with them, and they will not be macro expanded.
        Note that macro expansion is not a good option since it produces a term using the smart constructors `Name.mkStr`, `Name.mkNum`
        instead of the constructors `Name.str` and `Name.num` -/
      quotedNameToPattern stx
    else if k == choiceKind then
      throwError "invalid pattern, notation is ambiguous"
    else
      throwInvalidPattern
  | Syntax.ident .. =>
    processId stx
  | stx =>
    throwInvalidPattern
where

  processCtorApp (stx : Syntax) : M Syntax := do
    let (f, namedArgs, args, ellipsis) ← expandApp stx true
    processCtorAppCore f namedArgs args ellipsis

  processCtor (stx : Syntax) : M Syntax := do
    processCtorAppCore stx #[] #[] false

  /- Check whether `stx` is a pattern variable or constructor-like (i.e., constructor or constant tagged with `[matchPattern]` attribute) -/
  processId (stx : Syntax) : M Syntax := do
    match (← resolveId? stx "pattern") with
    | none   => processVar stx
    | some f => match f with
      | Expr.const fName _ _ =>
        match (← getEnv).find? fName with
        | some (ConstantInfo.ctorInfo _) => processCtor stx
        | some _ =>
          if hasMatchPatternAttribute (← getEnv) fName then
            processCtor stx
          else
            processVar stx
        | none => throwCtorExpected
      | _ => processVar stx

  pushNewArg (accessible : Bool) (ctx : Context) (arg : Arg) : M Context := do
    match arg with
    | Arg.stx stx =>
      let stx ← if accessible then collect stx else pure stx
      return { ctx with newArgs := ctx.newArgs.push stx }
    | _ => unreachable!

  processExplicitArg (accessible : Bool) (ctx : Context) : M Context := do
    match ctx.args with
    | [] =>
      if ctx.ellipsis then
        pushNewArg accessible ctx (Arg.stx (← `(_)))
      else
        throwError! "explicit parameter is missing, unused named arguments {ctx.namedArgs.map fun narg => narg.name}"
    | arg::args =>
      pushNewArg accessible { ctx with args := args } arg

  processImplicitArg (accessible : Bool) (ctx : Context) : M Context := do
    if ctx.explicit then
      processExplicitArg accessible ctx
    else
      pushNewArg accessible ctx (Arg.stx (← `(_)))

  processCtorAppContext (ctx : Context) : M Syntax := do
    if isDone ctx then
      finalize ctx
    else
      let accessible := isNextArgAccessible ctx
      let (d, ctx)   := getNextParam ctx
      match ctx.namedArgs.findIdx? fun namedArg => namedArg.name == d.1 with
      | some idx =>
        let arg := ctx.namedArgs[idx]
        let ctx := { ctx with namedArgs := ctx.namedArgs.eraseIdx idx }
        let ctx ← pushNewArg accessible ctx arg.val
        processCtorAppContext ctx
      | none =>
        let ctx ← match d.2 with
          | BinderInfo.implicit     => processImplicitArg accessible ctx
          | BinderInfo.instImplicit => processImplicitArg accessible ctx
          | _                       => processExplicitArg accessible ctx
        processCtorAppContext ctx

  processCtorAppCore (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) : M Syntax := do
    let args := args.toList
    let (fId, explicit) ← match f with
      | `($fId:ident)  => pure (fId, false)
      | `(@$fId:ident) => pure (fId, true)
      | _              => throwError "identifier expected"
    let some (Expr.const fName _ _) ← resolveId? fId "pattern" | throwCtorExpected
    let fInfo ← getConstInfo fName
    let paramDecls ← forallTelescopeReducing fInfo.type fun xs _ => xs.mapM fun x => do
      let d ← getFVarLocalDecl x
      return (d.userName, d.binderInfo)
    match fInfo with
    | ConstantInfo.ctorInfo val =>
      processCtorAppContext
        { funId := fId, explicit := explicit, ctorVal? := val, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
    | _ =>
      if hasMatchPatternAttribute (← getEnv) fName then
        processCtorAppContext
          { funId := fId, explicit := explicit, ctorVal? := none, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
      else
        throwCtorExpected

def main (alt : MatchAltView) : M MatchAltView := do
  let patterns ← alt.patterns.mapM fun p => do
    trace[Elab.match] "collecting variables at pattern: {p}"
    collect p
  return { alt with patterns := patterns }

end CollectPatternVars

private def collectPatternVars (alt : MatchAltView) : TermElabM (Array PatternVar × MatchAltView) := do
  let (alt, s) ← (CollectPatternVars.main alt).run {}
  return (s.vars, alt)

/- Return the pattern variables in the given pattern.
  Remark: this method is not used here, but in other macros (e.g., at `Do.lean`). -/
def getPatternVars (patternStx : Syntax) : TermElabM (Array PatternVar) := do
  let patternStx ← liftMacroM <| expandMacros patternStx
  let (_, s) ← (CollectPatternVars.collect patternStx).run {}
  return s.vars

def getPatternsVars (patterns : Array Syntax) : TermElabM (Array PatternVar) := do
  let collect : CollectPatternVars.M Unit := do
    for pattern in patterns do
      discard <| CollectPatternVars.collect (← liftMacroM <| expandMacros pattern)
  let (_, s) ← collect.run {}
  return s.vars

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

private def elabPatterns (patternStxs : Array Syntax) (matchType : Expr) : TermElabM (Array Expr × Expr) :=
  withReader (fun ctx => { ctx with implicitLambda := false }) do
    let mut patterns  := #[]
    let mut matchType := matchType
    for patternStx in patternStxs do
      matchType ← whnf matchType
      match matchType with
      | Expr.forallE _ d b _ =>
        let pattern ← elabTermEnsuringType patternStx d
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
       trace[Elab.match] "finalizePatternDecls: mvarId: {mvarId} := {e}, fvar: {mkFVar fvarId}"
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
  return decls

open Meta.Match (Pattern Pattern.var Pattern.inaccessible Pattern.ctor Pattern.as Pattern.val Pattern.arrayLit AltLHS MatcherResult)

namespace ToDepElimPattern

structure State where
  found      : NameSet := {}
  localDecls : Array LocalDecl
  newLocals  : NameSet := {}

abbrev M := StateRefT State TermElabM

private def alreadyVisited (fvarId : FVarId) : M Bool := do
  let s ← get
  return s.found.contains fvarId

private def markAsVisited (fvarId : FVarId) : M Unit :=
  modify fun s => { s with found := s.found.insert fvarId }

private def throwInvalidPattern {α} (e : Expr) : M α :=
  throwError! "invalid pattern {indentExpr e}"

/- Create a new LocalDecl `x` for the metavariable `mvar`, and return `Pattern.var x` -/
private def mkLocalDeclFor (mvar : Expr) : M Pattern := do
  let mvarId := mvar.mvarId!
  let s ← get
  match (← getExprMVarAssignment? mvarId) with
  | some val => return Pattern.inaccessible val
  | none =>
    let fvarId ← mkFreshId
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
      else if e.isNatLit || e.isStringLit || e.isCharLit then
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
        else matchConstCtor e.getAppFn (fun _ => throwInvalidPattern e) fun v us => do
          let args := e.getAppArgs
          unless args.size == v.numParams + v.numFields do
            throwInvalidPattern e
          let params := args.extract 0 v.numParams
          let fields := args.extract v.numParams args.size
          let fields ← fields.mapM main
          return Pattern.ctor v.name us params.toList fields.toList

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
    (k : AltLHS → Expr → TermElabM α) : TermElabM α := do
  let (patterns, matchType) ← withSynthesize <| elabPatterns patternStxs matchType
  let localDecls ← finalizePatternDecls patternVarDecls
  let patterns ← patterns.mapM (instantiateMVars ·)
  withDepElimPatterns localDecls patterns fun localDecls patterns =>
    k { ref := ref, fvarDecls := localDecls.toList, patterns := patterns.toList } matchType

def elabMatchAltView (alt : MatchAltView) (matchType : Expr) : TermElabM (AltLHS × Expr) := withRef alt.ref do
  let (patternVars, alt) ← collectPatternVars alt
  trace[Elab.match] "patternVars: {patternVars}"
  withPatternVars patternVars fun patternVarDecls => do
    withElaboratedLHS alt.ref patternVarDecls alt.patterns matchType fun altLHS matchType => do
      let rhs ← elabTermEnsuringType alt.rhs matchType
      let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr
      let rhs ← if xs.isEmpty then pure <| mkSimpleThunk rhs else mkLambdaFVars xs rhs
      trace[Elab.match] "rhs: {rhs}"
      return (altLHS, rhs)

def mkMatcher (elimName : Name) (matchType : Expr) (numDiscrs : Nat) (lhss : List AltLHS) : TermElabM MatcherResult :=
  Meta.Match.mkMatcher elimName matchType numDiscrs lhss

register_builtin_option match.ignoreUnusedAlts : Bool := {
  defValue := false
  descr := "if true, do not generate error if an alternative is not used"
}

def reportMatcherResultErrors (altLHSS : List AltLHS) (result : MatcherResult) : TermElabM Unit := do
  unless result.counterExamples.isEmpty do
    withHeadRefOnly <| throwError! "missing cases:\n{Meta.Match.counterExamplesToMessageData result.counterExamples}"
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

private def elabMatchAux (discrStxs : Array Syntax) (altViews : Array MatchAltView) (matchOptType : Syntax) (expectedType : Expr)
    : TermElabM Expr := do
  let (discrs, matchType, altLHSS, isDep, rhss) ← commitIfDidNotPostpone do
    let ⟨discrs, matchType, isDep, altViews⟩ ← elabMatchTypeAndDiscrs discrStxs matchOptType altViews expectedType
    let matchAlts ← liftMacroM <| expandMacrosInPatterns altViews
    trace[Elab.match] "matchType: {matchType}"
    let alts ← matchAlts.mapM fun alt => elabMatchAltView alt matchType
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
    let matcherResult ← mkMatcher matcherName matchType numDiscrs altLHSS
    let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
    reportMatcherResultErrors altLHSS matcherResult
    let r := mkApp matcherResult.matcher motive
    let r := mkAppN r discrs
    let r := mkAppN r rhss
    trace[Elab.match] "result: {r}"
    return r

private def getDiscrs (matchStx : Syntax) : Array Syntax :=
  matchStx[1].getSepArgs

private def getMatchOptType (matchStx : Syntax) : Syntax :=
  matchStx[2]

private def expandNonAtomicDiscrs? (matchStx : Syntax) : TermElabM (Option Syntax) :=
  let matchOptType := getMatchOptType matchStx;
  if matchOptType.isNone then do
    let discrs := getDiscrs matchStx;
    let allLocal ← discrs.allM fun discr => Option.isSome <$> isLocalIdent? discr[1]
    if allLocal then
      return none
    else
      let rec loop (discrs : List Syntax) (discrsNew : Array Syntax) := do
        match discrs with
        | [] =>
          let discrs := Syntax.mkSep discrsNew (mkAtomFrom matchStx ", ");
          pure (matchStx.setArg 1 discrs)
        | discr :: discrs =>
          -- Recall that
          -- matchDiscr := parser! optional (ident >> ":") >> termParser
          let term := discr[1]
          match (← isLocalIdent? term) with
          | some _ => loop discrs (discrsNew.push discr)
          | none   => withFreshMacroScope do
            let d ← `(_discr);
            unless isAuxDiscrName d.getId do -- Use assertion?
              throwError "unexpected internal auxiliary discriminant name"
            let discrNew := discr.setArg 1 d;
            let r ← loop discrs (discrsNew.push discrNew)
            `(let _discr := $term; $r)
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
  if getMatchOptType matchStx |>.isNone then
    let discrs := getDiscrs matchStx
    for discr in discrs do
      let term := discr[1]
      match (← isLocalIdent? term) with
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
parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
```
Remark the `optIdent` must be `none` at `matchDiscr`. They are expanded by `expandMatchDiscr?`.
-/
private def elabMatchCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let expectedType ← waitExpectedTypeAndDiscrs stx expectedType?
  let discrStxs := (getDiscrs stx).map fun d => d
  let altViews     := getMatchAlts stx
  let matchOptType := getMatchOptType stx
  elabMatchAux discrStxs altViews matchOptType expectedType

private def isPatternVar (stx : Syntax) : TermElabM Bool := do
  match (← resolveId? stx "pattern") with
  | none   => isAtomicIdent stx
  | some f => match f with
    | Expr.const fName _ _ =>
      match (← getEnv).find? fName with
      | some (ConstantInfo.ctorInfo _) => return false
      | _ => isAtomicIdent stx
    | _ => isAtomicIdent stx
where
  isAtomicIdent (stx : Syntax) : Bool :=
    stx.isIdent && stx.getId.eraseMacroScopes.isAtomic

-- parser! "match " >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermElab «match»] def elabMatch : TermElab := fun stx expectedType? => do
  match stx with
  | `(match $discr:term with | $y:ident => $rhs:term) =>
     if (← isPatternVar y) then expandSimpleMatch stx discr y rhs expectedType? else elabMatchDefault stx expectedType?
  | `(match $discr:term : $type with | $y:ident => $rhs:term) =>
     if (← isPatternVar y) then expandSimpleMatchWithType stx discr y type rhs expectedType? else elabMatchDefault stx expectedType?
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

-- parser!:leadPrec "nomatch " >> termParser
@[builtinTermElab «nomatch»] def elabNoMatch : TermElab := fun stx expectedType? =>
  match stx with
  | `(nomatch $discrExpr) => do
      let expectedType ← waitExpectedType expectedType?
      let discr := Syntax.node `Lean.Parser.Term.matchDiscr #[mkNullNode, discrExpr]
      elabMatchAux #[discr] #[] mkNullNode expectedType
  | _ => throwUnsupportedSyntax

end Lean.Elab.Term
