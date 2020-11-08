/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatchPatternAttr
import Lean.Meta.Match.Match
import Lean.Elab.SyntheticMVars
import Lean.Elab.App

namespace Lean.Elab.Term
open Meta

/- This modules assumes "match"-expressions use the following syntax.

```lean
def matchAlt : Parser :=
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $
  sepBy1 termParser ", " >> darrow >> termParser

def matchAlts (optionalFirstBar := true) : Parser :=
group $ withPosition $ fun pos =>
  (if optionalFirstBar then optional "| " else "| ") >>
  sepBy1 matchAlt (checkColGe pos.column "alternatives must be indented" >> "|")

def matchDiscr := parser! optional (try (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> termParser

def «match» := parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
```
-/

structure MatchAltView :=
  (ref      : Syntax)
  (patterns : Array Syntax)
  (rhs      : Syntax)

def mkMatchAltView (ref : Syntax) (matchAlt : Syntax) : MatchAltView := {
  ref := ref,
  patterns := matchAlt[0].getSepArgs,
  rhs := matchAlt[2]
}

private def expandSimpleMatch (stx discr lhsVar rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let newStx ← `(let $lhsVar := $discr; $rhs)
  withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private def expandSimpleMatchWithType (stx discr lhsVar type rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let newStx ← `(let $lhsVar : $type := $discr; $rhs)
  withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private def elabDiscrsWitMatchType (discrStxs : Array Syntax) (matchType : Expr) (expectedType : Expr) : TermElabM (Array Expr) := do
  let discrs := #[]
  let i := 0
  let matchType := matchType
  for discrStx in discrStxs do
    i := i + 1
    matchType ← whnf matchType
    match matchType with
    | Expr.forallE _ d b _ =>
      let discr ← fullApproxDefEq $ elabTermEnsuringType discrStx[1] d
      trace[Elab.match]! "discr #{i} {discr} : {d}"
      matchType ← b.instantiate1 discr
      discrs := discrs.push discr
    | _ =>
      throwError! "invalid type provided to match-expression, function type with arity #{discrStxs.size} expected"
  pure discrs

private def mkUserNameFor (e : Expr) : TermElabM Name :=
  match e with
  | Expr.fvar fvarId _ => do pure (← getLocalDecl fvarId).userName
  | _                  => mkFreshBinderName

-- `expandNonAtomicDiscrs?` create auxiliary variables with base name `_discr`
private def isAuxDiscrName (n : Name) : Bool :=
  n.eraseMacroScopes == `_discr

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

private def elabMatchTypeAndDiscrs (discrStxs : Array Syntax) (matchOptType : Syntax) (matchAltViews : Array MatchAltView) (expectedType : Expr)
    : TermElabM (Array Expr × Expr × Array MatchAltView) := do
  let numDiscrs := discrStxs.size
  if matchOptType.isNone then
    let rec loop (i : Nat) (discrs : Array Expr) (matchType : Expr) (matchAltViews : Array MatchAltView) := do
      match i with
      | 0   => pure (discrs.reverse, matchType, matchAltViews)
      | i+1 =>
        let discrStx := discrStxs[i]
        let discr ← elabAtomicDiscr discrStx
        let discr ← instantiateMVars discr
        let discrType ← inferType discr
        let discrType ← instantiateMVars discrType
        let matchTypeBody ← kabstract matchType discr
        let userName ← mkUserNameFor discr
        if discrStx[0].isNone then
          loop i (discrs.push discr) (Lean.mkForall userName BinderInfo.default discrType matchTypeBody) matchAltViews
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
              loop i discrs matchType matchAltViews
    loop discrStxs.size #[] expectedType matchAltViews
  else
    let matchTypeStx := matchOptType[0][1]
    let matchType ← elabType matchTypeStx
    let discrs ← elabDiscrsWitMatchType discrStxs matchType expectedType
    pure (discrs, matchType, matchAltViews)

/-
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $ sepBy1 termParser ", " >> darrow >> termParser
-/
def expandMacrosInPatterns (matchAlts : Array MatchAltView) : MacroM (Array MatchAltView) := do
  matchAlts.mapM fun matchAlt => do
    let patterns ← matchAlt.patterns.mapM expandMacros
    pure { matchAlt with patterns := patterns }

  /- Given `stx` a match-expression, return its alternatives. -/
  private def getMatchAlts (stx : Syntax) : Array MatchAltView := do
  let matchAlts  := stx[4]
  let firstVBar  := matchAlts[0]
  let ref        := firstVBar
  let result     := #[]
  for arg in matchAlts[1].getArgs do
    if ref.isNone then ref := arg -- The first vertical bar is optional
    if arg.getKind == `Lean.Parser.Term.matchAlt then
      result := result.push (mkMatchAltView ref arg)
    else
      ref := arg -- current `arg` is a vertical bar
  pure result

/--
  Auxiliary annotation used to mark terms marked with the "inaccessible" annotation `.(t)` and
  `_` in patterns. -/
def mkInaccessible (e : Expr) : Expr :=
  mkAnnotation `_inaccessible e

def inaccessible? (e : Expr) : Option Expr :=
  annotation? `_inaccessible e

inductive PatternVar
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
  pure $ Syntax.node `MVarWithIdKind #[Syntax.node mvarId #[]]

/-- Given a syntax node constructed using `mkMVarSyntax`, return its MVarId -/
private def getMVarSyntaxMVarId (stx : Syntax) : MVarId :=
  stx[0].getKind

/--
  The elaboration function for `Syntax` created using `mkMVarSyntax`.
  It just converts the metavariable id wrapped by the Syntax into an `Expr`. -/
@[builtinTermElab MVarWithIdKind] def elabMVarWithIdKind : TermElab := fun stx expectedType? =>
  pure $ mkInaccessible $ mkMVar (getMVarSyntaxMVarId stx)

@[builtinTermElab inaccessible] def elabInaccessible : TermElab := fun stx expectedType? => do
  let e ← elabTerm stx[1] expectedType?
  pure $ mkInaccessible e

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

structure State :=
  (found     : NameSet := {})
  (vars      : Array PatternVar := #[])

abbrev M := StateRefT State TermElabM

private def throwCtorExpected {α} : M α :=
  throwError "invalid pattern, constructor or constant marked with '[matchPattern]' expected"

private def getNumExplicitCtorParams (ctorVal : ConstructorVal) : TermElabM Nat :=
  forallBoundedTelescope ctorVal.type ctorVal.nparams fun ps _ => do
    let result := 0
    for p in ps do
      let localDecl ← getLocalDecl p.fvarId!
      if localDecl.binderInfo.isExplicit then
        result := result+1
    pure result

private def throwAmbiguous {α} (fs : List Expr) : M α :=
  throwError! "ambiguous pattern, use fully qualified name, possible interpretations {fs}"

def resolveId? (stx : Syntax) : M (Option Expr) :=
  match stx with
  | Syntax.ident _ _ val preresolved => do
    let rs ← try resolveName val preresolved [] catch _ => pure []
    let rs := rs.filter fun ⟨f, projs⟩ => projs.isEmpty
    let fs := rs.map fun (f, _) => f
    match fs with
    | []  => pure none
    | [f] => pure (some f)
    | _   => throwAmbiguous fs
  | _ => throwError "identifier expected"

private def throwInvalidPattern {α} : M α :=
  throwError "invalid pattern"

namespace CtorApp

/-
An application in a pattern can be

1- A constructor application
   The elaborator assumes fields are accessible and inductive parameters are not accessible.

2- A regular application `(f ...)` where `f` is tagged with `[matchPattern]`.
   The elaborator assumes implicit arguments are not accessible and explicit ones are accessible.
-/

structure Context :=
  (funId         : Syntax)
  (ctorVal?      : Option ConstructorVal) -- It is `some`, if constructor application
  (explicit      : Bool)
  (ellipsis      : Bool)
  (paramDecls    : Array LocalDecl)
  (paramDeclIdx  : Nat := 0)
  (namedArgs     : Array NamedArg)
  (args          : List Arg)
  (newArgs       : Array Syntax := #[])

instance : Inhabited Context := ⟨⟨arbitrary _, none, false, false, #[], 0, #[], [], #[]⟩⟩

private def isDone (ctx : Context) : Bool :=
  ctx.paramDeclIdx ≥ ctx.paramDecls.size

private def finalize (ctx : Context) : M Syntax := do
  if ctx.namedArgs.isEmpty && ctx.args.isEmpty then
    let fStx ← `(@$(ctx.funId):ident)
    pure $ mkAppStx fStx ctx.newArgs
  else
    throwError "too many arguments"

private def isNextArgAccessible (ctx : Context) : Bool :=
  let i := ctx.paramDeclIdx
  match ctx.ctorVal? with
  | some ctorVal => i ≥ ctorVal.nparams -- For constructor applications only fields are accessible
  | none =>
    if h : i < ctx.paramDecls.size then
      -- For `[matchPattern]` applications, only explicit parameters are accessible.
      let d := ctx.paramDecls.get ⟨i, h⟩
      d.binderInfo.isExplicit
    else
      false

private def getNextParam (ctx : Context) : LocalDecl × Context :=
  let i := ctx.paramDeclIdx
  let d := ctx.paramDecls[i]
  (d, { ctx with paramDeclIdx := ctx.paramDeclIdx + 1 })

private def pushNewArg (collect : Syntax → M Syntax) (accessible : Bool) (ctx : Context) (arg : Arg) : M Context :=
  match arg with
  | Arg.stx stx => do
    let stx ← if accessible then collect stx else pure stx
    pure { ctx with newArgs := ctx.newArgs.push stx }
  | _           => unreachable!

private def processExplicitArg (collect : Syntax → M Syntax) (accessible : Bool) (ctx : Context) : M Context :=
  match ctx.args with
  | [] =>
    if ctx.ellipsis then do
      let hole ← `(_)
      pushNewArg collect accessible ctx (Arg.stx hole)
    else
      throwError! "explicit parameter is missing, unused named arguments {ctx.namedArgs.map fun narg => narg.name}"
  | arg::args => do
    let ctx := { ctx with args := args }
    pushNewArg collect accessible ctx arg

private def processImplicitArg (collect : Syntax → M Syntax) (accessible : Bool) (ctx : Context) : M Context :=
  if ctx.explicit then
    processExplicitArg collect accessible ctx
  else do
    let hole ← `(_)
    pushNewArg collect accessible ctx (Arg.stx hole)

private partial def processCtorAppAux (collect : Syntax → M Syntax) (ctx : Context) : M Syntax := do
  if isDone ctx then
    finalize ctx
  else
    let accessible := isNextArgAccessible ctx
    let (d, ctx)   := getNextParam ctx
    match ctx.namedArgs.findIdx? fun namedArg => namedArg.name == d.userName with
    | some idx =>
      let arg := ctx.namedArgs[idx]
      let ctx := { ctx with namedArgs := ctx.namedArgs.eraseIdx idx }
      let ctx ← pushNewArg collect accessible ctx arg.val
      processCtorAppAux collect ctx
    | none =>
      let ctx ← match d.binderInfo with
        | BinderInfo.implicit     => processImplicitArg collect accessible ctx
        | BinderInfo.instImplicit => processImplicitArg collect accessible ctx
        | _                       => processExplicitArg collect accessible ctx
      processCtorAppAux collect ctx

def processCtorApp (collect : Syntax → M Syntax) (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) : M Syntax := do
  let args := args.toList
  let (fId, explicit) ← match_syntax f with
    | `($fId:ident)  => pure (fId, false)
    | `(@$fId:ident) => pure (fId, true)
    | _              => throwError "identifier expected"
  let some (Expr.const fName _ _) ← resolveId? fId | throwCtorExpected
  let fInfo ← getConstInfo fName
  forallTelescopeReducing fInfo.type fun xs _ => do
    let paramDecls ← xs.mapM getFVarLocalDecl
    match fInfo with
    | ConstantInfo.ctorInfo val =>
      processCtorAppAux collect
        { funId := fId, explicit := explicit, ctorVal? := val, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
    | _ =>
      let env ← getEnv
      if hasMatchPatternAttribute env fName then
        processCtorAppAux collect
          { funId := fId, explicit := explicit, ctorVal? := none, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
      else
        throwCtorExpected

end CtorApp

def processCtorApp (collect : Syntax → M Syntax) (stx : Syntax) : M Syntax := do
  let (f, namedArgs, args, ellipsis) ← liftM $ expandApp stx true
  CtorApp.processCtorApp collect f namedArgs args ellipsis

def processCtor (collect : Syntax → M Syntax) (stx : Syntax) : M Syntax := do
  CtorApp.processCtorApp collect stx #[] #[] false

private def processVar (idStx : Syntax) : M Syntax := do
  unless idStx.isIdent do
    throwErrorAt idStx "identifier expected"
  let id := idStx.getId
  unless id.eraseMacroScopes.isAtomic do throwError "invalid pattern variable, must be atomic"
  let s ← get
  if s.found.contains id then throwError! "invalid pattern, variable '{id}' occurred more than once"
  modify fun s => { s with vars := s.vars.push (PatternVar.localVar id), found := s.found.insert id }
  pure idStx

/- Check whether `stx` is a pattern variable or constructor-like (i.e., constructor or constant tagged with `[matchPattern]` attribute) -/
private def processId (collect : Syntax → M Syntax) (stx : Syntax) : M Syntax := do
  let env ← getEnv
  match (← resolveId? stx) with
  | none   => processVar stx
  | some f => match f with
    | Expr.const fName _ _ =>
      match env.find? fName with
      | some (ConstantInfo.ctorInfo _) => processCtor collect stx
      | some _ =>
        if hasMatchPatternAttribute env fName then
          processCtor collect stx
        else
          processVar stx
      | none => throwCtorExpected
    | _ => processVar stx

private def nameToPattern : Name → TermElabM Syntax
  | Name.anonymous => `(Name.anonymous)
  | Name.str p s _ => do let p ← nameToPattern p; `(Name.str $p $(quote s) _)
  | Name.num p n _ => do let p ← nameToPattern p; `(Name.num $p $(quote n) _)

private def quotedNameToPattern (stx : Syntax) : TermElabM Syntax :=
  match stx[0].isNameLit? with
  | some val => nameToPattern val
  | none     => throwIllFormedSyntax

partial def collect : Syntax → M Syntax
  | stx@(Syntax.node k args) => withRef stx $ withFreshMacroScope do
    if k == `Lean.Parser.Term.app then
      processCtorApp collect stx
    else if k == `Lean.Parser.Term.anonymousCtor then
      let elems ← args[1].getArgs.mapSepElemsM collect
      pure $ Syntax.node k (args.set! 1 $ mkNullNode elems)
    else if k == `Lean.Parser.Term.structInst then
      /- { " >> optional (try (termParser >> " with ")) >> sepBy structInstField ", " true >> optional ".." >> optional (" : " >> termParser) >> " }" -/
      let withMod := args[1]
      unless withMod.isNone do
        throwErrorAt withMod "invalid struct instance pattern, 'with' is not allowed in patterns"
      let fields := args[2].getArgs
      let fields ← fields.mapSepElemsM fun field => do
        -- parser! structInstLVal >> " := " >> termParser
        let newVal ← collect field[3] -- `structInstLVal` has arity 2
        pure $ field.setArg 3 newVal
      pure $ Syntax.node k (args.set! 2 $ mkNullNode fields)
    else if k == `Lean.Parser.Term.hole then
      let r ← mkMVarSyntax
      modify fun s => { s with vars := s.vars.push $ PatternVar.anonymousVar $ getMVarSyntaxMVarId r }
      pure r
    else if k == `Lean.Parser.Term.paren then
      let arg := args[1]
      if arg.isNone then
        pure stx -- `()`
      else
        let t := arg[0]
        let s := arg[1]
        if s.isNone || s[0].getKind == `Lean.Parser.Term.typeAscription then
          -- Ignore `s`, since it empty or it is a type ascription
          let t ← collect t
          let arg := arg.setArg 0 t
          pure $ Syntax.node k (args.set! 1 arg)
        else
          -- Tuple literal is a constructor
          let t ← collect t
          let arg := arg.setArg 0 t
          let tupleTail := s[0]
          let tupleTailElems := tupleTail[1].getArgs
          let tupleTailElems ← tupleTailElems.mapSepElemsM collect
          let tupleTail := tupleTail.setArg 1 $ mkNullNode tupleTailElems
          let s         := s.setArg 0 tupleTail
          let arg       := arg.setArg 1 s
          pure $ Syntax.node k (args.set! 1 arg)
    else if k == `Lean.Parser.Term.explicitUniv then
      processCtor collect stx[0]
    else if k == `Lean.Parser.Term.namedPattern then
      /- Recall that
         def namedPattern := check... >> tparser! "@" >> termParser -/
      let id := stx[0]
      processVar id
      let pat := stx[2]
      pat ← collect pat
      `(namedPattern $id $pat)
    else if k == `Lean.Parser.Term.inaccessible then
      pure stx
    else if k == strLitKind then
      pure stx
    else if k == numLitKind then
      pure stx
    else if k == charLitKind then
      pure stx
    else if k == `Lean.Parser.Term.quotedName then
      /- Quoted names have an elaboration function associated with them, and they will not be macro expanded.
         Note that macro expansion is not a good option since it produces a term using the smart constructors `mkNameStr`, `mkNameNum`
         instead of the constructors `Name.str` and `Name.num` -/
      quotedNameToPattern stx
    else if k == choiceKind then
      throwError "invalid pattern, notation is ambiguous"
    else
      throwInvalidPattern
  | stx@(Syntax.ident _ _ _ _) =>
    processId collect stx
  | stx =>
    throwInvalidPattern

def main (alt : MatchAltView) : M MatchAltView := do
  let patterns ← alt.patterns.mapM fun p => do
    trace[Elab.match]! "collecting variables at pattern: {p}"
    collect p
  pure { alt with patterns := patterns }

end CollectPatternVars

private def collectPatternVars (alt : MatchAltView) : TermElabM (Array PatternVar × MatchAltView) := do
  let (alt, s) ← (CollectPatternVars.main alt).run {}
  pure (s.vars, alt)

/- Return the pattern variables in the given pattern.
  Remark: this method is not used here, but in other macros (e.g., at `Do.lean`). -/
def getPatternVars (patternStx : Syntax) : TermElabM (Array PatternVar) := do
  let patternStx ← liftMacroM $ expandMacros patternStx
  let (_, s) ← (CollectPatternVars.collect patternStx).run {}
  pure s.vars

def getPatternsVars (patterns : Array Syntax) : TermElabM (Array PatternVar) := do
  let collect : CollectPatternVars.M Unit := do
    for pattern in patterns do
      CollectPatternVars.collect (← liftMacroM $ expandMacros pattern)
      pure ()
  let (_, s) ← collect.run {}
  pure s.vars

/- We convert the collected `PatternVar`s intro `PatternVarDecl` -/
inductive PatternVarDecl
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
          mkFreshExprMVarWithId mvarId type
          pure ()
        | _ => pure ()
      k decls
  loop 0 #[]

private def elabPatterns (patternStxs : Array Syntax) (matchType : Expr) : TermElabM (Array Expr × Expr) := do
  let patterns  := #[]
  let matchType := matchType
  for patternStx in patternStxs do
    matchType ← whnf matchType
    match matchType with
    | Expr.forallE _ d b _ =>
      let pattern ← elabTermEnsuringType patternStx d
      matchType := b.instantiate1 pattern
      patterns  := patterns.push pattern
    | _ => throwError "unexpected match type"
  pure (patterns, matchType)

def finalizePatternDecls (patternVarDecls : Array PatternVarDecl) : TermElabM (Array LocalDecl) := do
  let decls := #[]
  for pdecl in patternVarDecls do
    match pdecl with
    | PatternVarDecl.localVar fvarId =>
      let decl ← getLocalDecl fvarId
      let decl ← instantiateLocalDeclMVars decl
      decls := decls.push decl
    | PatternVarDecl.anonymousVar mvarId fvarId =>
       let e ← instantiateMVars (mkMVar mvarId);
       trace[Elab.match]! "finalizePatternDecls: mvarId: {mvarId} := {e}, fvar: {mkFVar fvarId}"
       match e with
       | Expr.mvar newMVarId _ =>
         /- Metavariable was not assigned, or assigned to another metavariable. So,
            we assign to the auxiliary free variable we created at `withPatternVars` to `newMVarId`. -/
         assignExprMVar newMVarId (mkFVar fvarId)
         trace[Elab.match]! "finalizePatternDecls: {mkMVar newMVarId} := {mkFVar fvarId}"
         let decl ← getLocalDecl fvarId
         let decl ← instantiateLocalDeclMVars decl
         decls := decls.push decl
       | _ => pure ()
  pure decls

open Meta.Match (Pattern Pattern.var Pattern.inaccessible Pattern.ctor Pattern.as Pattern.val Pattern.arrayLit AltLHS MatcherResult)

namespace ToDepElimPattern

structure State :=
  (found      : NameSet := {})
  (localDecls : Array LocalDecl)
  (newLocals  : NameSet := {})

abbrev M := StateRefT State TermElabM

private def alreadyVisited (fvarId : FVarId) : M Bool := do
  let s ← get
  pure $ s.found.contains fvarId

private def markAsVisited (fvarId : FVarId) : M Unit :=
  modify fun s => { s with found := s.found.insert fvarId }

private def throwInvalidPattern {α} (e : Expr) : M α :=
  throwError! "invalid pattern {indentExpr e}"

/- Create a new LocalDecl `x` for the metavariable `mvar`, and return `Pattern.var x` -/
private def mkLocalDeclFor (mvar : Expr) : M Pattern := do
  let mvarId := mvar.mvarId!
  let s ← get
  match (← getExprMVarAssignment? mvarId) with
  | some val => pure $ Pattern.inaccessible val
  | none =>
    let fvarId ← mkFreshId
    let type   ← inferType mvar
    /- HACK: `fvarId` is not in the scope of `mvarId`
       If this generates problems in the future, we should update the metavariable declarations. -/
    assignExprMVar mvarId (mkFVar fvarId)
    let userName ← liftM $ mkFreshBinderName
    let newDecl := LocalDecl.cdecl (arbitrary _) fvarId userName type BinderInfo.default;
    modify fun s =>
      { s with
        newLocals  := s.newLocals.insert fvarId,
        localDecls :=
        match s.localDecls.findIdx? fun decl => mvar.occurs decl.type with
        | none   => s.localDecls.push newDecl -- None of the existing declarations depend on `mvar`
        | some i => s.localDecls.insertAt i newDecl }
    pure $ Pattern.var fvarId

partial def main (e : Expr) : M Pattern := do
  let isLocalDecl (fvarId : FVarId) : M Bool := do
    let s ← get
    pure $ s.localDecls.any fun d => d.fvarId == fvarId
  let mkPatternVar (fvarId : FVarId) (e : Expr) : M Pattern := do
    if (← alreadyVisited fvarId) then
      pure $ Pattern.inaccessible e
    else
      markAsVisited fvarId
      pure $ Pattern.var e.fvarId!
  let mkInaccessible (e : Expr) : M Pattern := do
    match e with
    | Expr.fvar fvarId _ =>
      if (← isLocalDecl fvarId) then
        mkPatternVar fvarId e
      else
        pure $ Pattern.inaccessible e
    | _ =>
      pure $ Pattern.inaccessible e
  match inaccessible? e with
  | some t => mkInaccessible t
  | none   =>
  match e.arrayLit? with
  | some (α, lits) =>
    let ps ← lits.mapM main;
    pure $ Pattern.arrayLit α ps
  | none =>
  if e.isAppOfArity `namedPattern 3 then
    let p ← main $ e.getArg! 2;
    match e.getArg! 1 with
    | Expr.fvar fvarId _ => pure $ Pattern.as fvarId p
    | _                  => throwError "unexpected occurrence of auxiliary declaration 'namedPattern'"
  else if e.isNatLit || e.isStringLit || e.isCharLit then
    pure $ Pattern.val e
  else if e.isFVar then
    let fvarId := e.fvarId!
    unless(← isLocalDecl fvarId) do throwInvalidPattern e
    mkPatternVar fvarId e
  else if e.isMVar then
    mkLocalDeclFor e
  else
    let newE ← whnf e
    if newE != e then
      main newE
    else matchConstCtor e.getAppFn (fun _ => throwInvalidPattern e) fun v us => do
      let args := e.getAppArgs
      unless args.size == v.nparams + v.nfields do
        throwInvalidPattern e
      let params := args.extract 0 v.nparams
      let fields := args.extract v.nparams args.size
      let fields ← fields.mapM main
      pure $ Pattern.ctor v.name us params.toList fields.toList

end ToDepElimPattern

def withDepElimPatterns {α} (localDecls : Array LocalDecl) (ps : Array Expr) (k : Array LocalDecl → Array Pattern → TermElabM α) : TermElabM α := do
  let (patterns, s) ← (ps.mapM ToDepElimPattern.main).run { localDecls := localDecls }
  let localDecls ← s.localDecls.mapM fun d => instantiateLocalDeclMVars d
  /- toDepElimPatterns may have added new localDecls. Thus, we must update the local context before we execute `k` -/
  let lctx ← getLCtx
  let lctx := localDecls.foldl (fun (lctx : LocalContext) d => lctx.erase d.fvarId) lctx
  let lctx := localDecls.foldl (fun (lctx : LocalContext) d => lctx.addDecl d) lctx
  withTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) $ k localDecls patterns

private def withElaboratedLHS {α} (ref : Syntax) (patternVarDecls : Array PatternVarDecl) (patternStxs : Array Syntax) (matchType : Expr)
    (k : AltLHS → Expr → TermElabM α) : TermElabM α := do
  let (patterns, matchType) ← withSynthesize $ elabPatterns patternStxs matchType
  let localDecls ← finalizePatternDecls patternVarDecls
  let patterns ← patterns.mapM instantiateMVars
  withDepElimPatterns localDecls patterns fun localDecls patterns =>
    k { ref := ref, fvarDecls := localDecls.toList, patterns := patterns.toList } matchType

def elabMatchAltView (alt : MatchAltView) (matchType : Expr) : TermElabM (AltLHS × Expr) := withRef alt.ref do
  let (patternVars, alt) ← collectPatternVars alt
  trace[Elab.match]! "patternVars: {patternVars}"
  withPatternVars patternVars fun patternVarDecls => do
    withElaboratedLHS alt.ref patternVarDecls alt.patterns matchType fun altLHS matchType => do
      let rhs ← elabTermEnsuringType alt.rhs matchType
      let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr
      let rhs ← if xs.isEmpty then pure $ mkSimpleThunk rhs else mkLambdaFVars xs rhs
      trace[Elab.match]! "rhs: {rhs}"
      pure (altLHS, rhs)

def mkMatcher (elimName : Name) (matchType : Expr) (numDiscrs : Nat) (lhss : List AltLHS) : TermElabM MatcherResult :=
  liftMetaM $ Meta.Match.mkMatcher elimName matchType numDiscrs lhss

def reportMatcherResultErrors (result : MatcherResult) : TermElabM Unit := do
  -- TODO: improve error messages
  unless result.counterExamples.isEmpty do
    throwError! "missing cases:\n{Meta.Match.counterExamplesToMessageData result.counterExamples}"
  unless result.unusedAltIdxs.isEmpty do
    throwError! "unused alternatives: {result.unusedAltIdxs.map fun idx => s!"#{idx+1}"}"

private def elabMatchAux (discrStxs : Array Syntax) (altViews : Array MatchAltView) (matchOptType : Syntax) (expectedType : Expr)
    : TermElabM Expr := do
  let (discrs, matchType, altViews) ← elabMatchTypeAndDiscrs discrStxs matchOptType altViews expectedType
  let matchAlts ← liftMacroM $ expandMacrosInPatterns altViews
  trace[Elab.match]! "matchType: {matchType}"
  let alts ← matchAlts.mapM $ fun alt => elabMatchAltView alt matchType
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
   the type of `x` is only available adfer we proces the last argument of `List.forM`.
  -/
  synthesizeSyntheticMVars
  /-
   We apply pending default types to make sure we can process examples such as
   ```
   let (a, b) := (0, 0)
   ```
  -/
  synthesizeUsingDefault
  -- TODO report error if matchType or altLHSS.toList have metavars
  let rhss := alts.map Prod.snd
  let altLHSS := alts.map Prod.fst
  let numDiscrs := discrs.size
  let matcherName ← mkAuxName `match
  let matcherResult ← mkMatcher matcherName matchType numDiscrs altLHSS.toList
  let motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType
  reportMatcherResultErrors matcherResult
  let r := mkApp matcherResult.matcher motive
  let r := mkAppN r discrs
  let r := mkAppN r rhss
  trace[Elab.match]! "result: {r}"
  pure r

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
      pure none
    else
      let rec loop (discrs : List Syntax) (discrsNew : Array Syntax) := do
        match discrs with
        | [] =>
          let discrs := mkSepStx discrsNew (mkAtomFrom matchStx ", ");
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
      pure (some (← loop discrs.toList #[]))
  else
    -- We do not pull non atomic discriminants when match type is provided explicitly by the user
    pure none

private def waitExpectedType (expectedType? : Option Expr) : TermElabM Expr := do
  tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
    | some expectedType => pure expectedType
    | none              => mkFreshTypeMVar

private def tryPostponeIfDiscrTypeIsMVar (matchStx : Syntax) : TermElabM Unit := do
  -- We don't wait for the discriminants types when match type is provided by user
  if getMatchOptType matchStx $.isNone then
    let discrs := getDiscrs matchStx
    for discr in discrs do
      let term := discr[1]
      match (← isLocalIdent? term) with
      | none   => throwErrorAt discr "unexpected discriminant" -- see `expandNonAtomicDiscrs?
      | some d =>
        let dType ← inferType d
        trace[Elab.match]! "discr {d} : {dType}"
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
  | some expectedType => pure expectedType
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

-- parser! "match " >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermElab «match»] def elabMatch : TermElab := fun stx expectedType? =>
  match_syntax stx with
  | `(match $discr:term with $y:ident => $rhs:term)           => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term with | $y:ident => $rhs:term)         => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term : $type with $y:ident => $rhs:term)   => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | `(match $discr:term : $type with | $y:ident => $rhs:term) => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | _ => do
    match (← expandNonAtomicDiscrs? stx) with
    | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
    | none =>
      let discrs       := getDiscrs stx;
      let matchOptType := getMatchOptType stx;
      if !matchOptType.isNone && discrs.any fun d => !d[0].isNone then
        throwErrorAt matchOptType "match expected type should not be provided when discriminants with equality proofs are used"
      elabMatchCore stx expectedType?

@[builtinInit] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.match;
pure ()

-- parser!:leadPrec "nomatch " >> termParser
@[builtinTermElab «nomatch»] def elabNoMatch : TermElab := fun stx expectedType? =>
  match_syntax stx with
  | `(nomatch $discrExpr) => do
      let expectedType ← waitExpectedType expectedType?
      let discr := Syntax.node `Lean.Parser.Term.matchDiscr #[mkNullNode, discrExpr]
      elabMatchAux #[discr] #[] mkNullNode expectedType
  | _ => throwUnsupportedSyntax

end Term
end Elab
end Lean
