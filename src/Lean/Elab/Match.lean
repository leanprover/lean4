/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatchPatternAttr
import Lean.Meta.Match.Match
import Lean.Elab.SyntheticMVars
import Lean.Elab.App

namespace Lean
namespace Elab
namespace Term

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

def mkMatchAltView (ref : Syntax) (matchAlt : Syntax) : MatchAltView :=
{ ref := ref, patterns := (matchAlt.getArg 0).getArgs.getSepElems, rhs := matchAlt.getArg 2 }

private def expandSimpleMatch (stx discr lhsVar rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
newStx ← `(let $lhsVar := $discr; $rhs);
withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private def expandSimpleMatchWithType (stx discr lhsVar type rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
newStx ← `(let $lhsVar : $type := $discr; $rhs);
withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private partial def elabDiscrsWitMatchTypeAux (discrStxs : Array Syntax) (expectedType : Expr) : Nat → Expr → Array Expr → TermElabM (Array Expr)
| i, matchType, discrs =>
  if h : i < discrStxs.size then do
    let discrStx := (discrStxs.get ⟨i, h⟩).getArg 1;
    matchType ← whnf matchType;
    match matchType with
    | Expr.forallE _ d b _ => do
      discr ← fullApproxDefEq $ elabTermEnsuringType discrStx d;
      trace `Elab.match fun _ => "discr #" ++ toString i ++ " " ++ discr ++ " : " ++ d;
      elabDiscrsWitMatchTypeAux (i+1) (b.instantiate1 discr) (discrs.push discr)
    | _ => throwError ("invalid type provided to match-expression, function type with arity #" ++ toString discrStxs ++ " expected")
  else do
    unlessM (fullApproxDefEq $ isDefEq matchType expectedType) $
      throwError ("invalid result type provided to match-expression" ++ indentExpr matchType ++ Format.line ++ "expected type" ++ indentExpr expectedType);
    pure discrs

private def elabDiscrsWitMatchType (discrStxs : Array Syntax) (matchType : Expr) (expectedType : Expr) : TermElabM (Array Expr) :=
elabDiscrsWitMatchTypeAux discrStxs expectedType 0 matchType #[]

private def mkUserNameFor (e : Expr) : TermElabM Name :=
match e with
| Expr.fvar fvarId _ => do localDecl ← getLocalDecl fvarId; pure localDecl.userName
| _ => mkFreshBinderName

-- `expandNonAtomicDiscrs?` create auxiliary variables with base name `_discr`
private def isAuxDiscrName (n : Name) : Bool :=
n.eraseMacroScopes == `_discr

-- See expandNonAtomicDiscrs?
private def elabAtomicDiscr (discr : Syntax) : TermElabM Expr := do
let term := discr.getArg 1;
local? ← isLocalIdent? term;
match local? with
| some e@(Expr.fvar fvarId _) => do
  localDecl ← getLocalDecl fvarId;
  if !isAuxDiscrName localDecl.userName then
    pure e -- it is not an auxiliary local created by `expandNonAtomicDiscrs?`
  else
    pure localDecl.value
| _ => throwErrorAt discr "unexpected discriminant"

private def elabMatchTypeAndDiscrsAux (discrStxs : Array Syntax) : Nat → Array Expr → Expr → Array MatchAltView → TermElabM (Array Expr × Expr × Array MatchAltView)
| 0,   discrs, matchType, matchAltViews => pure (discrs.reverse, matchType, matchAltViews)
| i+1, discrs, matchType, matchAltViews => do
  let discrStx := discrStxs.get! i;
  discr ← elabAtomicDiscr discrStx;
  discr ← instantiateMVars discr;
  discrType ← inferType discr;
  discrType ← instantiateMVars discrType;
  matchTypeBody ← kabstract matchType discr;
  userName ← mkUserNameFor discr;
  if (discrStx.getArg 0).isNone then do
    elabMatchTypeAndDiscrsAux i (discrs.push discr) (Lean.mkForall userName BinderInfo.default discrType matchTypeBody) matchAltViews
  else
    let identStx := (discrStx.getArg 0).getArg 0;
    withLocalDeclD userName discrType fun x => do
    eqType ← mkEq discr x;
    withLocalDeclD identStx.getId eqType fun h => do
    let matchTypeBody := matchTypeBody.instantiate1 x;
    matchType ← mkForallFVars #[x, h] matchTypeBody;
    refl ← mkEqRefl discr;
    let discrs := (discrs.push refl).push discr;
    let matchAltViews := matchAltViews.map fun altView =>
      { altView with patterns := altView.patterns.insertAt (i+1) identStx };
    elabMatchTypeAndDiscrsAux i discrs matchType matchAltViews

private def elabMatchTypeAndDiscrs (discrStxs : Array Syntax) (matchOptType : Syntax) (matchAltViews : Array MatchAltView) (expectedType : Expr)
    : TermElabM (Array Expr × Expr × Array MatchAltView) :=
let numDiscrs := discrStxs.size;
if matchOptType.isNone then do
  elabMatchTypeAndDiscrsAux discrStxs discrStxs.size #[] expectedType matchAltViews
else do
  let matchTypeStx := (matchOptType.getArg 0).getArg 1;
  matchType ← elabType matchTypeStx;
  discrs ← elabDiscrsWitMatchType discrStxs matchType expectedType;
  pure (discrs, matchType, matchAltViews)

/-
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $ sepBy1 termParser ", " >> darrow >> termParser
-/
def expandMacrosInPatterns (matchAlts : Array MatchAltView) : MacroM (Array MatchAltView) := do
matchAlts.mapM fun matchAlt => do
  patterns ← matchAlt.patterns.mapM $ expandMacros;
  pure $ { matchAlt with patterns := patterns }

private partial def getMatchAltsAux (args : Array Syntax) : Nat → Syntax → Array MatchAltView → Array MatchAltView
| i, ref, result =>
  if h : i < args.size then
    let arg := args.get ⟨i, h⟩;
    let ref := if ref.isNone then arg else ref; -- The first vertical is optional
    if arg.getKind == `Lean.Parser.Term.matchAlt then
      getMatchAltsAux (i+1) ref (result.push (mkMatchAltView ref arg))
    else
      -- current `arg` is the vertical bar delimiter
      getMatchAltsAux (i+1) arg result
  else
    result

/- Given `stx` a match-expression, return its alternatives. -/
private def getMatchAlts (stx : Syntax) : Array MatchAltView :=
let matchAlts  := stx.getArg 4;
let firstVBar  := matchAlts.getArg 0;
getMatchAltsAux (matchAlts.getArg 1).getArgs 0 firstVBar #[]

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

instance PatternVar.hasToString : HasToString PatternVar :=
⟨fun v => match v with
  | PatternVar.localVar x          => toString x
  | PatternVar.anonymousVar mvarId => "?m" ++ toString mvarId⟩

@[init] private def registerAuxiliaryNodeKind : IO Unit :=
Parser.registerBuiltinNodeKind `MVarWithIdKind

/--
  Create an auxiliary Syntax node wrapping a fresh metavariable id.
  We use this kind of Syntax for representing `_` occurring in patterns.
  The metavariables are created before we elaborate the patterns into `Expr`s. -/
private def mkMVarSyntax : TermElabM Syntax := do
mvarId ← mkFreshId;
pure $ Syntax.node `MVarWithIdKind #[Syntax.node mvarId #[]]

/-- Given a syntax node constructed using `mkMVarSyntax`, return its MVarId -/
private def getMVarSyntaxMVarId (stx : Syntax) : MVarId :=
(stx.getArg 0).getKind

/--
  The elaboration function for `Syntax` created using `mkMVarSyntax`.
  It just converts the metavariable id wrapped by the Syntax into an `Expr`. -/
@[builtinTermElab MVarWithIdKind] def elabMVarWithIdKind : TermElab :=
fun stx expectedType? => pure $ mkInaccessible $ mkMVar (getMVarSyntaxMVarId stx)

@[builtinTermElab inaccessible] def elabInaccessible : TermElab :=
fun stx expectedType? => do
  e ← elabTerm (stx.getArg 1) expectedType?;
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
forallBoundedTelescope ctorVal.type ctorVal.nparams fun ps _ =>
  ps.foldlM
    (fun acc p => do
      localDecl ← getLocalDecl p.fvarId!;
      if localDecl.binderInfo.isExplicit then pure $ acc+1 else pure acc)
    0

private def throwAmbiguous {α} (fs : List Expr) : M α :=
throwError ("ambiguous pattern, use fully qualified name, possible interpretations " ++ fs)

def resolveId? (stx : Syntax) : M (Option Expr) :=
match stx with
| Syntax.ident _ _ val preresolved => do
  rs ← liftM $ catch (resolveName val preresolved []) (fun _ => pure []);
  let rs := rs.filter fun ⟨f, projs⟩ => projs.isEmpty;
  let fs := rs.map fun ⟨f, _⟩ => f;
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

instance Context.inhabited : Inhabited Context :=
⟨⟨arbitrary _, none, false, false, #[], 0, #[], [], #[]⟩⟩

private def isDone (ctx : Context) : Bool :=
ctx.paramDeclIdx ≥ ctx.paramDecls.size

private def finalize (ctx : Context) : M Syntax :=
if ctx.namedArgs.isEmpty && ctx.args.isEmpty then do
  fStx ← `(@$(ctx.funId):ident);
  pure $ mkAppStx fStx ctx.newArgs
else
  throwError "too many arguments"

private def isNextArgAccessible (ctx : Context) : Bool :=
let i := ctx.paramDeclIdx;
match ctx.ctorVal? with
| some ctorVal => i ≥ ctorVal.nparams -- For constructor applications only fields are accessible
| none =>
  if h : i < ctx.paramDecls.size then
    -- For `[matchPattern]` applications, only explicit parameters are accessible.
    let d := ctx.paramDecls.get ⟨i, h⟩;
    d.binderInfo.isExplicit
  else
    false

private def getNextParam (ctx : Context) : LocalDecl × Context :=
let i := ctx.paramDeclIdx;
let d := ctx.paramDecls.get! i;
(d, { ctx with paramDeclIdx := ctx.paramDeclIdx + 1 })

private def pushNewArg (collect : Syntax → M Syntax) (accessible : Bool) (ctx : Context) (arg : Arg) : M Context :=
match arg with
| Arg.stx stx => do
  stx ← if accessible then collect stx else pure stx;
  pure { ctx with newArgs := ctx.newArgs.push stx }
| _           => unreachable!

private def processExplicitArg (collect : Syntax → M Syntax) (accessible : Bool) (ctx : Context) : M Context :=
match ctx.args with
| [] =>
  if ctx.ellipsis then do
    hole ← `(_);
    pushNewArg collect accessible ctx (Arg.stx hole)
  else
    throwError ("explicit parameter is missing, unused named arguments " ++ toString (ctx.namedArgs.map $ fun narg => narg.name))
| arg::args => do
  let ctx := { ctx with args := args };
  pushNewArg collect accessible ctx arg

private def processImplicitArg (collect : Syntax → M Syntax) (accessible : Bool) (ctx : Context) : M Context :=
if ctx.explicit then
  processExplicitArg collect accessible ctx
else do
  hole ← `(_);
  pushNewArg collect accessible ctx (Arg.stx hole)

private partial def processCtorAppAux (collect : Syntax → M Syntax) : Context → M Syntax
| ctx =>
  if isDone ctx then finalize ctx
  else
    let accessible := isNextArgAccessible ctx;
    let (d, ctx)   := getNextParam ctx;
    match ctx.namedArgs.findIdx? (fun namedArg => namedArg.name == d.userName) with
    | some idx => do
      let arg := ctx.namedArgs.get! idx;
      let ctx := { ctx with namedArgs := ctx.namedArgs.eraseIdx idx };
      ctx ← pushNewArg collect accessible ctx arg.val;
      processCtorAppAux ctx
    | none => do
      ctx ← match d.binderInfo with
      | BinderInfo.implicit     => processImplicitArg collect accessible ctx
      | BinderInfo.instImplicit => processImplicitArg collect accessible ctx
      | _                       => processExplicitArg collect accessible ctx;
      processCtorAppAux ctx

def processCtorApp (collect : Syntax → M Syntax) (f : Syntax) (namedArgs : Array NamedArg) (args : Array Arg) (ellipsis : Bool) : M Syntax := do
let args := args.toList;
(fId, explicit) ← match_syntax f with
| `($fId:ident)  => pure (fId, false)
| `(@$fId:ident) => pure (fId, true)
| _              => throwError "identifier expected";
some (Expr.const fName _ _) ← resolveId? fId | throwCtorExpected;
fInfo ← getConstInfo fName;
forallTelescopeReducing fInfo.type fun xs _ => do
paramDecls ← xs.mapM getFVarLocalDecl;
match fInfo with
| ConstantInfo.ctorInfo val =>
  processCtorAppAux collect
    { funId := fId, explicit := explicit, ctorVal? := val, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
| _ => do
  env ← getEnv;
  if hasMatchPatternAttribute env fName then
    processCtorAppAux collect
      { funId := fId, explicit := explicit, ctorVal? := none, paramDecls := paramDecls, namedArgs := namedArgs, args := args, ellipsis := ellipsis }
  else
    throwCtorExpected

end CtorApp

def processCtorApp (collect : Syntax → M Syntax) (stx : Syntax) : M Syntax := do
(f, namedArgs, args, ellipsis) ← liftM $ expandApp stx true;
CtorApp.processCtorApp collect f namedArgs args ellipsis

def processCtor (collect : Syntax → M Syntax) (stx : Syntax) : M Syntax := do
CtorApp.processCtorApp collect stx #[] #[] false

private def processVar (idStx : Syntax) : M Syntax := do
unless idStx.isIdent $
  throwErrorAt idStx "identifier expected";
let id := idStx.getId;
unless id.eraseMacroScopes.isAtomic $ throwError "invalid pattern variable, must be atomic";
s ← get;
when (s.found.contains id) $ throwError ("invalid pattern, variable '" ++ id ++ "' occurred more than once");
modify fun s => { s with vars := s.vars.push (PatternVar.localVar id), found := s.found.insert id };
pure idStx

/- Check whether `stx` is a pattern variable or constructor-like (i.e., constructor or constant tagged with `[matchPattern]` attribute) -/
private def processId (collect : Syntax → M Syntax) (stx : Syntax) : M Syntax := do
env ← getEnv;
f? ← resolveId? stx;
match f? with
| none   => processVar stx
| some f => match f with
  | Expr.const fName _ _ => do
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
| Name.str p s _ => do p ← nameToPattern p; `(Name.str $p $(quote s) _)
| Name.num p n _ => do p ← nameToPattern p; `(Name.num $p $(quote n) _)

private def quotedNameToPattern (stx : Syntax) : TermElabM Syntax :=
match (stx.getArg 0).isNameLit? with
| some val => nameToPattern val
| none     => throwIllFormedSyntax

partial def collect : Syntax → M Syntax
| stx@(Syntax.node k args) => withRef stx $ withFreshMacroScope $
  if k == `Lean.Parser.Term.app then do
    processCtorApp collect stx
  else if k == `Lean.Parser.Term.anonymousCtor then do
    elems ← (args.get! 1).getArgs.mapSepElemsM $ collect;
    pure $ Syntax.node k $ args.set! 1 $ mkNullNode elems
  else if k == `Lean.Parser.Term.structInst then do
    /- { " >> optional (try (termParser >> " with ")) >> sepBy structInstField ", " true >> optional ".." >> optional (" : " >> termParser) >> " }" -/
    let withMod := args.get! 1;
    unless withMod.isNone $
      throwErrorAt withMod "invalid struct instance pattern, 'with' is not allowed in patterns";
    let fields := (args.get! 2).getArgs;
    fields ← fields.mapSepElemsM fun field => do {
      -- parser! structInstLVal >> " := " >> termParser
      newVal ← collect (field.getArg 3); -- `structInstLVal` has arity 2
      pure $ field.setArg 3 newVal
    };
    pure $ Syntax.node k $ args.set! 2 $ mkNullNode fields
  else if k == `Lean.Parser.Term.hole then do
    r ← liftM mkMVarSyntax;
    modify fun s => { s with vars := s.vars.push $ PatternVar.anonymousVar $ getMVarSyntaxMVarId r };
    pure r
  else if k == `Lean.Parser.Term.paren then
    let arg := args.get! 1;
    if arg.isNone then
      pure stx -- `()`
    else do
      let t := arg.getArg 0;
      let s := arg.getArg 1;
      if s.isNone || (s.getArg 0).isOfKind `Lean.Parser.Term.typeAscription then do
        -- Ignore `s`, since it empty or it is a type ascription
        t ← collect t;
        let arg := arg.setArg 0 t;
        pure $ Syntax.node k $ args.set! 1 arg
      else do
        -- Tuple literal is a constructor
        t ← collect t;
        let arg := arg.setArg 0 t;
        let tupleTail := s.getArg 0;
        let tupleTailElems := (tupleTail.getArg 1).getArgs;
        tupleTailElems ← tupleTailElems.mapSepElemsM collect;
        let tupleTail := tupleTail.setArg 1 $ mkNullNode tupleTailElems;
        let s         := s.setArg 0 tupleTail;
        let arg       := arg.setArg 1 s;
        pure $ Syntax.node k $ args.set! 1 arg
  else if k == `Lean.Parser.Term.explicitUniv then do
    processCtor collect (stx.getArg 0)
  else if k == `Lean.Parser.Term.namedPattern then do
    /- Recall that
       def namedPattern := check... >> tparser! "@" >> termParser -/
    let id := stx.getArg 0;
    processVar id;
    let pat := stx.getArg 2;
    pat ← collect pat;
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
    liftM $ quotedNameToPattern stx
  else if k == choiceKind then
    throwError "invalid pattern, notation is ambiguous"
  else
    throwInvalidPattern
| stx@(Syntax.ident _ _ _ _) =>
  processId collect stx
| stx =>
  throwInvalidPattern

def main (alt : MatchAltView) : M MatchAltView := do
patterns ← alt.patterns.mapM fun p => do {
  trace `Elab.match fun _ => "collecting variables at pattern: " ++ p;
  collect p
};
pure { alt with patterns := patterns }

end CollectPatternVars

private def collectPatternVars (alt : MatchAltView) : TermElabM (Array PatternVar × MatchAltView) := do
(alt, s) ← (CollectPatternVars.main alt).run {};
pure (s.vars, alt)

/- Return the pattern variables in the given pattern.
  Remark: this method is not used here, but in other macros (e.g., at `Do.lean`). -/
def getPatternVars (patternStx : Syntax) : TermElabM (Array PatternVar) := do
patternStx ← liftMacroM $ expandMacros patternStx;
(_, s) ← (CollectPatternVars.collect patternStx).run {};
pure s.vars

def getPatternsVars (patterns : Array Syntax) : TermElabM (Array PatternVar) := do
(_, s) ← (patterns.mapM fun pattern => do { pattern ← liftMacroM $ expandMacros pattern; CollectPatternVars.collect pattern }).run {};
pure s.vars

/- We convert the collected `PatternVar`s intro `PatternVarDecl` -/
inductive PatternVarDecl
/- For `anonymousVar`, we create both a metavariable and a free variable. The free variable is used as an assignment for the metavariable
   when it is not assigned during pattern elaboration. -/
| anonymousVar (mvarId : MVarId) (fvarId : FVarId)
| localVar     (fvarId : FVarId)

private partial def withPatternVarsAux {α} (pVars : Array PatternVar) (k : Array PatternVarDecl → TermElabM α)
    : Nat → Array PatternVarDecl → TermElabM α
| i, decls =>
  if h : i < pVars.size then
    match pVars.get ⟨i, h⟩ with
    | PatternVar.anonymousVar mvarId => do
      type ← mkFreshTypeMVar;
      userName ← mkFreshBinderName;
      withLocalDecl userName BinderInfo.default type fun x =>
        withPatternVarsAux (i+1) (decls.push (PatternVarDecl.anonymousVar mvarId x.fvarId!))
    | PatternVar.localVar userName   => do
      type ← mkFreshTypeMVar;
      withLocalDecl userName BinderInfo.default type fun x =>
        withPatternVarsAux (i+1) (decls.push (PatternVarDecl.localVar x.fvarId!))
  else do
    /- We must create the metavariables for `PatternVar.anonymousVar` AFTER we create the new local decls using `withLocalDecl`.
       Reason: their scope must include the new local decls since some of them are assigned by typing constraints. -/
    decls.forM fun decl => match decl with
      | PatternVarDecl.anonymousVar mvarId fvarId => do
        type ← inferType (mkFVar fvarId);
        _ ← mkFreshExprMVarWithId mvarId type;
        pure ()
      | _ => pure ();
    k decls

private def withPatternVars {α} (pVars : Array PatternVar) (k : Array PatternVarDecl → TermElabM α) : TermElabM α :=
withPatternVarsAux pVars k 0 #[]

private partial def elabPatternsAux (patternStxs : Array Syntax) : Nat → Expr → Array Expr → TermElabM (Array Expr × Expr)
| i, matchType, patterns =>
  if h : i < patternStxs.size then do
    matchType ← whnf matchType;
    match matchType with
    | Expr.forallE _ d b _ => do
      let patternStx := patternStxs.get ⟨i, h⟩;
      pattern ← elabTermEnsuringType patternStx d;
      elabPatternsAux (i+1) (b.instantiate1 pattern) (patterns.push pattern)
    | _ => throwError "unexpected match type"
  else
    pure (patterns, matchType)

def finalizePatternDecls (patternVarDecls : Array PatternVarDecl) : TermElabM (Array LocalDecl) :=
patternVarDecls.foldlM
  (fun (decls : Array LocalDecl) pdecl => do
    match pdecl with
    | PatternVarDecl.localVar fvarId => do
      decl ← getLocalDecl fvarId;
      decl ← instantiateLocalDeclMVars decl;
      pure $ decls.push decl
    | PatternVarDecl.anonymousVar mvarId fvarId => do
      e ← instantiateMVars (mkMVar mvarId);
      trace `Elab.match fun _ => "finalizePatternDecls: mvarId: " ++ mvarId ++ " := " ++ e ++ ", fvarId: " ++ mkFVar fvarId;
      match e with
      | Expr.mvar newMVarId _ => do
        /- Metavariable was not assigned, or assigned to another metavariable. So,
           we assign to the auxiliary free variable we created at `withPatternVars` to `newMVarId`. -/
        assignExprMVar newMVarId (mkFVar fvarId);
        trace `Elab.match fun _ => "finalizePatternDecls: " ++ mkMVar newMVarId ++ " := " ++ mkFVar fvarId;
        decl ← getLocalDecl fvarId;
        decl ← instantiateLocalDeclMVars decl;
        pure $ decls.push decl
      | _ => pure decls)
  #[]

open Meta.Match (Pattern Pattern.var Pattern.inaccessible Pattern.ctor Pattern.as Pattern.val Pattern.arrayLit AltLHS MatcherResult)

namespace ToDepElimPattern

structure State :=
(found      : NameSet := {})
(localDecls : Array LocalDecl)
(newLocals  : NameSet := {})

abbrev M := StateRefT State TermElabM

private def alreadyVisited (fvarId : FVarId) : M Bool := do
s ← get;
pure $ s.found.contains fvarId

private def markAsVisited (fvarId : FVarId) : M Unit :=
modify $ fun s => { s with found := s.found.insert fvarId }

private def throwInvalidPattern {α} (e : Expr) : M α :=
throwError ("invalid pattern " ++ indentExpr e)

/- Create a new LocalDecl `x` for the metavariable `mvar`, and return `Pattern.var x` -/
private def mkLocalDeclFor (mvar : Expr) : M Pattern := do
let mvarId := mvar.mvarId!;
s ← get;
val? ← getExprMVarAssignment? mvarId;
match val? with
| some val => pure $ Pattern.inaccessible val
| none => do
  fvarId ← mkFreshId;
  type   ← inferType mvar;
  /- HACK: `fvarId` is not in the scope of `mvarId`
     If this generates problems in the future, we should update the metavariable declarations. -/
  assignExprMVar mvarId (mkFVar fvarId);
  userName ← liftM $ mkFreshBinderName;
  let newDecl := LocalDecl.cdecl (arbitrary _) fvarId userName type BinderInfo.default;
  modify $ fun s =>
    { s with
      newLocals  := s.newLocals.insert fvarId,
      localDecls :=
      match s.localDecls.findIdx? fun decl => mvar.occurs decl.type with
      | none   => s.localDecls.push newDecl -- None of the existing declarations depend on `mvar`
      | some i => s.localDecls.insertAt i newDecl };
  pure $ Pattern.var fvarId

partial def main : Expr → M Pattern
| e =>
  let isLocalDecl (fvarId : FVarId) : M Bool := do {
    s ← get;
    pure $ s.localDecls.any fun d => d.fvarId == fvarId
  };
  let mkPatternVar (fvarId : FVarId) (e : Expr) : M Pattern := do {
    condM (alreadyVisited fvarId)
      (pure $ Pattern.inaccessible e)
      (do markAsVisited fvarId; pure $ Pattern.var e.fvarId!)
  };
  let mkInaccessible (e : Expr) : M Pattern := do {
    match e with
    | Expr.fvar fvarId _ =>
      condM (isLocalDecl fvarId)
        (mkPatternVar fvarId e)
        (pure $ Pattern.inaccessible e)
    | _ =>
      pure $ Pattern.inaccessible e
  };
  match inaccessible? e with
  | some t => mkInaccessible t
  | none   =>
  match e.arrayLit? with
  | some (α, lits) => do
    ps ← lits.mapM main;
    pure $ Pattern.arrayLit α ps
  | none =>
  if e.isAppOfArity `namedPattern 3 then do
    p ← main $ e.getArg! 2;
    match e.getArg! 1 with
    | Expr.fvar fvarId _ => pure $ Pattern.as fvarId p
    | _                  => throwError "unexpected occurrence of auxiliary declaration 'namedPattern'"
  else if e.isNatLit || e.isStringLit || e.isCharLit then
    pure $ Pattern.val e
  else if e.isFVar then do
    let fvarId := e.fvarId!;
    unlessM (isLocalDecl fvarId) $ throwInvalidPattern e;
    mkPatternVar fvarId e
  else if e.isMVar then do
    mkLocalDeclFor e
  else do
    newE ← whnf e;
    if newE != e then
      main newE
    else matchConstCtor e.getAppFn (fun _ => throwInvalidPattern e) fun v us => do
      let args := e.getAppArgs;
      unless (args.size == v.nparams + v.nfields) $ throwInvalidPattern e;
      let params := args.extract 0 v.nparams;
      let fields := args.extract v.nparams args.size;
      fields ← fields.mapM main;
      pure $ Pattern.ctor v.name us params.toList fields.toList

end ToDepElimPattern

def withDepElimPatterns {α} (localDecls : Array LocalDecl) (ps : Array Expr) (k : Array LocalDecl → Array Pattern → TermElabM α) : TermElabM α := do
(patterns, s) ← (ps.mapM ToDepElimPattern.main).run { localDecls := localDecls };
localDecls ← s.localDecls.mapM fun d => instantiateLocalDeclMVars d;
/- toDepElimPatterns may have added new localDecls. Thus, we must update the local context before we execute `k` -/
lctx ← getLCtx;
let lctx := localDecls.foldl (fun (lctx : LocalContext) d => lctx.erase d.fvarId) lctx;
let lctx := localDecls.foldl (fun (lctx : LocalContext) d => lctx.addDecl d) lctx;
adaptTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) $ k localDecls patterns

private def withElaboratedLHS {α} (ref : Syntax) (patternVarDecls : Array PatternVarDecl) (patternStxs : Array Syntax) (matchType : Expr)
  (k : AltLHS → Expr → TermElabM α) : TermElabM α := do
(patterns, matchType) ← withSynthesize $ elabPatternsAux patternStxs 0 matchType #[];
localDecls ← finalizePatternDecls patternVarDecls;
patterns ← patterns.mapM instantiateMVars;
withDepElimPatterns localDecls patterns fun localDecls patterns =>
  k { ref := ref, fvarDecls := localDecls.toList, patterns := patterns.toList } matchType

def elabMatchAltView (alt : MatchAltView) (matchType : Expr) : TermElabM (AltLHS × Expr) :=
withRef alt.ref do
(patternVars, alt) ← collectPatternVars alt;
trace `Elab.match fun _ => "patternVars: " ++ toString patternVars;
withPatternVars patternVars fun patternVarDecls => do
  withElaboratedLHS alt.ref patternVarDecls alt.patterns matchType fun altLHS matchType => do
    rhs ← elabTermEnsuringType alt.rhs matchType;
    let xs := altLHS.fvarDecls.toArray.map LocalDecl.toExpr;
    rhs ← if xs.isEmpty then pure $ mkSimpleThunk rhs else mkLambdaFVars xs rhs;
    trace `Elab.match fun _ => "rhs: " ++ rhs;
    pure (altLHS, rhs)

def mkMatcher (elimName : Name) (matchType : Expr) (numDiscrs : Nat) (lhss : List AltLHS) : TermElabM MatcherResult :=
liftMetaM $ Meta.Match.mkMatcher elimName matchType numDiscrs lhss

def reportMatcherResultErrors (result : MatcherResult) : TermElabM Unit := do
-- TODO: improve error messages
unless result.counterExamples.isEmpty $
  throwError ("missing cases:" ++ Format.line ++ Meta.Match.counterExamplesToMessageData result.counterExamples);
unless result.unusedAltIdxs.isEmpty $
  throwError ("unused alternatives: " ++ toString (result.unusedAltIdxs.map fun idx => "#" ++ toString (idx+1)))

private def elabMatchAux (discrStxs : Array Syntax) (altViews : Array MatchAltView) (matchOptType : Syntax) (expectedType : Expr)
    : TermElabM Expr := do
(discrs, matchType, altViews) ← elabMatchTypeAndDiscrs discrStxs matchOptType altViews expectedType;
matchAlts ← liftMacroM $ expandMacrosInPatterns altViews;
trace `Elab.match fun _ => "matchType: " ++ matchType;
alts ← matchAlts.mapM $ fun alt => elabMatchAltView alt matchType;
synthesizeSyntheticMVarsNoPostponing;
-- TODO report error if matchType or altLHSS.toList have metavars
let rhss := alts.map Prod.snd;
let altLHSS := alts.map Prod.fst;
let numDiscrs := discrs.size;
matcherName ← mkAuxName `match;
matcherResult ← mkMatcher matcherName matchType numDiscrs altLHSS.toList;
motive ← forallBoundedTelescope matchType numDiscrs fun xs matchType => mkLambdaFVars xs matchType;
reportMatcherResultErrors matcherResult;
let r := mkApp matcherResult.matcher motive;
let r := mkAppN r discrs;
let r := mkAppN r rhss;
trace `Elab.match fun _ => "result: " ++ r;
pure r

private def getDiscrs (matchStx : Syntax) : Array Syntax :=
(matchStx.getArg 1).getArgs.getSepElems

private def getMatchOptType (matchStx : Syntax) : Syntax :=
matchStx.getArg 2

private def expandNonAtomicDiscrsAux (matchStx : Syntax) : List Syntax → Array Syntax → TermElabM Syntax
| [], discrsNew =>
  let discrs := mkSepStx discrsNew (mkAtomFrom matchStx ", ");
  pure $ matchStx.setArg 1 discrs
| discr :: discrs, discrsNew => do
  -- Recall that
  -- matchDiscr := parser! optional (ident >> ":") >> termParser
  let term := discr.getArg 1;
  local? ← isLocalIdent? term;
  match local? with
  | some _ => expandNonAtomicDiscrsAux discrs (discrsNew.push discr)
  | none   => withFreshMacroScope do
    d ← `(_discr);
    unless (isAuxDiscrName d.getId) $ -- Use assertion?
      throwError "unexpected internal auxiliary discriminant name";
    let discrNew := discr.setArg 1 d;
    r ← expandNonAtomicDiscrsAux discrs (discrsNew.push discrNew);
    `(let _discr := $term; $r)

private def expandNonAtomicDiscrs? (matchStx : Syntax) : TermElabM (Option Syntax) :=
let matchOptType := getMatchOptType matchStx;
if matchOptType.isNone then do
  let discrs := getDiscrs matchStx;
  allLocal ← discrs.allM fun discr => Option.isSome <$> isLocalIdent? (discr.getArg 1);
  if allLocal then
    pure none
  else
    some <$> expandNonAtomicDiscrsAux matchStx discrs.toList #[]
else
  -- We do not pull non atomic discriminants when match type is provided explicitly by the user
  pure none

private def waitExpectedType (expectedType? : Option Expr) : TermElabM Expr := do
tryPostponeIfNoneOrMVar expectedType?;
match expectedType? with
  | some expectedType => pure expectedType
  | none              => mkFreshTypeMVar

private def tryPostponeIfDiscrTypeIsMVar (matchStx : Syntax) : TermElabM Unit :=
-- We don't wait for the discriminants types when match type is provided by user
when (getMatchOptType matchStx).isNone do
  let discrs := getDiscrs matchStx;
  discrs.forM fun discr => do
    let term := discr.getArg 1;
    local? ← isLocalIdent? term;
    match local? with
    | none   => throwErrorAt discr "unexpected discriminant" -- see `expandNonAtomicDiscrs?
    | some d => do
      dType ← inferType d;
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
tryPostponeIfNoneOrMVar expectedType?;
tryPostponeIfDiscrTypeIsMVar matchStx;
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
expectedType ← waitExpectedTypeAndDiscrs stx expectedType?;
let discrStxs := (getDiscrs stx).map fun d => d;
let altViews     := getMatchAlts stx;
let matchOptType := getMatchOptType stx;
elabMatchAux discrStxs altViews matchOptType expectedType

-- parser! "match " >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermElab «match»] def elabMatch : TermElab :=
fun stx expectedType? => match_syntax stx with
  | `(match $discr:term with $y:ident => $rhs:term)           => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term with | $y:ident => $rhs:term)         => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term : $type with $y:ident => $rhs:term)   => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | `(match $discr:term : $type with | $y:ident => $rhs:term) => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | _ => do
    stxNew? ← expandNonAtomicDiscrs? stx;
    match stxNew? with
    | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
    | none => do
      let discrs       := getDiscrs stx;
      let matchOptType := getMatchOptType stx;
      when (!matchOptType.isNone && discrs.any fun d => !(d.getArg 0).isNone) $
        throwErrorAt matchOptType "match expected type should not be provided when discriminants with equality proofs are used";
      elabMatchCore stx expectedType?

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.match;
pure ()

-- parser!:leadPrec "nomatch " >> termParser
@[builtinTermElab «nomatch»] def elabNoMatch : TermElab :=
fun stx expectedType? => match_syntax stx with
  | `(nomatch $discrExpr) => do
      expectedType ← waitExpectedType expectedType?;
      let discr := Syntax.node `Lean.Parser.Term.matchDiscr #[mkNullNode, discrExpr];
      elabMatchAux #[discr] #[] mkNullNode expectedType
  | _ => throwUnsupportedSyntax

end Term
end Elab
end Lean
