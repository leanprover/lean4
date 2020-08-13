/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.EqnCompiler.MatchPattern
import Lean.Meta.EqnCompiler.DepElim
import Lean.Elab.SyntheticMVars

namespace Lean
namespace Elab
namespace Term

/- This modules assumes "match"-expressions use the following syntax.

```lean
def matchAlt : Parser :=
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $
  sepBy1 termParser ", " >> darrow >> termParser

def matchAlts (optionalFirstBar := true) : Parser :=
withPosition $ fun pos =>
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

def mkMatchAltView (matchAlt : Syntax) : MatchAltView :=
{ ref := matchAlt, patterns := (matchAlt.getArg 0).getArgs.getSepElems, rhs := matchAlt.getArg 2 }

private def expandSimpleMatch (stx discr lhsVar rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
newStx ← `(let $lhsVar := $discr; $rhs);
withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private def expandSimpleMatchWithType (stx discr lhsVar type rhs : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
newStx ← `(let $lhsVar : $type := $discr; $rhs);
withMacroExpansion stx newStx $ elabTerm newStx expectedType?

private def expandMatchOptTypeAux (ref : Syntax) : Nat → MacroM Syntax
| 0   => pure $ mkHole ref
| n+1 => do t ← expandMatchOptTypeAux n; r ← `(forall _, $t); pure (r.copyInfo ref)

private def expandMatchOptType (ref : Syntax) (optType : Syntax) (numDiscrs : Nat) : MacroM Syntax :=
if optType.isNone then
  expandMatchOptTypeAux ref numDiscrs
else
  pure $ (optType.getArg 0).getArg 1

private def elabMatchOptType (matchStx : Syntax) (numDiscrs : Nat) : TermElabM Expr := do
typeStx ← liftMacroM $ expandMatchOptType matchStx (matchStx.getArg 2) numDiscrs;
elabType typeStx

private partial def elabDiscrsAux (ref : Syntax) (discrStxs : Array Syntax) (expectedType : Expr) : Nat → Expr → Array Expr → TermElabM (Array Expr)
| i, matchType, discrs =>
  if h : i < discrStxs.size then do
    let discrStx := discrStxs.get ⟨i, h⟩;
    matchType ← whnf ref matchType;
    match matchType with
    | Expr.forallE _ d b _ => do
      discr ← elabTerm discrStx d;
      discr ← ensureHasType discrStx d discr;
      elabDiscrsAux (i+1) (b.instantiate1 discr) (discrs.push discr)
    | _ => throwError ref ("invalid type provided to match-expression, function type with arity #" ++ toString discrStxs ++ " expected")
  else do
    unlessM (isDefEq ref matchType expectedType) $
      throwError ref ("invalid result type provided to match-expression" ++ indentExpr matchType ++ Format.line ++ "expected type" ++ indentExpr expectedType);
    pure discrs

private def elabDiscrs (ref : Syntax) (discrStxs : Array Syntax) (matchType : Expr) (expectedType : Expr) : TermElabM (Array Expr) :=
elabDiscrsAux ref discrStxs expectedType 0 matchType #[]

/-
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $ sepBy1 termParser ", " >> darrow >> termParser
-/
def expandMacrosInPatterns (matchAlts : Array MatchAltView) : TermElabM (Array MatchAltView) := do
env ← getEnv;
matchAlts.mapM fun matchAlt => do
  patterns ← liftMacroM $ matchAlt.patterns.mapM $ expandMacros env;
  pure $ { matchAlt with patterns := patterns }

/- Given `stx` a match-expression, return its alternatives. -/
private def getMatchAlts (stx : Syntax) : Array MatchAltView :=
let alts : Array Syntax := (stx.getArg 5).getArgs.filter fun alt => alt.getKind == `Lean.Parser.Term.matchAlt;
alts.map mkMatchAltView

/--
  Auxiliary annotation used to mark terms marked with the "inaccessible" annotation `.(t)` and
  `_` in patterns. -/
def mkInaccessible (e : Expr) : Expr :=
mkAnnotation `_inaccessible e

def isInaccessible? (e : Expr) : Option Expr :=
isAnnotation? `_inaccessible e

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
  that implied by typing constraints. Thus, we represent them with fresh named holes `?x`.
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

abbrev M := StateT State TermElabM

private def throwCtorExpected {α} (stx : Syntax) : M α :=
liftM $ throwError stx "invalid pattern, constructor or constant marked with '[matchPattern]' expected"

private def getNumExplicitCtorParams (ref : Syntax) (ctorVal : ConstructorVal) : TermElabM Nat :=
liftMetaM ref $ Meta.forallBoundedTelescope ctorVal.type ctorVal.nparams fun ps _ =>
  ps.foldlM
    (fun acc p => do
      localDecl ← Meta.getLocalDecl p.fvarId!;
      if localDecl.binderInfo.isExplicit then pure $ acc+1 else pure acc)
    0

private def throwAmbiguous {α} (ref : Syntax) (fs : List Expr) : M α :=
liftM $ throwError ref ("ambiguous pattern, use fully qualified name, possible interpretations " ++ fs)

private def processVar (ref : Syntax) (id : Name) (mustBeCtor : Bool := false) : M Unit := do
when mustBeCtor $ throwCtorExpected ref;
unless id.eraseMacroScopes.isAtomic $ liftM $ throwError ref "invalid pattern variable, must be atomic";
s ← get;
when (s.found.contains id) $ liftM $ throwError ref ("invalid pattern, variable '" ++ id ++ "' occurred more than once");
modify fun s => { s with vars := s.vars.push (PatternVar.localVar id), found := s.found.insert id }

/- Check whether `stx` is a pattern variable or constructor-like (i.e., constructor or constant tagged with `[matchPattern]` attribute)
   If `mustBeCtor == true`, then `stx` cannot be a pattern variable.

   If `stx` is a constructor, then return the number of explicit arguments that are inductive type parameters. -/
private def processIdAux (stx : Syntax) (mustBeCtor : Bool) : M Nat := do
env ← liftM $ getEnv;
match stx.isTermId? true with
| none           => throwCtorExpected stx
| some (id, opt) => do
  when ((opt.getArg 0).isOfKind `Lean.Parser.Term.namedPattern) $
    liftM $ throwError stx "invalid occurrence of named pattern";
  match id with
  | Syntax.ident _ _ val preresolved => do
    rs ← liftM $ catch (resolveName stx val preresolved []) (fun _ => pure []);
    let rs := rs.filter fun ⟨f, projs⟩ => projs.isEmpty;
    let fs := rs.map fun ⟨f, _⟩ => f;
    match fs with
    | []  => do processVar stx id.getId mustBeCtor; pure 0
    | [f] => match f with
      | Expr.const fName _ _ =>
        match env.find? fName with
        | some $ ConstantInfo.ctorInfo val => liftM $ getNumExplicitCtorParams stx val
        | some $ info =>
          if EqnCompiler.hasMatchPatternAttribute env fName then pure 0
          else do processVar stx id.getId mustBeCtor; pure 0
        | none => throwCtorExpected stx
      | _ => do processVar stx id.getId mustBeCtor; pure 0
    | _   => throwAmbiguous stx fs
  | _ => unreachable!

private def processCtor (stx : Syntax) : M Nat :=
processIdAux stx true

private def processId (stx : Syntax) : M Unit := do
_ ← processIdAux stx false; pure ()

private def throwInvalidPattern {α} (stx : Syntax) : M α :=
liftM $ throwError stx "invalid pattern"

private partial def collect : Syntax → M Syntax
| stx@(Syntax.node k args) => withFreshMacroScope $
  if k == `Lean.Parser.Term.app then do
    let appFn   := args.get! 0;
    let appArgs := (args.get! 1).getArgs;
    appArgs.forM fun appArg =>
      when (appArg.isOfKind `Lean.Parser.Term.namedPattern) $
        liftM $ throwError appArg "named parameters are not allowed in patterns";
    /- We must skip explict inducitve datatype parameters since they are by defaul inaccessible.
       Example: `A` is inaccessible term at `Sum.inl A b` -/
    numArgsToSkip ← processCtor appFn;
    appArgs ← appArgs.mapIdxM fun i arg => if i < numArgsToSkip then pure arg else collect arg;
    pure $ Syntax.node k $ args.set! 1 (mkNullNode appArgs)
  else if k == `Lean.Parser.Term.anonymousCtor then do
    elems ← (args.get! 1).getArgs.mapSepElemsM $ collect;
    pure $ Syntax.node k $ args.set! 1 $ mkNullNode elems
  else if k == `Lean.Parser.Term.structInst then do
    /- { " >> optional (try (termParser >> " with ")) >> sepBy structInstField ", " true >> optional ".." >> optional (" : " >> termParser) >> " }" -/
    let withMod := args.get! 1;
    unless withMod.isNone $
      liftM $ throwError withMod "invalid struct instance pattern, 'with' is not allowed in patterns";
    let fields := (args.get! 2).getArgs;
    fields ← fields.mapSepElemsM fun field => do {
      -- parser! structInstLVal >> " := " >> termParser
      newVal ← collect (field.getArg 2);
      pure $ field.setArg 2 newVal
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
  else if k == `Lean.Parser.Term.id then do
    let extra := args.get! 1;
    if extra.isNone then do
      processId stx;
      pure stx
    else if (extra.getArg 0).isOfKind `Lean.Parser.Term.explicitUniv then do
      _ ← processCtor stx;
      pure stx
    else if (extra.getArg 0).isOfKind `Lean.Parser.Term.namedPattern then do
      /- Recall that
         def namedPattern := checkNoWsBefore "no space before '@'" >> parser! "@" >> termParser maxPrec
         def id := parser! ident >> optional (explicitUniv <|> namedPattern) -/
      let id := stx.getIdOfTermId;
      processVar stx id;
      let pat := (extra.getArg 0).getArg 1;
      pat ← collect pat;
      `(namedPattern $(mkTermIdFrom stx id) $pat)
    else
      throwInvalidPattern stx
  else if k == `Lean.Parser.Term.inaccessible then
    pure stx
  else if k == `Lean.Parser.Term.str then
    pure stx
  else if k == `Lean.Parser.Term.num then
    pure stx
  else if k == `Lean.Parser.Term.char then
    pure stx
  else if k == choiceKind then
    liftM $ throwError stx "invalid pattern, notation is ambiguous"
  else
    throwInvalidPattern stx
| stx@(Syntax.ident _ _ _ _) => do
  processId stx;
  pure stx
| stx =>
  throwInvalidPattern stx

def main (alt : MatchAltView) : M MatchAltView := do
patterns ← alt.patterns.mapM fun p => do {
  liftM $ trace `Elab.match p fun _ => "collecting variables at pattern: " ++ p;
  collect p
};
pure { alt with patterns := patterns }

end CollectPatternVars

private def collectPatternVars (alt : MatchAltView) : TermElabM (Array PatternVar × MatchAltView) := do
(alt, s) ← (CollectPatternVars.main alt).run {};
pure (s.vars, alt)

private partial def withPatternVarsAux {α} (ref : Syntax) (pVars : Array PatternVar) (k : Array Expr → TermElabM α) : Nat → Array Expr → TermElabM α
| i, xs =>
  if h : i < pVars.size then
    match pVars.get ⟨i, h⟩ with
    | PatternVar.anonymousVar mvarId => do
      withPatternVarsAux (i+1) (xs.push (mkMVar mvarId))
    | PatternVar.localVar userName   => do
      type ← mkFreshTypeMVar ref;
      withLocalDecl ref userName BinderInfo.default type fun x => withPatternVarsAux (i+1) (xs.push x)
  else do
    /- We must create the metavariables for `PatternVar.anonymousVar` AFTER we create the new local decls using `withLocalDecl`.
       Reason: their scope must include the new local decls since some of them will be assigned by typing constraints. -/
    pVars.forM fun pvar => match pvar with
      | PatternVar.anonymousVar mvarId => do _ ← mkFreshExprMVarWithId ref mvarId; pure ()
      | _ => pure ();
    k xs

private def withPatternVars {α} (ref : Syntax) (pVars : Array PatternVar) (k : Array Expr → TermElabM α) : TermElabM α :=
withPatternVarsAux ref pVars k 0 #[]

private partial def elabPatternsAux (ref : Syntax) (patternStxs : Array Syntax) : Nat → Expr → Array Expr → TermElabM (Array Expr)
| i, matchType, patterns =>
  if h : i < patternStxs.size then do
    matchType ← whnf ref matchType;
    match matchType with
    | Expr.forallE _ d b _ => do
      let patternStx := patternStxs.get ⟨i, h⟩;
      pattern ← elabTerm patternStx d;
      pattern ← ensureHasType patternStx d pattern;
      elabPatternsAux (i+1) (b.instantiate1 pattern) (patterns.push pattern)
    | _ => throwError ref "unexpected match type"
  else
    pure patterns

/- Recall that `_` occurring in patterns are converted into metavariables. After we elaborate the patterns,
   this method is invoked to convert unassigned metavariables in new local decls.
   We execute `k` in the updated local context. -/
private partial def withPatternDeclsAux {α} (ref : Syntax) (patternVars : Array Expr) (k : Array LocalDecl → TermElabM α) : Nat → Array LocalDecl → TermElabM α
| i, decls =>
  if h : i < patternVars.size then do
    let pVar := patternVars.get ⟨i, h⟩;
    /- pVar is a free variable or a meta variable -/
    e ← instantiateMVars ref pVar;
    match e with
    | Expr.fvar fvarId _ => do
      decl ← getLocalDecl fvarId;
      withPatternDeclsAux (i+1) (decls.push decl)
    | Expr.mvar mvarId _ => do
      decl ← getMVarDecl mvarId;
      type ← instantiateMVars ref decl.type;
      withLocalDecl ref ((`_x).appendIndexAfter i) BinderInfo.default type fun x => do
        decl ← getLocalDecl x.fvarId!;
        withPatternDeclsAux (i+1) (decls.push decl)
    | _ =>
      withPatternDeclsAux (i+1) decls
  else
    k decls

private partial def withPatternDecls {α} (ref : Syntax) (patternVars : Array Expr) (k : Array LocalDecl → TermElabM α) : TermElabM α :=
withPatternDeclsAux ref patternVars k 0 #[]

private def elabPatterns (ref : Syntax) (patternVars : Array Expr) (patternStxs : Array Syntax) (matchType : Expr) : TermElabM (Array Expr) := do
patterns ← withSynthesize $ elabPatternsAux ref patternStxs 0 matchType #[];
patterns ← patterns.mapM $ instantiateMVars ref;
trace `Elab.match ref fun _ => "patterns: " ++ patterns;
withPatternDecls ref patternVars fun decls => do
trace `Elab.match ref fun _ => MessageData.ofArray $ decls.map fun (d : LocalDecl) => (d.userName ++ " : " ++ d.type : MessageData);
pure patterns

def elabMatchAltView (alt : MatchAltView) (matchType : Expr) : TermElabM (Meta.DepElim.AltLHS × Expr) := do
(patternVars, alt) ← collectPatternVars alt;
trace `Elab.match alt.ref fun _ => "patternVars: " ++ toString patternVars;
withPatternVars alt.ref patternVars fun xs => do
  trace `Elab.match alt.ref fun _ => "xs: " ++ xs;
  ps ← elabPatterns alt.ref xs alt.patterns matchType;
  -- TODO
  pure (⟨[], []⟩, arbitrary _)

/-
```
parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
```
Remark the `optIdent` must be `none` at `matchDiscr`. They are expanded by `expandMatchDiscr?`.
-/
private def elabMatchCore (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
tryPostponeIfNoneOrMVar expectedType?;
expectedType ← match expectedType? with
  | some expectedType => pure expectedType
  | none              => mkFreshTypeMVar stx;
let discrStxs := (stx.getArg 1).getArgs.getSepElems.map fun d => d.getArg 1;
matchType ← elabMatchOptType stx discrStxs.size;
matchAlts ← expandMacrosInPatterns $ getMatchAlts stx;
discrs ← elabDiscrs stx discrStxs matchType expectedType;
alts ← matchAlts.mapM $ fun alt => elabMatchAltView alt matchType;
throwError stx ("WIP type: " ++ matchType ++ "\n" ++ discrs ++ "\n" ++ toString (matchAlts.map fun alt => toString alt.patterns))

/- Auxiliary method for `expandMatchDiscr?` -/
private partial def mkMatchType (discrs : Array Syntax) : Nat → MacroM Syntax
| i => withFreshMacroScope $
  if h : i < discrs.size then
    let discr := discrs.get ⟨i, h⟩;
    if discr.isOfKind `Lean.Parser.Term.matchDiscr then do
      type ← mkMatchType (i+1);
      if (discr.getArg 0).isNone then
        `(_ → $type)
      else
        let t := discr.getArg 1;
        `((x : _) → x = $t → $type)
    else
      mkMatchType (i+1)
  else
    `(_)

private def mkOptType (typeStx : Syntax) : Syntax :=
mkNullNode #[mkNode `Lean.Parser.Term.typeSpec #[mkAtomFrom typeStx ", ", typeStx]]

/- Auxiliary method for `expandMatchDiscr?` -/
private partial def mkNewDiscrs (discrs : Array Syntax) : Nat → Array Syntax → MacroM (Array Syntax)
| i, newDiscrs =>
  if h : i < discrs.size then
    let discr := discrs.get ⟨i, h⟩;
    if discr.isOfKind `Lean.Parser.Term.matchDiscr then do
      if (discr.getArg 0).isNone then
        mkNewDiscrs (i+1) (newDiscrs.push discr)
      else do
        let newDiscrs := newDiscrs.push $ discr.setArg 0 mkNullNode;
        let newDiscrs := newDiscrs.push $ mkAtomFrom discr ", ";
        eqPrf ← `(Eq.refl _);
        let newDiscrs := newDiscrs.push $ mkNode `Lean.Parser.Term.matchDiscr #[mkNullNode, eqPrf];
        mkNewDiscrs (i+1) newDiscrs
    else
      mkNewDiscrs (i+1) (newDiscrs.push discr)
  else
    pure newDiscrs

/- Auxiliary method for `expandMatchDiscr?` -/
private partial def mkNewPatterns (ref : Syntax) (discrs patterns : Array Syntax) : Nat → Array Syntax → MacroM (Array Syntax)
| i, newPatterns =>
  if h : i < discrs.size then
    let discr := discrs.get ⟨i, h⟩;
    if h : i < patterns.size then
      let pattern := patterns.get ⟨i, h⟩;
      if discr.isOfKind `Lean.Parser.Term.matchDiscr then do
        if (discr.getArg 0).isNone then
          mkNewPatterns (i+1) (newPatterns.push pattern)
        else
          let newPatterns := newPatterns.push pattern;
          let newPatterns := newPatterns.push $ mkAtomFrom pattern ", ";
          let ident       := (discr.getArg 0).getArg 0;
          let newPatterns := newPatterns.push $ mkTermIdFromIdent ident;
          mkNewPatterns (i+1) newPatterns
      else
        -- it is a ", "
        mkNewPatterns (i+1) (newPatterns.push pattern)
    else
      throw $ Macro.Exception.error ref ("invalid number of patterns, expected #" ++ toString discrs.size)
  else
    pure newPatterns

/- Auxiliary method for `expandMatchDiscr?` -/
private partial def mkNewAlt (discrs : Array Syntax) (alt : Syntax) : MacroM Syntax := do
let patterns := (alt.getArg 0).getArgs;
newPatterns ← mkNewPatterns alt discrs patterns 0 #[];
pure $ alt.setArg 0 (mkNullNode newPatterns)

/- Auxiliary method for `expandMatchDiscr?` -/
private partial def mkNewAlts (discrs : Array Syntax) (alts : Array Syntax) : MacroM (Array Syntax) :=
alts.mapSepElemsM $ mkNewAlt discrs

/-- Expand discriminants of the form `h : t` -/
private def expandMatchDiscr? (stx : Syntax) : MacroM (Option Syntax) := do
let discrs := (stx.getArg 1).getArgs;
if discrs.getSepElems.all fun d => (d.getArg 0).isNone then
  pure none -- nothing to be done
else do
  unless (stx.getArg 2).isNone $
    throw $ Macro.Exception.error (stx.getArg 2) "match expected type should not be provided when discriminants with equality proofs are used";
  matchType ← mkMatchType discrs 0;
  let matchType := matchType.copyInfo stx;
  let stx := stx.setArg 2 (mkOptType matchType);
  newDiscrs ← mkNewDiscrs discrs 0 #[];
  let stx := stx.setArg 1 (mkNullNode newDiscrs);
  let alts := (stx.getArg 5).getArgs;
  newAlts ← mkNewAlts discrs alts;
  let stx := stx.setArg 5 (mkNullNode newAlts);
  pure stx

-- parser! "match " >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermElab «match»] def elabMatch : TermElab :=
fun stx expectedType? => match_syntax stx with
  | `(match $discr:term with $y:ident => $rhs:term)           => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term with | $y:ident => $rhs:term)         => expandSimpleMatch stx discr y rhs expectedType?
  | `(match $discr:term : $type with $y:ident => $rhs:term)   => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | `(match $discr:term : $type with | $y:ident => $rhs:term) => expandSimpleMatchWithType stx discr y type rhs expectedType?
  | _ => do
    stxNew? ← liftMacroM $ expandMatchDiscr? stx;
    match stxNew? with
    | some stxNew => withMacroExpansion stx stxNew $ elabTerm stxNew expectedType?
    | none        => elabMatchCore stx expectedType?

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.match;
pure ()

end Term
end Elab
end Lean
