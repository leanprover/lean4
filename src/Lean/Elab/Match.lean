/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Term

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
(patterns : Array Syntax)
(rhs      : Syntax)

def mkMatchAltView (matchAlt : Syntax) : MatchAltView :=
{ patterns := (matchAlt.getArg 0).getArgs.getSepElems, rhs := matchAlt.getArg 2 }

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

end Term
end Elab
end Lean
