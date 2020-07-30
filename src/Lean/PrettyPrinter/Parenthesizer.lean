/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-!
The parenthesizer inserts parentheses into a `Syntax` object where syntactically necessary, usually as an intermediary
step between the delaborator and the formatter. While the delaborator outputs structurally well-formed syntax trees that
can be re-elaborated without post-processing, this tree structure is lost in the formatter and thus needs to be
preserved by proper insertion of parentheses.

# The abstract problem & solution

The Lean 4 grammar is unstructured and extensible with arbitrary new parsers, so in general it is undecidable whether
parentheses are necessary or even allowed at any point in the syntax tree. Parentheses for different categories, e.g.
terms and levels, might not even have the same structure. In this module, we focus on the correct parenthesization of
parsers defined via `Lean.Parser.prattParser`, which includes both aforementioned built-in categories. Custom
parenthesizers can be added for new node kinds, but the data collected in the implementation below might not be
appropriate for other parenthesization strategies.

Usages of a parser defined via `prattParser` in general have the form `p prec`, where `prec` is the minimum precedence
or binding power. Recall that a Pratt parser greedily runs a leading parser with precedence at least `prec` (otherwise
it fails) followed by zero or more trailing parsers with precedence at least `prec`; the precedence of a parser is
encoded in the call to `leadingNode/trailingNode`, respectively. Thus we should parenthesize a syntax node `stx`
supposedly produced by `p prec` if

1. the leading/any trailing parser involved in `stx` has precedence < `prec` (because without parentheses, `p prec`
   would not produce all of `stx`), or
2. the trailing parser parsing the input to *the right of* `stx`, if any, has precedence >= `prec` (because without
   parentheses, `p prec` would have parsed it as well and made it a part of `stx`).

Note that in case 2, it is also sufficient to parenthesize a *parent* node as long as the offending parser is still to
the right of that node. For example, imagine the tree structure of `(f $ fun x => x) y` without parentheses. We need to
insert *some* parentheses between `x` and `y` since the lambda body is parsed with precedence 0, while the identifier
parser for `y` has precedence `maxPrec`. But we need to parenthesize the `$` node anyway since the precedence of its
RHS (0) again is smaller than that of `y`. So it's better to only parenthesize the outer node than ending up with
`(f $ (fun x => x)) y`.

# Implementation

We transform the syntax tree and collect the necessary precedence information for that in a single traversal over the
syntax tree and the parser (as a `Lean.Expr`) that produced it. The traversal is right-to-left to cover case 2. More
specifically, for every Pratt parser call, we store as monadic state the precedence of the left-most trailing parser and
the minimum precedence of any parser (`contPrec`/`minPrec`) in this call, if any, and the precedence of the nested
trailing Pratt parser call (`trailPrec`), if any. If `stP` is the state resulting from the traversal of a Pratt parser
call `p prec`, and `st` is the state of the surrounding call, we parenthesize if `prec > stP.minPrec` (case 1) or if
`stP.trailPrec <= st.contPrec` (case 2).

The primary traversal is over the parser `Expr`. The `visit` function takes such a parser and, if it is the application
of a constant `c`, looks for a `[parenthesizer c]` declaration. If it exists, we run it, which might again call `visit`.
Otherwise, we do a single step of reduction at the head of the expression (with `default` reducibility) and try again.
If the reduction is stuck, we fail. This happens mostly at the `Parser.mk` decl, which is irreducible, when some parser
primitive has not been handled yet. You can think of this traversal as a special-case, customized `Expr` interpreter.

The traversal over the `Syntax` object is complicated by the fact that a parser does not produce exactly one syntax
node, but an arbitrary (but constant, for each parser) amount that it pushes on top of the parser stack. This amount can
even be zero for parsers such as `checkWsBefore`. Thus we cannot simply pass and return a `Syntax` object to and from
`visit`. Instead, we use a `Syntax.Traverser` that allows arbitrary movement and modification inside the syntax tree.
Our traversal invariant is that a parser interpreter should stop at the syntax object to the *left* of all syntax
objects its parser produced, except when it is already at the left-most child. This special case is not an issue in
practice since if there is another parser to the left that produced zero nodes in this case, it should always do so, so
there is no danger of the left-most child being processed multiple times.

Ultimately, most parenthesizers are implemented via three primitives that do all the actual syntax traversal:
`visitParenthesizable mkParen prec` recurses on the current node and afterwards transforms it with `mkParen` if the above
condition for `p prec` is fulfilled. `visitToken` advances to the preceding sibling and is used on atoms. `visitArgs x`
executes `x` on the last child of the current node and then advances to the preceding sibling (of the original current
node).

-/

import Lean.Parser
import Lean.Meta
import Lean.Elab.Quotation

namespace Lean
namespace PrettyPrinter
namespace Parenthesizer

structure Context :=
-- We need to store this argument of `visitParenthesizable` to deal with the implicit Pratt parser call in
-- `trailingNode.parenthesizer`.
(mkParen : Option (Syntax → Syntax) := none)

structure State :=
(stxTrav : Syntax.Traverser)
--- precedence of the current left-most trailing parser, if any; see module doc for details
(contPrec : Option Nat := none)
-- current minimum precedence in this Pratt parser call, if any; see module doc for details
(minPrec : Option Nat := none)
-- precedence of the trailing Pratt parser call if any; see module doc for details
(trailPrec : Option Nat := none)
-- true iff we have already visited a token on this parser level; used for detecting trailing parsers
(visitedToken : Bool := false)

end Parenthesizer

abbrev ParenthesizerM := ReaderT Parenthesizer.Context $ StateT Parenthesizer.State MetaM

abbrev Parenthesizer := Expr → ParenthesizerM Unit

unsafe def mkParenthesizerAttribute : IO (KeyedDeclsAttribute Parenthesizer) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinParenthesizer,
  name := `parenthesizer,
  descr := "Register a parenthesizer.

[parenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.",
  valueTypeName := `Lean.PrettyPrinter.Parenthesizer,
  evalKey := fun env args => match attrParamSyntaxToIdentifier args with
    | some id => match env.find? id with
      | some _ => pure id
      | none   => throw ("invalid [parenthesizer] argument, unknown identifier '" ++ toString id ++ "'")
    | none    => throw "invalid [parenthesizer] argument, expected identifier"
} `Lean.PrettyPrinter.parenthesizerAttribute
@[init mkParenthesizerAttribute] constant parenthesizerAttribute : KeyedDeclsAttribute Parenthesizer := arbitrary _

namespace Parenthesizer

open Lean.Meta
open Lean.Format

instance ParenthesizerM.monadTraverser : Syntax.MonadTraverser ParenthesizerM := ⟨{
  get       := State.stxTrav <$> get,
  set       := fun t => modify (fun st => { st with stxTrav := t }),
  modifyGet := fun _ f => modifyGet (fun st => let (a, t) := f st.stxTrav; (a, { st with stxTrav := t })) }⟩

open Syntax.MonadTraverser

def addPrecCheck (prec : Nat) : ParenthesizerM Unit :=
modify $ fun st => { st with contPrec := prec, minPrec := Nat.min (st.minPrec.getD prec) prec }

/-- Execute `x` at the right-most child of the current node, if any, then advance to the left. -/
def visitArgs (x : ParenthesizerM Unit) : ParenthesizerM Unit := do
stx ← getCur;
when (stx.getArgs.size > 0) $
  goDown (stx.getArgs.size - 1) *> x <* goUp;
goLeft

/--
  Call an appropriate `[parenthesizer]` depending on the `Parser` `Expr` `p`. After the call, the traverser position
  should be to the left of all nodes produced by `p`, or at the left-most child if there are no other nodes left. -/
partial def visit : Parenthesizer | p => do
stx ← getCur;
-- do reductions _except_ for definition unfolding
p ← liftM $ whnfCore p;
trace! `PrettyPrinter.parenthesize ("parenthesizing" ++ MessageData.nest 2 (line ++ stx) ++ line ++ "using" ++ MessageData.nest 2 (line ++ p));
let c := Expr.constName? p.getAppFn;
env ← liftM getEnv;
match c >>= (parenthesizerAttribute.ext.getState env).table.find? with
| some (f::_) => do
  -- call first matching parenthesizer
  f p
| _           =>
  -- `choice` is not an actual parser, so special-case it here
  if c == some `choice then
    visitArgs $ stx.getArgs.size.forM $ fun _ => do
      stx ← getCur;
      visit (mkConst stx.getKind)
  else do
    -- (try to) unfold definition and recurse
    some p' ← liftM $ unfoldDefinition? p
      | throw $ Exception.other $ "no known parenthesizer for '" ++ toString p ++ "'";
    visit p'

open Lean.Parser

-- Macro scopes in the parenthesizer output are ultimately ignored by the pretty printer,
-- so give a trivial implementation.
instance monadQuotation : MonadQuotation ParenthesizerM := {
  getCurrMacroScope   := pure $ arbitrary _,
  getMainModule       := pure $ arbitrary _,
  withFreshMacroScope := fun α x => x,
}

def visitAntiquot : ParenthesizerM Unit := do
stx ← getCur;
if Elab.Term.Quotation.isAntiquot stx then visitArgs $ do
  -- antiquot syntax is, simplified, `syntax:maxPrec "$" "$"* antiquotExpr ":" (nonReservedSymbol name) "*"?`
  goLeft; goLeft; goLeft; -- now on `antiquotExpr`
  visit (mkConst `Lean.Parser.antiquotExpr);
  addPrecCheck maxPrec
else
  throw $ Exception.other $ "not an antiquotation"

/-- Recurse using `visit`, and parenthesize the result using `mkParen` if necessary. -/
def visitParenthesizable (mkParen : Syntax → Syntax) (prec : Nat) : ParenthesizerM Unit := do
stx ← getCur;
idx ← getIdx;
st ← get;
-- reset prec/prec and store `mkParen` for the recursive call
set { stxTrav := st.stxTrav };
adaptReader (fun (ctx : Context) => { ctx with mkParen := some mkParen }) $
  -- we assume that each node kind is produced by a 0-ary parser of the same name
  visit (mkConst stx.getKind);
{ minPrec := some minPrec, trailPrec := trailPrec, .. } ← get
  | panic! "visitParenthesizable: visited a term without tokens?!";
trace! `PrettyPrinter.parenthesize ("...precedences are " ++ fmt prec ++ " >? " ++ fmt minPrec ++ ", " ++ fmt trailPrec ++ " <=? " ++ fmt st.contPrec);
-- Should we parenthesize?
when (prec > minPrec || match trailPrec, st.contPrec with some trailPrec, some contPrec => trailPrec <= contPrec | _, _ => false) $ do {
    -- The recursive `visit` call, by the invariant, has moved to the preceding node. In order to parenthesize
    -- the original node, we must first move to the right, except if we already were at the left-most child in the first
    -- place.
    when (idx > 0) goRight;
    stx ← getCur;
    match stx.getHeadInfo, stx.getTailInfo with
    | some hi, some ti =>
      -- Move leading/trailing whitespace of `stx` outside of parentheses
      let stx := (stx.setHeadInfo { hi with leading := "".toSubstring }).setTailInfo { ti with trailing := "".toSubstring };
      let stx := mkParen stx;
      let stx := (stx.setHeadInfo { hi with trailing := "".toSubstring }).setTailInfo { ti with leading := "".toSubstring };
      setCur stx
    | _, _ => setCur (mkParen stx);
    stx ← getCur; trace! `PrettyPrinter.parenthesize ("parenthesized: " ++ stx.formatStx none);
    goLeft;
    -- after parenthesization, there is no more trailing parser
    modify (fun st => { st with contPrec := maxPrec, trailPrec := none })
};
{ trailPrec := trailPrec, .. } ← get;
-- If we already had a token at this level, keep the trailing parser. Otherwise, use the minimum of
-- `prec` and `trailPrec`.
let trailPrec := if st.visitedToken then st.trailPrec else match trailPrec with
  | some trailPrec => some (Nat.min trailPrec prec)
  | _              => some prec;
modify (fun stP => { stP with minPrec := st.minPrec, trailPrec := trailPrec })

/-- Adjust state and advance. -/
def visitToken : Parenthesizer | p => do
modify (fun st => { st with contPrec := none, visitedToken := true });
goLeft

@[builtinParenthesizer termParser]
def termParser.parenthesizer : Parenthesizer | p => visitAntiquot <|> do
stx ← getCur;
-- this can happen at `termParser <|> many1 commandParser` in `Term.stxQuot`
if stx.getKind == nullKind then
  throw $ Exception.other "BACKTRACK"
else do
  prec ← liftM $ reduceEval p.appArg!;
  visitParenthesizable (fun stx => Unhygienic.run `(($stx))) prec

@[builtinParenthesizer tacticParser]
def tacticParser.parenthesizer : Parenthesizer | p => visitAntiquot <|> do
prec ← liftM $ reduceEval p.appArg!;
visitParenthesizable (fun stx => Unhygienic.run `(tactic|($stx))) prec

@[builtinParenthesizer levelParser]
def levelParser.parenthesizer : Parenthesizer | p => visitAntiquot <|> do
prec ← liftM $ reduceEval p.appArg!;
visitParenthesizable (fun stx => Unhygienic.run `(level|($stx))) prec

@[builtinParenthesizer categoryParser]
def categoryParser.parenthesizer : Parenthesizer | p => visitAntiquot <|> do
stx ← getCur;
visit (mkConst stx.getKind)

@[builtinParenthesizer withAntiquot]
def withAntiquot.parenthesizer : Parenthesizer | p =>
visitAntiquot <|> visit (p.getArg! 1)

@[builtinParenthesizer try]
def try.parenthesizer : Parenthesizer | p =>
visit p.appArg!

@[builtinParenthesizer andthen]
def andthen.parenthesizer : Parenthesizer | p =>
visit (p.getArg! 1) *> visit (p.getArg! 0)

@[builtinParenthesizer node]
def node.parenthesizer : Parenthesizer | p => do
stx ← getCur;
k ← liftM $ reduceEval $ p.getArg! 0;
when (k != stx.getKind) $ do {
  trace! `PrettyPrinter.parenthesize.backtrack ("unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'");
  -- HACK; see `orelse.parenthesizer`
  throw $ Exception.other "BACKTRACK"
};
visitArgs $ visit p.appArg!

@[builtinParenthesizer checkPrec]
def checkPrec.parenthesizer : Parenthesizer | p => do
prec ← liftM $ reduceEval $ p.getArg! 0;
addPrecCheck prec

@[builtinParenthesizer leadingNode]
def leadingNode.parenthesizer : Parenthesizer | p => do
-- Unfold `leadingNode` as usual, but limit `contPrec` to `maxPrec-1` afterwards.
-- This is because `maxPrec-1` is the precedence of function application, which is the only way to turn a leading parser
-- into a trailing one.
some p ← liftM $ unfoldDefinition? p
  | unreachable!;
visit p;
modify $ fun st => { st with contPrec := (fun p => Nat.min (maxPrec-1) p) <$> st.contPrec }

@[builtinParenthesizer trailingNode]
def trailingNode.parenthesizer : Parenthesizer | p => do
stx ← getCur;
k ← liftM $ reduceEval $ p.getArg! 0;
prec ← liftM $ reduceEval $ p.getArg! 1;
when (k != stx.getKind) $ do {
  trace! `PrettyPrinter.parenthesize.backtrack ("unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'");
  -- HACK; see `orelse.parenthesizer`
  throw $ Exception.other "BACKTRACK"
};
visitArgs $ do {
  visit p.appArg!;
  addPrecCheck prec;
  -- After visiting the nodes actually produced by the parser passed to `trailingNode`, we are positioned on the
  -- left-most child, which is the term injected by `trailingNode` in place of the recursion. Left recursion is not an
  -- issue for the parenthesizer, so we can think of this child being produced by `termParser 0`, or whichever Pratt
  -- parser is calling us; we only need to know its `mkParen`, which we retrieve from the context.
  { mkParen := some mkParen, .. } ← read
    | panic! "trailingNode.parenthesizer called outside of visitParenthesizable call";
  visitAntiquot <|> visitParenthesizable mkParen 0
}

@[builtinParenthesizer symbol] def symbol.parenthesizer := visitToken
@[builtinParenthesizer symbolNoWs] def symbolNoWs.parenthesizer := visitToken
@[builtinParenthesizer unicodeSymbol] def unicodeSymbol.parenthesizer := visitToken

@[builtinParenthesizer identNoAntiquot] def identNoAntiquot.parenthesizer := visitToken
@[builtinParenthesizer rawIdent] def rawIdent.parenthesizer := visitToken
@[builtinParenthesizer nonReservedSymbol] def nonReservedSymbol.parenthesizer := visitToken

@[builtinParenthesizer charLitNoAntiquot] def charLitNoAntiquot.parenthesizer := visitToken
@[builtinParenthesizer strLitNoAntiquot] def strLitNoAntiquot.parenthesizer := visitToken
@[builtinParenthesizer nameLitNoAntiquot] def nameLitNoAntiquot.parenthesizer := visitToken
@[builtinParenthesizer numLitNoAntiquot] def numLitNoAntiquot.parenthesizer := visitToken
@[builtinParenthesizer fieldIdx] def fieldIdx.parenthesizer := visitToken

@[builtinParenthesizer many]
def many.parenthesizer : Parenthesizer | p => do
stx ← getCur;
visitArgs $ stx.getArgs.size.forM $ fun _ => visit (p.getArg! 0)

@[builtinParenthesizer many1] def many1.parenthesizer : Parenthesizer | p => do
stx ← getCur;
if stx.getKind == nullKind then
  visitArgs $ stx.getArgs.size.forM $ fun _ => visit (p.getArg! 0)
else
  -- can happen with `unboxSingleton = true`
  visit (p.getArg! 0)

@[builtinParenthesizer Parser.optional]
def optional.parenthesizer : Parenthesizer | p => do
visitArgs $ visit (p.getArg! 0)

@[builtinParenthesizer sepBy]
def sepBy.parenthesizer : Parenthesizer | p => do
stx ← getCur;
visitArgs $ (List.range stx.getArgs.size).reverse.forM $ fun i => visit (p.getArg! (i % 2))

@[builtinParenthesizer sepBy1] def sepBy1.parenthesizer := sepBy.parenthesizer

@[builtinParenthesizer orelse] def orelse.parenthesizer : Parenthesizer | p => do
st ← get;
-- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
-- them in turn. Uses the syntax traverser non-linearly!
catch (visit (p.getArg! 0)) $ fun e => match e with
  | Exception.other "BACKTRACK" => set st *> visit (p.getArg! 1)
  | _                           => throw e

@[builtinParenthesizer withPosition] def withPosition.parenthesizer : Parenthesizer | p => do
-- call closure with dummy position
visit $ mkApp (p.getArg! 0) (mkConst `sorryAx [levelZero])

@[builtinParenthesizer checkStackTop] def checkStackTop.parenthesizer : Parenthesizer | p => pure ()
@[builtinParenthesizer checkWsBefore] def checkWsBefore.parenthesizer : Parenthesizer | p => pure ()
@[builtinParenthesizer checkNoWsBefore] def checkNoWsBefore.parenthesizer : Parenthesizer | p => pure ()
@[builtinParenthesizer checkTailWs] def checkTailWs.parenthesizer : Parenthesizer | p => pure ()
@[builtinParenthesizer checkColGe] def checkColGe.parenthesizer : Parenthesizer | p => pure ()

open Lean.Parser.Command
@[builtinParenthesizer commentBody] def commentBody.parenthesizer := visitToken
@[builtinParenthesizer quotedSymbol] def quotedSymbol.parenthesizer := visitToken
@[builtinParenthesizer unquotedSymbol] def unquotedSymbol.parenthesizer := visitToken

end Parenthesizer

/-- Add necessary parentheses in `stx` parsed by `parser`. -/
def parenthesize (parser : Expr) (stx : Syntax) : MetaM Syntax := do
(_, st) ← Parenthesizer.visit parser {} { stxTrav := Syntax.Traverser.fromSyntax stx };
pure st.stxTrav.cur

def parenthesizeTerm := parenthesize (mkApp (mkConst `Lean.Parser.termParser) (mkNatLit 0))

def parenthesizeCommand := parenthesize (mkApp (mkConst `Lean.Parser.commandParser) (mkNatLit 0))

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `PrettyPrinter.parenthesize;
pure ()

end PrettyPrinter
end Lean
