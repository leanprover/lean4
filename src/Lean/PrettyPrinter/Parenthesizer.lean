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
   parentheses, `p prec` would have parsed it as well and made it a part of `stx`). We also check that the two parsers
   are from the same syntax category.

Note that in case 2, it is also sufficient to parenthesize a *parent* node as long as the offending parser is still to
the right of that node. For example, imagine the tree structure of `(f $ fun x => x) y` without parentheses. We need to
insert *some* parentheses between `x` and `y` since the lambda body is parsed with precedence 0, while the identifier
parser for `y` has precedence `maxPrec`. But we need to parenthesize the `$` node anyway since the precedence of its
RHS (0) again is smaller than that of `y`. So it's better to only parenthesize the outer node than ending up with
`(f $ (fun x => x)) y`.

# Implementation

We transform the syntax tree and collect the necessary precedence information for that in a single traversal. The
traversal is right-to-left to cover case 2. More specifically, for every Pratt parser call, we store as monadic state
the precedence of the left-most trailing parser and the minimum precedence of any parser (`contPrec`/`minPrec`) in this
call, if any, and the precedence of the nested trailing Pratt parser call (`trailPrec`), if any. If `stP` is the state
resulting from the traversal of a Pratt parser call `p prec`, and `st` is the state of the surrounding call, we
parenthesize if `prec > stP.minPrec` (case 1) or if `stP.trailPrec <= st.contPrec` (case 2).

The traversal can be customized for each `[*Parser]` parser declaration `c` (more specifically, each `SyntaxNodeKind`
`c`) using the `[parenthesizer c]` attribute. Otherwise, a default parenthesizer will be synthesized from the used
parser combinators by recursively replacing them with declarations tagged as `[combinatorParenthesizer]` for the
respective combinator. If a called function does not have a registered combinator parenthesizer and is not reducible,
the synthesizer fails. This happens mostly at the `Parser.mk` decl, which is irreducible, when some parser primitive has
not been handled yet.

The traversal over the `Syntax` object is complicated by the fact that a parser does not produce exactly one syntax
node, but an arbitrary (but constant, for each parser) amount that it pushes on top of the parser stack. This amount can
even be zero for parsers such as `checkWsBefore`. Thus we cannot simply pass and return a `Syntax` object to and from
`visit`. Instead, we use a `Syntax.Traverser` that allows arbitrary movement and modification inside the syntax tree.
Our traversal invariant is that a parser interpreter should stop at the syntax object to the *left* of all syntax
objects its parser produced, except when it is already at the left-most child. This special case is not an issue in
practice since if there is another parser to the left that produced zero nodes in this case, it should always do so, so
there is no danger of the left-most child being processed multiple times.

Ultimately, most parenthesizers are implemented via three primitives that do all the actual syntax traversal:
`maybeParenthesize mkParen prec x` runs `x` and afterwards transforms it with `mkParen` if the above
condition for `p prec` is fulfilled. `visitToken` advances to the preceding sibling and is used on atoms. `visitArgs x`
executes `x` on the last child of the current node and then advances to the preceding sibling (of the original current
node).

-/

import Lean.Util.ReplaceExpr
import Lean.Meta.Basic
import Lean.Meta.WHNF
import Lean.KeyedDeclsAttribute
import Lean.Parser.Extension
import Lean.ParserCompiler.Attribute

namespace Lean
namespace PrettyPrinter
namespace Parenthesizer

structure Context :=
-- We need to store this `categoryParser` argument to deal with the implicit Pratt parser call in `trailingNode.parenthesizer`.
(cat : Name := Name.anonymous)

structure State :=
(stxTrav : Syntax.Traverser)
--- precedence and category of the current left-most trailing parser, if any; see module doc for details
(contPrec : Option Nat := none)
(contCat := Name.anonymous)
-- current minimum precedence in this Pratt parser call, if any; see module doc for details
(minPrec : Option Nat := none)
-- precedence of the trailing Pratt parser call if any; see module doc for details
(trailPrec : Option Nat := none)
-- true iff we have already visited a token on this parser level; used for detecting trailing parsers
(visitedToken : Bool := false)

end Parenthesizer

abbrev ParenthesizerM := ReaderT Parenthesizer.Context $ StateT Parenthesizer.State MetaM

abbrev Parenthesizer := ParenthesizerM Unit

unsafe def mkParenthesizerAttribute : IO (KeyedDeclsAttribute Parenthesizer) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinParenthesizer,
  name := `parenthesizer,
  descr := "Register a parenthesizer for a parser.

[parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.",
  valueTypeName := `Lean.PrettyPrinter.Parenthesizer,
  evalKey := fun builtin env args => match attrParamSyntaxToIdentifier args with
    | some id =>
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a parenthesizer for it immediately, so we just check for a declaration in this case
      if (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id then pure id
      else throw ("invalid [parenthesizer] argument, unknown syntax kind '" ++ toString id ++ "'")
    | none    => throw "invalid [parenthesizer] argument, expected identifier"
} `Lean.PrettyPrinter.parenthesizerAttribute
@[init mkParenthesizerAttribute] constant parenthesizerAttribute : KeyedDeclsAttribute Parenthesizer := arbitrary _

abbrev CategoryParenthesizer := forall (prec : Nat), Parenthesizer

unsafe def mkCategoryParenthesizerAttribute : IO (KeyedDeclsAttribute CategoryParenthesizer) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinCategoryParenthesizer,
  name := `categoryParenthesizer,
  descr := "Register a parenthesizer for a syntax category.

[parenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,
which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`
with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,
but still be traversed for parenthesizing nested categories.",
  valueTypeName := `Lean.PrettyPrinter.CategoryParenthesizer,
  evalKey := fun _ env args => match attrParamSyntaxToIdentifier args with
    | some id =>
      if Parser.isParserCategory env id then pure id
      else throw ("invalid [parenthesizer] argument, unknown parser category '" ++ toString id ++ "'")
    | none    => throw "invalid [parenthesizer] argument, expected identifier"
} `Lean.PrettyPrinter.categoryParenthesizerAttribute
@[init mkCategoryParenthesizerAttribute] constant categoryParenthesizerAttribute : KeyedDeclsAttribute CategoryParenthesizer := arbitrary _

unsafe def mkCombinatorParenthesizerAttribute : IO ParserCompiler.CombinatorAttribute :=
ParserCompiler.registerCombinatorAttribute
  `combinatorParenthesizer
  "Register a parenthesizer for a parser combinator.

[combinatorParenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.
Note that, unlike with [parenthesizer], this is not a node kind since combinators usually do not introduce their own node kinds.
The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
with `Parenthesizer` in the parameter types."
@[init mkCombinatorParenthesizerAttribute] constant combinatorParenthesizerAttribute : ParserCompiler.CombinatorAttribute := arbitrary _

namespace Parenthesizer

open Lean.Meta
open Lean.Format

instance ParenthesizerM.monadTraverser : Syntax.MonadTraverser ParenthesizerM := ⟨{
  get       := State.stxTrav <$> get,
  set       := fun t => modify (fun st => { st with stxTrav := t }),
  modifyGet := fun _ f => modifyGet (fun st => let (a, t) := f st.stxTrav; (a, { st with stxTrav := t })) }⟩

open Syntax.MonadTraverser

def addPrecCheck (prec : Nat) : ParenthesizerM Unit :=
modify $ fun st => { st with contPrec := Nat.min (st.contPrec.getD prec) prec, minPrec := Nat.min (st.minPrec.getD prec) prec }

/-- Execute `x` at the right-most child of the current node, if any, then advance to the left. -/
def visitArgs (x : ParenthesizerM Unit) : ParenthesizerM Unit := do
stx ← getCur;
when (stx.getArgs.size > 0) $
  goDown (stx.getArgs.size - 1) *> x <* goUp;
goLeft

-- Macro scopes in the parenthesizer output are ultimately ignored by the pretty printer,
-- so give a trivial implementation.
instance monadQuotation : MonadQuotation ParenthesizerM := {
  getCurrMacroScope   := pure $ arbitrary _,
  getMainModule       := pure $ arbitrary _,
  withFreshMacroScope := fun α x => x,
}

set_option class.instance_max_depth 100 -- TODO delete

/-- Run `x` and parenthesize the result using `mkParen` if necessary. -/
def maybeParenthesize (cat : Name) (mkParen : Syntax → Syntax) (prec : Nat) (x : ParenthesizerM Unit) : ParenthesizerM Unit := do
stx ← getCur;
idx ← getIdx;
st ← get;
-- reset precs for the recursive call
set { stxTrav := st.stxTrav : State };
trace! `PrettyPrinter.parenthesize ("parenthesizing (cont := " ++ toString (st.contPrec, st.contCat) ++ ")" ++ MessageData.nest 2 (line ++ stx));
x;
{ minPrec := some minPrec, trailPrec := trailPrec, .. } ← get
  | panic! "maybeParenthesize: visited a syntax tree without precedences?!";
trace! `PrettyPrinter.parenthesize ("...precedences are " ++ fmt prec ++ " >? " ++ fmt minPrec ++ ", " ++ fmt (trailPrec, cat) ++ " <=? " ++ fmt (st.contPrec, st.contCat));
-- Should we parenthesize?
when (prec > minPrec || match trailPrec, st.contPrec with some trailPrec, some contPrec => cat == st.contCat && trailPrec <= contPrec | _, _ => false) $ do {
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
    modify (fun st => { st with contPrec := Parser.maxPrec, contCat := cat, trailPrec := none })
};
{ trailPrec := trailPrec, .. } ← get;
-- If we already had a token at this level, keep the trailing parser. Otherwise, use the minimum of
-- `prec` and `trailPrec`.
let trailPrec := if st.visitedToken then st.trailPrec else match trailPrec with
  | some trailPrec => some (Nat.min trailPrec prec)
  | _              => some prec;
modify (fun stP => { stP with minPrec := st.minPrec, trailPrec := trailPrec })

/-- Adjust state and advance. -/
def visitToken : Parenthesizer := do
modify (fun st => { st with contPrec := none, contCat := Name.anonymous, visitedToken := true });
goLeft

@[combinatorParenthesizer Lean.Parser.orelse] def orelse.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer := do
st ← get;
-- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
-- them in turn. Uses the syntax traverser non-linearly!
catch p1 $ fun e => match e with
  | Exception.core $ Core.Exception.error _ "BACKTRACK" => set st *> p2
  | _                                                   => throw e

-- `mkAntiquot` is quite complex, so we'd rather have its parenthesizer synthesized below the actual parser definition.
-- Note that there is a mutual recursion
-- `categoryParser -> mkAntiquot -> termParser -> categoryParser`, so we need to introduce an indirection somewhere
-- anyway.
@[extern 7 "lean_mk_antiquot_parenthesizer"]
constant mkAntiquot.parenthesizer' (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parenthesizer :=
arbitrary _

def parenthesizerForKind (k : SyntaxNodeKind) : Parenthesizer := do
env ← liftM getEnv;
p::_ ← pure $ parenthesizerAttribute.getValues env k
  | liftM (throwError $ "no known parenthesizer for kind '" ++ toString k ++ "'");
p

@[combinatorParenthesizer Lean.Parser.withAntiquot]
def withAntiquot.parenthesizer (antiP p : Parenthesizer) : Parenthesizer :=
-- TODO: could be optimized using `isAntiquot` (which would have to be moved), but I'd rather
-- fix the backtracking hack outright.
orelse.parenthesizer antiP p

def parenthesizeCategoryCore (cat : Name) (prec : Nat) : Parenthesizer :=
adaptReader (fun (ctx : Context) => { ctx with cat := cat }) do
  stx ← getCur;
  if stx.getKind == `choice then
    visitArgs $ stx.getArgs.size.forM $ fun _ => do
      stx ← getCur;
      parenthesizerForKind stx.getKind
  else
    withAntiquot.parenthesizer (mkAntiquot.parenthesizer' cat.toString none) (parenthesizerForKind stx.getKind);
  modify fun st => { st with contCat := cat }

@[combinatorParenthesizer Lean.Parser.categoryParser]
def categoryParser.parenthesizer (cat : Name) (prec : Nat) : Parenthesizer := do
env ← liftM getEnv;
match categoryParenthesizerAttribute.getValues env cat with
| p::_ => p prec
-- Fall back to the generic parenthesizer.
-- In this case this node will never be parenthesized since we don't know which parentheses to use.
| _    => parenthesizeCategoryCore cat prec

@[combinatorParenthesizer Lean.Parser.categoryParserOfStack]
def categoryParserOfStack.parenthesizer (offset : Nat) (prec : Nat) : Parenthesizer := do
st ← get;
let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset);
categoryParser.parenthesizer stx.getId prec

@[builtinCategoryParenthesizer term]
def term.parenthesizer : CategoryParenthesizer | prec => do
stx ← getCur;
-- this can happen at `termParser <|> many1 commandParser` in `Term.stxQuot`
if stx.getKind == nullKind then
  liftM $ throwError "BACKTRACK"
else do
  maybeParenthesize `term (fun stx => Unhygienic.run `(($stx))) prec $
    parenthesizeCategoryCore `term prec

@[builtinCategoryParenthesizer tactic]
def tactic.parenthesizer : CategoryParenthesizer | prec => do
maybeParenthesize `tactic (fun stx => Unhygienic.run `(tactic|($stx))) prec $
  parenthesizeCategoryCore `tactic prec

@[builtinCategoryParenthesizer level]
def level.parenthesizer : CategoryParenthesizer | prec => do
maybeParenthesize `level (fun stx => Unhygienic.run `(level|($stx))) prec $
  parenthesizeCategoryCore `level prec

@[combinatorParenthesizer Lean.Parser.try]
def try.parenthesizer (p : Parenthesizer) : Parenthesizer :=
p

@[combinatorParenthesizer Lean.Parser.lookahead]
def lookahead.parenthesizer (p : Parenthesizer) : Parenthesizer :=
p

@[combinatorParenthesizer Lean.Parser.andthen]
def andthen.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer :=
p2 *> p1

@[combinatorParenthesizer Lean.Parser.node]
def node.parenthesizer (k : SyntaxNodeKind) (p : Parenthesizer) : Parenthesizer := do
stx ← getCur;
when (k != stx.getKind) $ do {
  trace! `PrettyPrinter.parenthesize.backtrack ("unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'");
  -- HACK; see `orelse.parenthesizer`
  liftM $ throwError "BACKTRACK"
};
visitArgs p

@[combinatorParenthesizer Lean.Parser.checkPrec]
def checkPrec.parenthesizer (prec : Nat) : Parenthesizer :=
addPrecCheck prec

@[combinatorParenthesizer Lean.Parser.leadingNode]
def leadingNode.parenthesizer (k : SyntaxNodeKind) (prec : Nat) (p : Parenthesizer) : Parenthesizer := do
node.parenthesizer k p;
addPrecCheck prec;
-- Limit `cont` precedence to `maxPrec-1`.
-- This is because `maxPrec-1` is the precedence of function application, which is the only way to turn a leading parser
-- into a trailing one.
modify fun st => { st with contPrec := Nat.min (Parser.maxPrec-1) prec }

@[combinatorParenthesizer Lean.Parser.trailingNode]
def trailingNode.parenthesizer (k : SyntaxNodeKind) (prec : Nat) (p : Parenthesizer) : Parenthesizer := do
stx ← getCur;
when (k != stx.getKind) $ do {
  trace! `PrettyPrinter.parenthesize.backtrack ("unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'");
  -- HACK; see `orelse.parenthesizer`
  liftM $ throwError "BACKTRACK"
};
visitArgs $ do {
  p;
  addPrecCheck prec;
  ctx ← read;
  modify fun st => { st with contCat := ctx.cat };
  -- After visiting the nodes actually produced by the parser passed to `trailingNode`, we are positioned on the
  -- left-most child, which is the term injected by `trailingNode` in place of the recursion. Left recursion is not an
  -- issue for the parenthesizer, so we can think of this child being produced by `termParser 0`, or whichever Pratt
  -- parser is calling us.
  categoryParser.parenthesizer ctx.cat 0
}

@[combinatorParenthesizer Lean.Parser.symbol] def symbol.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.symbolNoWs] def symbolNoWs.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.unicodeSymbol] def unicodeSymbol.parenthesizer := visitToken

@[combinatorParenthesizer Lean.Parser.identNoAntiquot] def identNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.rawIdent] def rawIdent.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.identEq] def identEq.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.nonReservedSymbol] def nonReservedSymbol.parenthesizer := visitToken

@[combinatorParenthesizer Lean.Parser.charLitNoAntiquot] def charLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.strLitNoAntiquot] def strLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.nameLitNoAntiquot] def nameLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.numLitNoAntiquot] def numLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.fieldIdx] def fieldIdx.parenthesizer := visitToken

@[combinatorParenthesizer Lean.Parser.many]
def many.parenthesizer (p : Parenthesizer) : Parenthesizer := do
stx ← getCur;
visitArgs $ stx.getArgs.size.forM fun _ => p

@[combinatorParenthesizer Lean.Parser.many1]
def many1.parenthesizer (p : Parenthesizer) : Parenthesizer := do
stx ← getCur;
if stx.getKind == nullKind then
  many.parenthesizer p
else
  -- can happen with `unboxSingleton = true`
  p

@[combinatorParenthesizer Lean.Parser.optional]
def optional.parenthesizer (p : Parenthesizer) : Parenthesizer := do
visitArgs p

@[combinatorParenthesizer Lean.Parser.sepBy]
def sepBy.parenthesizer (p pSep : Parenthesizer) : Parenthesizer := do
stx ← getCur;
visitArgs $ (List.range stx.getArgs.size).reverse.forM $ fun i => if i % 2 == 0 then p else pSep

@[combinatorParenthesizer Lean.Parser.sepBy1] def sepBy1.parenthesizer := sepBy.parenthesizer

@[combinatorParenthesizer Lean.Parser.withPosition] def withPosition.parenthesizer (p : Position → Parenthesizer) : Parenthesizer := do
-- call closure with dummy position
p ⟨0, 0⟩

@[combinatorParenthesizer Lean.Parser.setExpected]
def setExpected.parenthesizer (expected : List String) (p : Parenthesizer) : Parenthesizer :=
p

@[combinatorParenthesizer Lean.Parser.toggleInsideQuot]
def toggleInsideQuot.parenthesizer (p : Parenthesizer) : Parenthesizer :=
p

@[combinatorParenthesizer Lean.Parser.checkStackTop] def checkStackTop.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkWsBefore] def checkWsBefore.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkNoWsBefore] def checkNoWsBefore.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkTailWs] def checkTailWs.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkColGe] def checkColGe.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkNoImmediateColon] def checkNoImmediateColon.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkInsideQuot] def checkInsideQuot.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkOutsideQuot] def checkOutsideQuot.parenthesizer : Parenthesizer := pure ()

@[combinatorParenthesizer Lean.Parser.pushNone] def pushNone.parenthesizer : Parenthesizer := goLeft

@[combinatorParenthesizer Lean.Parser.quotedSymbol] def quotedSymbol.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.unquotedSymbol] def unquotedSymbol.parenthesizer := visitToken

@[combinatorParenthesizer ite, macroInline] def ite {α : Type} (c : Prop) [h : Decidable c] (t e : Parenthesizer) : Parenthesizer :=
if c then t else e

-- replace all references of `Parser` with `Parenthesizer` as a first approximation
def preprocessParserBody (e : Expr) : Expr :=
e.replace fun e => if e.isConstOf `Lean.Parser.Parser then mkConst `Lean.PrettyPrinter.Parenthesizer else none

-- translate an expression of type `Parser` into one of type `Parenthesizer`
partial def compileParserBody : Expr → MetaM Expr | e => do
e ← whnfCore e;
match e with
| e@(Expr.lam _ _ _ _)     => Meta.lambdaTelescope e fun xs b => compileParserBody b >>= Meta.mkLambda xs
| e@(Expr.fvar _ _)        => pure e
| _ => do
  let fn := e.getAppFn;
  Expr.const c _ _ ← pure fn
    | liftM (throwError $ "call of unknown parser at '" ++ toString e ++ "'");
  let args := e.getAppArgs;
  -- call the parenthesizer `p` with (a prefix of) the arguments of `e`, recursing for arguments
  -- of type `Parenthesizer` (i.e. formerly `Parser`)
  let mkCall (p : Name) := do {
    ty ← inferType (mkConst p);
    Meta.forallTelescope ty fun params _ =>
      params.foldlM₂ (fun p param arg => do
        paramTy ← inferType param;
        resultTy ← Meta.forallTelescope paramTy fun _ b => pure b;
        arg ← if resultTy.isConstOf `Lean.PrettyPrinter.Parenthesizer then compileParserBody arg
          else pure arg;
        pure $ mkApp p arg)
        (mkConst p)
        e.getAppArgs
  };
  env ← getEnv;
  match combinatorParenthesizerAttribute.getDeclFor env c with
  | some p => mkCall p
  | none   => do
    let parenthesizerDeclName := c ++ `parenthesizer;
    cinfo ← getConstInfo c;
    resultTy ← Meta.forallTelescope cinfo.type fun _ b => pure b;
    if resultTy.isConstOf `Lean.Parser.TrailingParser || resultTy.isConstOf `Lean.Parser.Parser then do
      -- synthesize a new `[combinatorParenthesizer]`
      some value ← pure cinfo.value?
        | liftM (throwError $ "don't know how to generate parenthesizer for non-definition '" ++ toString e ++ "'");
      value ← compileParserBody $ preprocessParserBody value;
      ty ← Meta.forallTelescope cinfo.type fun params _ =>
        params.foldrM (fun param ty => do
          paramTy ← inferType param;
          paramTy ← Meta.forallTelescope paramTy fun _ b => pure $
            if b.isConstOf `Lean.Parser.Parser then mkConst `Lean.PrettyPrinter.Parenthesizer
            else b;
          pure $ mkForall `_ BinderInfo.default paramTy ty)
          (mkConst `Lean.PrettyPrinter.Parenthesizer);
      let decl := Declaration.defnDecl { name := parenthesizerDeclName, lparams := [],
        type := ty, value := value, hints := ReducibilityHints.opaque, isUnsafe := false };
      env ← getEnv;
      env ← match env.addAndCompile {} decl with
      | Except.ok    env => pure env
      | Except.error kex => liftM (throwError $ toString $ fmt $ kex.toMessageData {});
      setEnv $ combinatorParenthesizerAttribute.setDeclFor env c parenthesizerDeclName;
      mkCall parenthesizerDeclName
    else do
      -- if this is a generic function, e.g. `HasAndthen.andthen`, it's easier to just unfold it until we are
      -- back to parser combinators
      some e' ← liftM $ unfoldDefinition? e
        | liftM (throwError $ "don't know how to generate parenthesizer for non-parser combinator '" ++ e ++ "'");
      compileParserBody e'

/-- Compile the given declaration into a `[builtinParenthesizer declName]` or `[parenthesizer declName]`. -/
def compileParser (env : Environment) (declName : Name) (builtin : Bool) : IO Environment := do
-- This will also tag the declaration as a `[combinatorParenthesizer declName]` in case the parser is used by other parsers.
-- Note that simply having `[(builtin)Parenthesizer]` imply `[combinatorParenthesizer]` is not ideal since builtin
-- attributes are active only in the next stage, while `[combinatorParenthesizer]` is active immediately (since we never
-- call them at compile time but only reference them).
(env, Expr.const parenthesizerDeclName _ _) ← ((compileParserBody (mkConst declName)).run).run' env
  | unreachable!;
-- We assume that for tagged parsers, the kind is equal to the declaration name. This is automatically true for parsers
-- using `parser!` or `syntax`.
let kind := declName;
env.addAttribute parenthesizerDeclName (if builtin then `builtinParenthesizer else `parenthesizer)
  (mkNullNode #[mkIdent kind])

unsafe def mkParenthesizerOfConstantUnsafe (constName : Name) (compileParenthesizerDescr : ParserDescr → StateT Environment IO Parenthesizer)
    : StateT Environment IO Parenthesizer :=
fun env => match env.find? constName with
| none      => throw $ IO.userError ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  if info.type.isConstOf `Lean.Parser.TrailingParser || info.type.isConstOf `Lean.Parser.Parser then
    match parenthesizerAttribute.getValues env constName with
    | p::_ => pure (p, env)
    | _    => do
      env ← compileParser env constName /- builtin -/ false;
      pure (parenthesizerForKind constName, env)
  else do
    d ← IO.ofExcept $ env.evalConst TrailingParserDescr constName;
    compileParenthesizerDescr d env

@[implementedBy mkParenthesizerOfConstantUnsafe]
constant mkParenthesizerOfConstantAux (constName : Name) (compileParenthesizerDescr : ParserDescr → StateT Environment IO Parenthesizer)
    : StateT Environment IO Parenthesizer :=
arbitrary _

unsafe def compileParenthesizerDescr : ParserDescr → StateT Environment IO Parenthesizer
| ParserDescr.andthen d₁ d₂                       => andthen.parenthesizer <$> compileParenthesizerDescr d₁ <*> compileParenthesizerDescr d₂
| ParserDescr.orelse d₁ d₂                        => orelse.parenthesizer <$> compileParenthesizerDescr d₁ <*> compileParenthesizerDescr d₂
| ParserDescr.optional d                          => optional.parenthesizer <$> compileParenthesizerDescr d
| ParserDescr.lookahead d                         => lookahead.parenthesizer <$> compileParenthesizerDescr d
| ParserDescr.try d                               => try.parenthesizer <$> compileParenthesizerDescr d
| ParserDescr.many d                              => many.parenthesizer <$> compileParenthesizerDescr d
| ParserDescr.many1 d                             => many1.parenthesizer <$> compileParenthesizerDescr d
| ParserDescr.sepBy d₁ d₂                         => sepBy.parenthesizer <$> compileParenthesizerDescr d₁ <*> compileParenthesizerDescr d₂
| ParserDescr.sepBy1 d₁ d₂                        => sepBy1.parenthesizer <$> compileParenthesizerDescr d₁ <*> compileParenthesizerDescr d₂
| ParserDescr.node k prec d                       => leadingNode.parenthesizer k prec <$> compileParenthesizerDescr d
| ParserDescr.trailingNode k prec d               => trailingNode.parenthesizer k prec <$> compileParenthesizerDescr d
| ParserDescr.symbol tk                           => pure $ symbol.parenthesizer
| ParserDescr.numLit                              => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "numLit" `numLit) numLitNoAntiquot.parenthesizer
| ParserDescr.strLit                              => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "strLit" `strLit) strLitNoAntiquot.parenthesizer
| ParserDescr.charLit                             => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "charLit" `charLit) charLitNoAntiquot.parenthesizer
| ParserDescr.nameLit                             => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "nameLit" `nameLit) nameLitNoAntiquot.parenthesizer
| ParserDescr.ident                               => pure $ withAntiquot.parenthesizer (mkAntiquot.parenthesizer' "ident" `ident) identNoAntiquot.parenthesizer
| ParserDescr.nonReservedSymbol tk includeIdent   => pure $ nonReservedSymbol.parenthesizer
| ParserDescr.parser constName                    => do
  env ← get;
  p ← match combinatorParenthesizerAttribute.getDeclFor env constName with
  | some p => pure p
  | none   => do {
    (env, Expr.const p _ _) ← liftM $ ((compileParserBody (mkConst constName)).run).run' env
      | unreachable!;
    set env;
    pure p
  };
  env ← get;
  liftM $ IO.ofExcept $ env.evalConstCheck Parenthesizer `Lean.PrettyPrinter.Parenthesizer p
| ParserDescr.cat catName prec                    => pure $ categoryParser.parenthesizer catName prec

unsafe def addParenthesizerFromConstantUnsafe (env : Environment) (constName : Name) : IO Environment := do
(p, env) ← match env.find? constName with
| none      => throw $ IO.userError ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  if info.type.isConstOf `Lean.Parser.TrailingParser || info.type.isConstOf `Lean.Parser.Parser then
    match parenthesizerAttribute.getValues env constName with
    | p::_ => pure (p, env)
    | _    => do
      env ← compileParser env constName /- builtin -/ false;
      pure (parenthesizerForKind constName, env)
  else do {
    d ← IO.ofExcept $ env.evalConst TrailingParserDescr constName;
    compileParenthesizerDescr d env
  };
-- Register parenthesizer without exporting it to the .olean file. It will be re-interpreted and registered
-- when the parser is imported.
pure $ parenthesizerAttribute.ext.modifyState env fun st => { st with table := st.table.insert constName p }

@[implementedBy addParenthesizerFromConstantUnsafe]
constant addParenthesizerFromConstant (env : Environment) (constName : Name) : IO Environment := arbitrary _

end Parenthesizer
open Parenthesizer

/-- Add necessary parentheses in `stx` parsed by `parser`. -/
def parenthesize (parenthesizer : Parenthesizer) (stx : Syntax) : MetaM Syntax := Meta.withAtLeastTransparency Meta.TransparencyMode.default do
(_, st) ← parenthesizer {} { stxTrav := Syntax.Traverser.fromSyntax stx };
pure st.stxTrav.cur

def parenthesizeTerm := parenthesize $ categoryParser.parenthesizer `term 0
def parenthesizeCommand := parenthesize $ categoryParser.parenthesizer `command 0

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `PrettyPrinter.parenthesize;
pure ()

end PrettyPrinter
end Lean
