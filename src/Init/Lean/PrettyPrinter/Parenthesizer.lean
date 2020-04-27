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

Usages of a parser defined via `prattParser` in general have the form `p rbp`, where `rbp` is the right-binding power.
Recall that a Pratt parser greedily parses a leading token with precedence at least `rbp` (otherwise it fails) followed
by zero or more trailing tokens with precedence *higher* than `rbp`. Thus we should parenthesize a syntax node `stx`
produced by `p rbp` if

1. the left-most token in `stx` has precedence < `rbp`, or
2. the left-most token to *the right of* `stx` has precedence > `rbp` (because without parentheses, `p rbp` would have
   parsed it as well and made it a part of `stx`).

Note that in case 2, it is also sufficient to parenthesize a *parent* node as long as the offending token is still to
the right of that node. For example, imagine the tree structure of `(f $ fun x => x) y` without parentheses. We need to
insert *some* parentheses between `x` and `y` since the lambda body is parse with precedence 0, while `y` as an
identifier has precedence `appPrec`. But we need to parenthesize the `$` node anyway since the precedence of its
RHS (0) again is smaller than that of `y`. So it's better to only parenthesize the outer node than ending up with
`(f $ (fun x => x)) y`.

Unfortunately, we cannot determine the precedence of a token just by looking at the syntax tree because it can actually
have different precedences in different contexts (e.g. because of whitespace sensitivity). Thus we need to look at the
parser that produced the token as well.

# Implementation

We transform the syntax tree and collect the necessary precedence information for that in a single traversal over the
syntax tree and the parser (as a `Lean.Expr`) that produced it. The traversal is right-to-left to cover case 2. More
specifically, for every Pratt parser call, we store as monadic state the precedence of the (currently) last visited
token (`lbp`), if any, and the precedence of the nested trailing Pratt parser call (`trailRbp`), if any. If `stP` is the
state resulting from the traversal of a Pratt parser call `p rbp`, and `st` is the state of the surrounding call, we
parenthesize if `rbp > stP.lbp` (case 1) or if `stP.trailRbp < st.lbp` (case 2).

The primary traversal is over the parser `Expr`. The `visit` function takes such a parser and, if it is the application
of a constant `c`, looks for a `[parenthesizer c]` declaration. If it exists, we run it, which might again call `visit`.
Otherwise, we do a single step of reduction at the head of the expression (with `default` reducibility) and try again.
If the reduction is stuck, we fail. This happens mostly at the `Parser.mk` decl, which is irreducible, when some parser
primitive has not been handled yet. You can think of this traversal as a special-case, customized `Expr` interpreter.

The traversal over the `Syntax` object is complicated by the fact that a parser does not produce exactly one syntax
node, but an arbitrary (but constant, for each parser) amount that it pushes on top of the parser stack. This amount can
even be zero for parsers such as `checkWsBefore`. Thus we cannot simply pass and return a `Syntax` object to and from
`visit`. Instead, we use a `Syntax.Traverser` that allows arbitrary movement and modification inside the syntax tree.
Our traversal invariant is that a parser interpreter should stop at the node to the *left* of all nodes its parser
produced, except when it is already at the left-most child. This special case is not an issue in practice since if there
is another parser to the left that produced zero nodes in this case, it should always do so, so there is no danger of
the left-most child being processed multiple times.

Ultimately, most parenthesizers are implemented via three primitives that do all the actual syntax traversal:
`visitParenthesizable mkParen rbp` recurses on the current node and afterwards transforms it with `mkParen` if the above
condition for `p rbp` is fulfilled. `visitToken lbp` does not recurse but updates the current `lbp` and advances one
node to the left. `visitArgs x` executes `x` on the right-most child of the current node and then advances one node
to the left (of the original current node).
-/

prelude
import Init.Lean.Parser
import Init.Lean.Elab.Command
import Init.Lean.Delaborator

namespace Lean
namespace Syntax

/--
Represents a cursor into a syntax tree that can be read, written, and advanced down/up/left/right.
If the `Traverser` is used linearly, updates are linear in the `Syntax` object as well.
-/
structure Traverser :=
(cur     : Syntax)
(parents : Array Syntax)
(idxs    : Array Nat)

namespace Traverser

def fromSyntax (stx : Syntax) : Traverser :=
⟨stx, #[], #[]⟩

def setCur (t : Traverser) (stx : Syntax) : Traverser :=
{ t with cur := stx }

/-- Advance to the `idx`-th child of the current node. -/
def down (t : Traverser) (idx : Nat) : Traverser :=
{ cur := t.cur.getArg idx, parents := t.parents.push $ t.cur.setArg idx (arbitrary _), idxs := t.idxs.push idx }

/-- Advance to the parent of the current node, if any. -/
def up (t : Traverser) : Traverser :=
if t.parents.size > 0 then
  { cur := t.parents.back.setArg t.idxs.back t.cur, parents := t.parents.pop, idxs := t.idxs.pop }
else t

/-- Advance to the left sibling of the current node, if any. -/
def left (t : Traverser) : Traverser :=
if t.idxs.size > 0 && t.idxs.back > 0 then
  t.up.down (t.idxs.back - 1)
else t

/-- Advance to the right sibling of the current node, if any. -/
def right (t :Traverser) : Traverser :=
if t.idxs.size > 0 && t.idxs.back + 1 < t.parents.back.getArgs.size then
  t.up.down (t.idxs.back + 1)
else t

end Traverser

/-- Monad class that gives read/write access to a `Traverser`. -/
class MonadTraverser (m : Type → Type) :=
(st : MonadState Traverser m)

namespace MonadTraverser

variables {m : Type → Type} [Monad m] [t : MonadTraverser m]

def getCur : m Syntax := Traverser.cur <$> t.st.get
def setCur (stx : Syntax) : m Unit := @modify _ _ t.st (fun t => t.setCur stx)
def goDown (idx : Nat)    : m Unit := @modify _ _ t.st (fun t => t.down idx)
def goUp                  : m Unit := @modify _ _ t.st (fun t => t.up)
def goLeft                : m Unit := @modify _ _ t.st (fun t => t.left)
def goRight               : m Unit := @modify _ _ t.st (fun t => t.right)

def getIdx : m Nat := do
st ← t.st.get;
pure st.idxs.back

end MonadTraverser
end Syntax

namespace PrettyPrinter
namespace Parenthesizer

structure Context :=
-- We need to store this argument of `visitParenthesizable` to deal with the implicit Pratt parser call in
-- `trailingNode.parenthesizer`.
(mkParen : Option (Syntax → Syntax) := none)

structure State :=
(stxTrav : Syntax.Traverser)
-- precedence of the current left-most token if any; see module doc for details
(lbp      : Option Nat := none)
-- precedence of the trailing Pratt parser call if any; see module doc for details
(trailRbp : Option Nat := none)

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
| _           => do
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

/-- Recurse using `visit`, and parenthesize the result using `mkParen` if necessary. -/
def visitParenthesizable (mkParen : Syntax → Syntax) (rbp : Nat) : ParenthesizerM Unit := do
stx ← getCur;
idx ← getIdx;
⟨t, lbp, trailRbp⟩ ← get;
-- reset lbp/rbp and store `mkParen` for the recursive call
set { stxTrav := t };
adaptReader (fun (ctx : Context) => { ctx with mkParen := some mkParen }) $
  -- we assume that each node kind is produced by a 0-ary parser of the same name
  visit (mkConst stx.getKind);
⟨_, some lbp', trailRbp'⟩ ← get
  | panic! "visitParenthesizable: visited a term without tokens?!";
trace! `PrettyPrinter.parenthesize ("...precedences are " ++ fmt rbp ++ " >? " ++ fmt lbp' ++ ", " ++ fmt trailRbp' ++ " <? " ++ fmt lbp);
-- Should we parenthesize?
trailRbp' ← if rbp > lbp' || (match trailRbp', lbp with some trailRbp', some lbp => trailRbp' < lbp | _, _ => false) then do
    -- The recursive `visit` call, by the invariant, has moved to the next node to the left. In order to parenthesize
    -- the original node, we must first move to the right, except if we already were at the left-most child in the first
    -- place.
    when (idx > 0) goRight;
    setCur (mkParen stx);
    goLeft;
    -- after parenthesization, there is no more trailing parser
    pure none
  else pure trailRbp';
-- If we already had a token at this level (`lbp ≠ none`), keep the trailing parser. Otherwise, use the minimum of
-- `rbp` and `trailRbp'`.
let trailRbp := match trailRbp', lbp with
  | _,              some _ => trailRbp
  | some trailRbp', _      => some (Nat.min trailRbp' rbp)
  | _,              _      => some rbp;
modify (fun st => { st with lbp := lbp' <|> lbp, trailRbp := trailRbp })

/-- Set token precedence and advance to the left. -/
def visitToken (lbp : Nat) : ParenthesizerM Unit := do
modify (fun st => { st with lbp := lbp });
goLeft

/-- Execute `x` at the right-most child of the current node, if any, then advance to the left. -/
def visitArgs (x : ParenthesizerM Unit) : ParenthesizerM Unit := do
stx ← getCur;
when (stx.getArgs.size > 0) $
  goDown (stx.getArgs.size - 1) *> x <* goUp;
goLeft

def evalNat (e : Expr) : ParenthesizerM Nat := do
e ← liftM $ whnf e;
some n ← pure $ Meta.evalNat e
  | throw $ Exception.other $ "failed to evaluate Nat argument: " ++ toString e;
pure n

def evalOptPrec (e : Expr) : ParenthesizerM Nat := do
e ← liftM $ whnf e;
match e.getAppFn.constName? with
| some `Option.none => pure 0
| some `Option.some => evalNat e.appArg!
| _ => throw $ Exception.other $ "failed to evaluate precedence: " ++ toString e

def evalString (e : Expr) : ParenthesizerM String := do
Expr.lit (Literal.strVal s) _ ← liftM $ whnf e
  | throw $ Exception.other $ "failed to evaluate String argument: " ++ toString e;
pure s

partial def evalName : Expr → ParenthesizerM Name | e => do
e ← liftM $ whnf e;
if e.isAppOfArity `Lean.Name.anonymous 0 then
  pure Name.anonymous
else if e.isAppOfArity `Lean.Name.str 3 then do
  n ← evalName $ e.getArg! 0;
  s ← evalString $ e.getArg! 1;
  pure $ mkNameStr n s
else if e.isAppOfArity `Lean.Name.num 3 then do
  n ← evalName $ e.getArg! 0;
  u ← evalNat $ e.getArg! 1;
  pure $ mkNameNum n u
else
  throw $ Exception.other $ "failed to evaluate Name argument: " ++ toString e

@[builtinParenthesizer termParser]
def termParser.parenthesizer : Parenthesizer | p => do
lbp ← evalNat p.appArg!;
visitParenthesizable (fun stx => Unhygienic.run `(($stx))) lbp

@[builtinParenthesizer levelParser]
def levelParser.parenthesizer : Parenthesizer | p => do
lbp ← evalNat p.appArg!;
visitParenthesizable (fun stx => Unhygienic.run `(level|($stx))) lbp

@[builtinParenthesizer withAntiquot]
def withAntiquot.parenthesizer : Parenthesizer | p =>
visit (p.getArg! 1)

@[builtinParenthesizer try]
def try.parenthesizer : Parenthesizer | p =>
visit p.appArg!

@[builtinParenthesizer andthen]
def andthen.parenthesizer : Parenthesizer | p =>
visit (p.getArg! 1) *> visit (p.getArg! 0)

@[builtinParenthesizer node]
def node.parenthesizer : Parenthesizer | p => do
stx ← getCur;
k ← evalName $ p.getArg! 0;
when (k != stx.getKind) $
  --throw $ Exception.other $ "unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'";
  -- HACK; see `orelse.parenthesizer`
  throw $ Exception.other "BACKTRACK";
visitArgs $ visit p.appArg!

@[builtinParenthesizer trailingNode]
def trailingNode.parenthesizer : Parenthesizer | p => do
stx ← getCur;
k ← evalName $ p.getArg! 0;
when (k != stx.getKind) $
  --throw $ Exception.other $ "unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'";
  -- HACK; see `orelse.parenthesizer`
  throw $ Exception.other "BACKTRACK";
visitArgs $ do {
  visit p.appArg!;
  -- After visiting the node actually produced by the parser passed to `trailingNode`, we are positioned on the
  -- left-most child, which is the term injected by `trailingNode` in place of the recursion. Left recursion is not an
  -- issue for the parenthesizer, so we can think of this child being produced by `termParser 0`, or whichever Pratt
  -- parser is calling us; we only need to know its `mkParen`, which we retrieve from the context. Since the left-most
  -- child was not actually part of the input to this parser, we should reset the `lbp` after processing it. We also
  -- need to decrement it by 1 to acommodate the difference between handling of leading and trailing tokens.
  some lbp ← State.lbp <$> get
    | panic! "trailingNode.parenthesizer: visited a trailing term without tokens?!";
  { mkParen := some mkParen, .. } ← read
    | panic! "trailingNode.parenthesizer called outside of visitParenthesizable call";
  visitParenthesizable mkParen 0;
  modify (fun st => { st with lbp := some (lbp - 1) })
}

@[builtinParenthesizer symbolAux]
def symbolAux.parenthesizer : Parenthesizer | p =>
evalOptPrec p.appArg! >>= visitToken

@[builtinParenthesizer symbolNoWsAux] def symbolNoWsAux.parenthesizer := symbolAux.parenthesizer
@[builtinParenthesizer unicodeSymbol] def unicodeSymbol.parenthesizer := symbolAux.parenthesizer

@[builtinParenthesizer identNoAntiquot]
def identNoAntiquot.parenthesizer : Parenthesizer | p =>
visitToken appPrec

@[builtinParenthesizer charLitNoAntiquot] def charLitNoAntiquot.parenthesizer := identNoAntiquot.parenthesizer
@[builtinParenthesizer strLitNoAntiquot] def strLitNoAntiquot.parenthesizer := identNoAntiquot.parenthesizer
@[builtinParenthesizer nameLitNoAntiquot] def nameLitNoAntiquot.parenthesizer := identNoAntiquot.parenthesizer
@[builtinParenthesizer numLitNoAntiquot] def numLitNoAntiquot.parenthesizer := identNoAntiquot.parenthesizer
@[builtinParenthesizer fieldIdx] def fieldIdx.parenthesizer := identNoAntiquot.parenthesizer

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
visitArgs $ (List.range stx.getArgs.size).forM $ fun i => visit (p.getArg! (i % 2))

@[builtinParenthesizer sepBy1] def sepBy1.parenthesizer := sepBy.parenthesizer

@[builtinParenthesizer orelse] def orelse.parenthesizer : Parenthesizer | p => do
st ← get;
-- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
-- them in turn. Uses the syntax traverser non-linearly!
catch (visit (p.getArg! 0)) $ fun e => match e with
  | Exception.other "BACKTRACK" => set st *> visit (p.getArg! 1)
  | _                           => throw e

@[builtinParenthesizer checkStackTop] def checkStackTop.parenthesizer : Parenthesizer | p => pure ()
@[builtinParenthesizer checkWsBefore] def checkWsBefore.parenthesizer : Parenthesizer | p => pure ()
@[builtinParenthesizer checkNoWsBefore] def checkNoWsBefore.parenthesizer : Parenthesizer | p => pure ()
@[builtinParenthesizer checkTailWs] def checkTailWs.parenthesizer : Parenthesizer | p => pure ()


section
open Lean.Parser.Term
def depArrow' := leadingNode `Lean.Parser.Term.depArrow $ bracketedBinder true >> unicodeSymbol " → " " -> " >> termParser
end

/-
  `depArrow` is defined as
  ```
  parser! bracketedBinder true >> checkRBPGreater 25 "expected parentheses around dependent arrow" >> unicodeSymbol " → " " -> " >> termParser
  ```
  There is no generally sensible parenthesizer implementation for `checkRBPGreater`, so we special-case the entire
  parser by ignoring `checkRBPGreater` and lowering the result LBP to 25 (instead of the LBP of `bracketedBinder`, i.e.
  `appPrec`). Thus terms such as `f ((a : _) -> b)` will be reparenthesized correctly since the new LBP is now lower than
  the surrounding RBP (`appPrec`). -/
@[builtinParenthesizer Term.depArrow]
def depArrow.parenthesizer : Parenthesizer | p => do
visit (mkConst `Lean.PrettyPrinter.Parenthesizer.depArrow');
modify $ fun st => { st with lbp := some 25 }

end Parenthesizer

/-- Add necessary parentheses in `stx` parsed by `parser`. -/
def parenthesize (parser : Expr) (stx : Syntax) : MetaM Syntax := do
(_, st) ← Parenthesizer.visit parser {} { stxTrav := Syntax.Traverser.fromSyntax stx };
pure st.stxTrav.cur

def parenthesizeTerm := parenthesize (mkApp (mkConst `Lean.Parser.termParser) (mkNatLit 0))

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `PrettyPrinter.parenthesize;
pure ()

end PrettyPrinter
end Lean
