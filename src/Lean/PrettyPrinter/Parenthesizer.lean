/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.CoreM
import Lean.KeyedDeclsAttribute
import Lean.Parser.Extension
import Lean.ParserCompiler.Attribute
import Lean.PrettyPrinter.Basic


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

namespace Lean
namespace PrettyPrinter
namespace Parenthesizer

structure Context where
  -- We need to store this `categoryParser` argument to deal with the implicit Pratt parser call in `trailingNode.parenthesizer`.
  cat : Name := Name.anonymous

structure State where
  stxTrav : Syntax.Traverser
  --- precedence and category of the current left-most trailing parser, if any; see module doc for details
  contPrec : Option Nat := none
  contCat : Name := Name.anonymous
  -- current minimum precedence in this Pratt parser call, if any; see module doc for details
  minPrec : Option Nat := none
  -- precedence and category of the trailing Pratt parser call if any; see module doc for details
  trailPrec : Option Nat := none
  trailCat : Name := Name.anonymous
  -- true iff we have already visited a token on this parser level; used for detecting trailing parsers
  visitedToken : Bool := false

end Parenthesizer

abbrev ParenthesizerM := ReaderT Parenthesizer.Context $ StateRefT Parenthesizer.State CoreM
abbrev Parenthesizer := ParenthesizerM Unit

@[inline] def ParenthesizerM.orElse (p₁ : ParenthesizerM α) (p₂ : Unit → ParenthesizerM α) : ParenthesizerM α := do
  let s ← get
  catchInternalId backtrackExceptionId
    p₁
    (fun _ => do set s; p₂ ())

instance : OrElse (ParenthesizerM α) := ⟨ParenthesizerM.orElse⟩

unsafe def mkParenthesizerAttribute : IO (KeyedDeclsAttribute Parenthesizer) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtinParenthesizer,
    name := `parenthesizer,
    descr := "Register a parenthesizer for a parser.

  [parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.",
    valueTypeName := `Lean.PrettyPrinter.Parenthesizer,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let id ← Attribute.Builtin.getId stx
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a parenthesizer for it immediately, so we just check for a declaration in this case
      if (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id then pure id
      else throwError "invalid [parenthesizer] argument, unknown syntax kind '{id}'"
  } `Lean.PrettyPrinter.parenthesizerAttribute
@[builtinInit mkParenthesizerAttribute] constant parenthesizerAttribute : KeyedDeclsAttribute Parenthesizer

abbrev CategoryParenthesizer := forall (prec : Nat), Parenthesizer

unsafe def mkCategoryParenthesizerAttribute : IO (KeyedDeclsAttribute CategoryParenthesizer) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtinCategoryParenthesizer,
    name := `categoryParenthesizer,
    descr := "Register a parenthesizer for a syntax category.

  [categoryParenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,
  which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`
  with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,
  but still be traversed for parenthesizing nested categories.",
    valueTypeName := `Lean.PrettyPrinter.CategoryParenthesizer,
    evalKey := fun _ stx => do
      let env ← getEnv
      let id ← Attribute.Builtin.getId stx
      if Parser.isParserCategory env id then pure id
      else throwError "invalid [categoryParenthesizer] argument, unknown parser category '{toString id}'"
  } `Lean.PrettyPrinter.categoryParenthesizerAttribute
@[builtinInit mkCategoryParenthesizerAttribute] constant categoryParenthesizerAttribute : KeyedDeclsAttribute CategoryParenthesizer

unsafe def mkCombinatorParenthesizerAttribute : IO ParserCompiler.CombinatorAttribute :=
  ParserCompiler.registerCombinatorAttribute
    `combinatorParenthesizer
    "Register a parenthesizer for a parser combinator.

  [combinatorParenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.
  Note that, unlike with [parenthesizer], this is not a node kind since combinators usually do not introduce their own node kinds.
  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
  with `Parenthesizer` in the parameter types."
@[builtinInit mkCombinatorParenthesizerAttribute] constant combinatorParenthesizerAttribute : ParserCompiler.CombinatorAttribute

namespace Parenthesizer

open Lean.Core
open Std.Format

def throwBacktrack {α} : ParenthesizerM α :=
throw $ Exception.internal backtrackExceptionId

instance : Syntax.MonadTraverser ParenthesizerM := ⟨{
  get       := State.stxTrav <$> get,
  set       := fun t => modify (fun st => { st with stxTrav := t }),
  modifyGet := fun f => modifyGet (fun st => let (a, t) := f st.stxTrav; (a, { st with stxTrav := t }))
}⟩

open Syntax.MonadTraverser

def addPrecCheck (prec : Nat) : ParenthesizerM Unit :=
  modify fun st => { st with contPrec := Nat.min (st.contPrec.getD prec) prec, minPrec := Nat.min (st.minPrec.getD prec) prec }

/-- Execute `x` at the right-most child of the current node, if any, then advance to the left. -/
def visitArgs (x : ParenthesizerM Unit) : ParenthesizerM Unit := do
  let stx ← getCur
  if stx.getArgs.size > 0 then
    goDown (stx.getArgs.size - 1) *> x <* goUp
  goLeft

-- Macro scopes in the parenthesizer output are ultimately ignored by the pretty printer,
-- so give a trivial implementation.
instance : MonadQuotation ParenthesizerM := {
  getCurrMacroScope   := pure arbitrary,
  getMainModule       := pure arbitrary,
  withFreshMacroScope := fun x => x,
}

/--
  Run `x` and parenthesize the result using `mkParen` if necessary.
  If `canJuxtapose` is false, we assume the category does not have a token-less juxtaposition syntax a la function application and deactivate rule 2. -/
def maybeParenthesize (cat : Name) (canJuxtapose : Bool) (mkParen : Syntax → Syntax) (prec : Nat) (x : ParenthesizerM Unit) : ParenthesizerM Unit := do
  let stx ← getCur
  let idx ← getIdx
  let st ← get
  -- reset precs for the recursive call
  set { stxTrav := st.stxTrav : State }
  trace[PrettyPrinter.parenthesize] "parenthesizing (cont := {(st.contPrec, st.contCat)}){indentD (format stx)}"
  x
  let { minPrec := some minPrec, trailPrec := trailPrec, trailCat := trailCat, .. } ← get
    | trace[PrettyPrinter.parenthesize] "visited a syntax tree without precedences?!{line ++ format stx}"
  trace[PrettyPrinter.parenthesize] (m!"...precedences are {prec} >? {minPrec}" ++ if canJuxtapose then m!", {(trailPrec, trailCat)} <=? {(st.contPrec, st.contCat)}" else "")
  -- Should we parenthesize?
  if (prec > minPrec || canJuxtapose && match trailPrec, st.contPrec with | some trailPrec, some contPrec => trailCat == st.contCat && trailPrec <= contPrec | _, _ => false) then
      -- The recursive `visit` call, by the invariant, has moved to the preceding node. In order to parenthesize
      -- the original node, we must first move to the right, except if we already were at the left-most child in the first
      -- place.
      if idx > 0 then goRight
      let mut stx ← getCur
      -- Move leading/trailing whitespace of `stx` outside of parentheses
      if let SourceInfo.original _ pos trail endPos := stx.getHeadInfo then
        stx := stx.setHeadInfo (SourceInfo.original "".toSubstring pos trail endPos)
      if let SourceInfo.original lead pos _ endPos := stx.getTailInfo then
        stx := stx.setTailInfo (SourceInfo.original lead pos "".toSubstring endPos)
      let mut stx' := mkParen stx
      if let SourceInfo.original lead pos _ endPos := stx.getHeadInfo then
        stx' := stx'.setHeadInfo (SourceInfo.original lead pos "".toSubstring endPos)
      if let SourceInfo.original _ pos trail endPos := stx.getTailInfo then
        stx' := stx'.setTailInfo (SourceInfo.original "".toSubstring pos trail endPos)
      trace[PrettyPrinter.parenthesize] "parenthesized: {stx'.formatStx none}"
      setCur stx'
      goLeft
      -- after parenthesization, there is no more trailing parser
      modify (fun st => { st with contPrec := Parser.maxPrec, contCat := cat, trailPrec := none })
  let { trailPrec := trailPrec, .. } ← get
  -- If we already had a token at this level, keep the trailing parser. Otherwise, use the minimum of
  -- `prec` and `trailPrec`.
  if st.visitedToken then
    modify fun stP => { stP with trailPrec := st.trailPrec, trailCat := st.trailCat }
  else
    let trailPrec := match trailPrec with
    | some trailPrec => Nat.min trailPrec prec
    | _              => prec
    modify fun stP => { stP with trailPrec := trailPrec, trailCat := cat }
  modify fun stP => { stP with minPrec := st.minPrec }

/-- Adjust state and advance. -/
def visitToken : Parenthesizer := do
  modify fun st => { st with contPrec := none, contCat := Name.anonymous, visitedToken := true }
  goLeft

@[combinatorParenthesizer Lean.Parser.orelse] def orelse.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer := do
  let st ← get
  -- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
  -- them in turn. Uses the syntax traverser non-linearly!
  p1 <|> p2

-- `mkAntiquot` is quite complex, so we'd rather have its parenthesizer synthesized below the actual parser definition.
-- Note that there is a mutual recursion
-- `categoryParser -> mkAntiquot -> termParser -> categoryParser`, so we need to introduce an indirection somewhere
-- anyway.
@[extern 8 "lean_mk_antiquot_parenthesizer"]
constant mkAntiquot.parenthesizer' (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parenthesizer

@[inline] def liftCoreM {α} (x : CoreM α) : ParenthesizerM α :=
  liftM x

-- break up big mutual recursion
@[extern "lean_pretty_printer_parenthesizer_interpret_parser_descr"]
constant interpretParserDescr' : ParserDescr → CoreM Parenthesizer

unsafe def parenthesizerForKindUnsafe (k : SyntaxNodeKind) : Parenthesizer := do
  if k == `missing then
    pure ()
  else
    let p ← runForNodeKind parenthesizerAttribute k interpretParserDescr'
    p

@[implementedBy parenthesizerForKindUnsafe]
constant parenthesizerForKind (k : SyntaxNodeKind) : Parenthesizer

@[combinatorParenthesizer Lean.Parser.withAntiquot]
def withAntiquot.parenthesizer (antiP p : Parenthesizer) : Parenthesizer :=
  -- TODO: could be optimized using `isAntiquot` (which would have to be moved), but I'd rather
  -- fix the backtracking hack outright.
  orelse.parenthesizer antiP p

@[combinatorParenthesizer Lean.Parser.withAntiquotSuffixSplice]
def withAntiquotSuffixSplice.parenthesizer (k : SyntaxNodeKind) (p suffix : Parenthesizer) : Parenthesizer := do
  if (← getCur).isAntiquotSuffixSplice then
    visitArgs <| suffix *> p
  else
    p

@[combinatorParenthesizer Lean.Parser.tokenWithAntiquot]
def tokenWithAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  if (← getCur).isTokenAntiquot then
    visitArgs p
  else
    p

def parenthesizeCategoryCore (cat : Name) (prec : Nat) : Parenthesizer :=
  withReader (fun ctx => { ctx with cat := cat }) do
    let stx ← getCur
    if stx.getKind == `choice then
      visitArgs $ stx.getArgs.size.forM fun _ => do
        let stx ← getCur
        parenthesizerForKind stx.getKind
    else
      withAntiquot.parenthesizer (mkAntiquot.parenthesizer' cat.toString none) (parenthesizerForKind stx.getKind)
    modify fun st => { st with contCat := cat }

@[combinatorParenthesizer Lean.Parser.categoryParser]
def categoryParser.parenthesizer (cat : Name) (prec : Nat) : Parenthesizer := do
  let env ← getEnv
  match categoryParenthesizerAttribute.getValues env cat with
  | p::_ => p prec
  -- Fall back to the generic parenthesizer.
  -- In this case this node will never be parenthesized since we don't know which parentheses to use.
  | _    => parenthesizeCategoryCore cat prec

@[combinatorParenthesizer Lean.Parser.categoryParserOfStack]
def categoryParserOfStack.parenthesizer (offset : Nat) (prec : Nat) : Parenthesizer := do
  let st ← get
  let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset)
  categoryParser.parenthesizer stx.getId prec

@[combinatorParenthesizer Lean.Parser.parserOfStack]
def parserOfStack.parenthesizer (offset : Nat) (prec : Nat := 0) : Parenthesizer := do
  let st ← get
  let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset)
  parenthesizerForKind stx.getKind

@[builtinCategoryParenthesizer term]
def term.parenthesizer : CategoryParenthesizer | prec => do
  let stx ← getCur
  -- this can happen at `termParser <|> many1 commandParser` in `Term.stxQuot`
  if stx.getKind == nullKind then
    throwBacktrack
  else do
    maybeParenthesize `term true (fun stx => Unhygienic.run `(($stx))) prec $
      parenthesizeCategoryCore `term prec

@[builtinCategoryParenthesizer tactic]
def tactic.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `tactic false (fun stx => Unhygienic.run `(tactic|($stx))) prec $
    parenthesizeCategoryCore `tactic prec

@[builtinCategoryParenthesizer level]
def level.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `level false (fun stx => Unhygienic.run `(level|($stx))) prec $
    parenthesizeCategoryCore `level prec

@[combinatorParenthesizer Lean.Parser.error]
def error.parenthesizer (msg : String) : Parenthesizer :=
  pure ()

@[combinatorParenthesizer Lean.Parser.errorAtSavedPos]
def errorAtSavedPos.parenthesizer (msg : String) (delta : Bool) : Parenthesizer :=
  pure ()

@[combinatorParenthesizer Lean.Parser.atomic]
def atomic.parenthesizer (p : Parenthesizer) : Parenthesizer :=
  p

@[combinatorParenthesizer Lean.Parser.lookahead]
def lookahead.parenthesizer (p : Parenthesizer) : Parenthesizer :=
  pure ()

@[combinatorParenthesizer Lean.Parser.notFollowedBy]
def notFollowedBy.parenthesizer (p : Parenthesizer) : Parenthesizer :=
  pure ()

@[combinatorParenthesizer Lean.Parser.andthen]
def andthen.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer :=
  p2 *> p1

@[combinatorParenthesizer Lean.Parser.node]
def node.parenthesizer (k : SyntaxNodeKind) (p : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  if k != stx.getKind then
    trace[PrettyPrinter.parenthesize.backtrack] "unexpected node kind '{stx.getKind}', expected '{k}'"
    -- HACK; see `orelse.parenthesizer`
    throwBacktrack
  visitArgs p

@[combinatorParenthesizer Lean.Parser.checkPrec]
def checkPrec.parenthesizer (prec : Nat) : Parenthesizer :=
  addPrecCheck prec

@[combinatorParenthesizer Lean.Parser.leadingNode]
def leadingNode.parenthesizer (k : SyntaxNodeKind) (prec : Nat) (p : Parenthesizer) : Parenthesizer := do
  node.parenthesizer k p
  addPrecCheck prec
  -- Limit `cont` precedence to `maxPrec-1`.
  -- This is because `maxPrec-1` is the precedence of function application, which is the only way to turn a leading parser
  -- into a trailing one.
  modify fun st => { st with contPrec := Nat.min (Parser.maxPrec-1) prec }

@[combinatorParenthesizer Lean.Parser.trailingNode]
def trailingNode.parenthesizer (k : SyntaxNodeKind) (prec lhsPrec : Nat) (p : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  if k != stx.getKind then
    trace[PrettyPrinter.parenthesize.backtrack] "unexpected node kind '{stx.getKind}', expected '{k}'"
    -- HACK; see `orelse.parenthesizer`
    throwBacktrack
  visitArgs do
    p
    addPrecCheck prec
    let ctx ← read
    modify fun st => { st with contCat := ctx.cat }
    -- After visiting the nodes actually produced by the parser passed to `trailingNode`, we are positioned on the
    -- left-most child, which is the term injected by `trailingNode` in place of the recursion. Left recursion is not an
    -- issue for the parenthesizer, so we can think of this child being produced by `termParser lhsPrec`, or whichever Pratt
    -- parser is calling us.
    categoryParser.parenthesizer ctx.cat lhsPrec

@[combinatorParenthesizer Lean.Parser.rawCh] def rawCh.parenthesizer (ch : Char) := visitToken

@[combinatorParenthesizer Lean.Parser.symbolNoAntiquot] def symbolNoAntiquot.parenthesizer (sym : String) := visitToken
@[combinatorParenthesizer Lean.Parser.unicodeSymbolNoAntiquot] def unicodeSymbolNoAntiquot.parenthesizer (sym asciiSym : String) := visitToken

@[combinatorParenthesizer Lean.Parser.identNoAntiquot] def identNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.rawIdentNoAntiquot] def rawIdentNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.identEq] def identEq.parenthesizer (id : Name) := visitToken
@[combinatorParenthesizer Lean.Parser.nonReservedSymbolNoAntiquot] def nonReservedSymbolNoAntiquot.parenthesizer (sym : String) (includeIdent : Bool) := visitToken

@[combinatorParenthesizer Lean.Parser.charLitNoAntiquot] def charLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.strLitNoAntiquot] def strLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.nameLitNoAntiquot] def nameLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.numLitNoAntiquot] def numLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.scientificLitNoAntiquot] def scientificLitNoAntiquot.parenthesizer := visitToken
@[combinatorParenthesizer Lean.Parser.fieldIdx] def fieldIdx.parenthesizer := visitToken

@[combinatorParenthesizer Lean.Parser.manyNoAntiquot]
def manyNoAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  visitArgs $ stx.getArgs.size.forM fun _ => p

@[combinatorParenthesizer Lean.Parser.many1NoAntiquot]
def many1NoAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  manyNoAntiquot.parenthesizer p

@[combinatorParenthesizer Lean.Parser.many1Unbox]
def many1Unbox.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  if stx.getKind == nullKind then
    manyNoAntiquot.parenthesizer p
  else
    p

@[combinatorParenthesizer Lean.Parser.optionalNoAntiquot]
def optionalNoAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  visitArgs p

@[combinatorParenthesizer Lean.Parser.sepByNoAntiquot]
def sepByNoAntiquot.parenthesizer (p pSep : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  visitArgs $ (List.range stx.getArgs.size).reverse.forM $ fun i => if i % 2 == 0 then p else pSep

@[combinatorParenthesizer Lean.Parser.sepBy1NoAntiquot] def sepBy1NoAntiquot.parenthesizer := sepByNoAntiquot.parenthesizer

@[combinatorParenthesizer Lean.Parser.withPosition] def withPosition.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  -- We assume the formatter will indent syntax sufficiently such that parenthesizing a `withPosition` node is never necessary
  modify fun st => { st with contPrec := none }
  p
@[combinatorParenthesizer Lean.Parser.withoutPosition] def withoutPosition.parenthesizer (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.withForbidden] def withForbidden.parenthesizer (tk : Parser.Token) (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.withoutForbidden] def withoutForbidden.parenthesizer (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.withoutInfo] def withoutInfo.parenthesizer (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.setExpected]
def setExpected.parenthesizer (expected : List String) (p : Parenthesizer) : Parenthesizer := p

@[combinatorParenthesizer Lean.Parser.incQuotDepth] def incQuotDepth.parenthesizer (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.decQuotDepth] def decQuotDepth.parenthesizer (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.suppressInsideQuot] def suppressInsideQuot.parenthesizer (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.evalInsideQuot] def evalInsideQuot.parenthesizer (declName : Name) (p : Parenthesizer) : Parenthesizer := p

@[combinatorParenthesizer Lean.Parser.checkStackTop] def checkStackTop.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkWsBefore] def checkWsBefore.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkNoWsBefore] def checkNoWsBefore.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkLinebreakBefore] def checkLinebreakBefore.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkTailWs] def checkTailWs.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkColGe] def checkColGe.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkColGt] def checkColGt.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkLineEq] def checkLineEq.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.eoi] def eoi.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.notFollowedByCategoryToken] def notFollowedByCategoryToken.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkNoImmediateColon] def checkNoImmediateColon.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkInsideQuot] def checkInsideQuot.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.checkOutsideQuot] def checkOutsideQuot.parenthesizer : Parenthesizer := pure ()
@[combinatorParenthesizer Lean.Parser.skip] def skip.parenthesizer : Parenthesizer := pure ()

@[combinatorParenthesizer Lean.Parser.pushNone] def pushNone.parenthesizer : Parenthesizer := goLeft

@[combinatorParenthesizer Lean.Parser.withOpenDecl] def withOpenDecl.parenthesizer (p : Parenthesizer) : Parenthesizer := p
@[combinatorParenthesizer Lean.Parser.withOpen] def withOpen.parenthesizer (p : Parenthesizer) : Parenthesizer := p

@[combinatorParenthesizer Lean.Parser.interpolatedStr]
def interpolatedStr.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  visitArgs $ (← getCur).getArgs.reverse.forM fun chunk =>
    if chunk.isOfKind interpolatedStrLitKind then
      goLeft
    else
      p

@[combinatorParenthesizer Lean.Parser.dbgTraceState] def dbgTraceState.parenthesizer (label : String) (p : Parenthesizer) : Parenthesizer := p

@[combinatorParenthesizer ite, macroInline] def ite {α : Type} (c : Prop) [h : Decidable c] (t e : Parenthesizer) : Parenthesizer :=
  if c then t else e

open Parser

abbrev ParenthesizerAliasValue := AliasValue Parenthesizer

builtin_initialize parenthesizerAliasesRef : IO.Ref (NameMap ParenthesizerAliasValue) ← IO.mkRef {}

def registerAlias (aliasName : Name) (v : ParenthesizerAliasValue) : IO Unit := do
  Parser.registerAliasCore parenthesizerAliasesRef aliasName v

instance : Coe Parenthesizer ParenthesizerAliasValue := { coe := AliasValue.const }
instance : Coe (Parenthesizer → Parenthesizer) ParenthesizerAliasValue := { coe := AliasValue.unary }
instance : Coe (Parenthesizer → Parenthesizer → Parenthesizer) ParenthesizerAliasValue := { coe := AliasValue.binary }

end Parenthesizer
open Parenthesizer

/-- Add necessary parentheses in `stx` parsed by `parser`. -/
def parenthesize (parenthesizer : Parenthesizer) (stx : Syntax) : CoreM Syntax := do
  trace[PrettyPrinter.parenthesize.input] "{format stx}"
  catchInternalId backtrackExceptionId
    (do
      let (_, st) ← (parenthesizer {}).run { stxTrav := Syntax.Traverser.fromSyntax stx }
      pure st.stxTrav.cur)
    (fun _ => throwError "parenthesize: uncaught backtrack exception")

def parenthesizeTerm := parenthesize $ categoryParser.parenthesizer `term 0
def parenthesizeTactic := parenthesize $ categoryParser.parenthesizer `tactic 0
def parenthesizeCommand := parenthesize $ categoryParser.parenthesizer `command 0

builtin_initialize registerTraceClass `PrettyPrinter.parenthesize

end PrettyPrinter
end Lean
