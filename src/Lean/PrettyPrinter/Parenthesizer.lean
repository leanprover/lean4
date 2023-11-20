/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Parser.Extension
import Lean.Parser.StrInterpolation
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
the right of that node. For example, imagine the tree structure of `(f fun x => x) y` without parentheses. We need to
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
parser combinators by recursively replacing them with declarations tagged as `[combinator_parenthesizer]` for the
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
    builtinName := `builtin_parenthesizer,
    name := `parenthesizer,
    descr := "Register a parenthesizer for a parser.

  [parenthesizer k] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `SyntaxNodeKind` `k`.",
    valueTypeName := `Lean.PrettyPrinter.Parenthesizer,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let stx ← Attribute.Builtin.getIdent stx
      let id := stx.getId
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a parenthesizer for it immediately, so we just check for a declaration in this case
      unless (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id do
        throwError "invalid [parenthesizer] argument, unknown syntax kind '{id}'"
      if (← getEnv).contains id && (← Elab.getInfoState).enabled then
        Elab.addConstInfo stx id none
      pure id
  } `Lean.PrettyPrinter.parenthesizerAttribute
@[builtin_init mkParenthesizerAttribute] opaque parenthesizerAttribute : KeyedDeclsAttribute Parenthesizer

abbrev CategoryParenthesizer := (prec : Nat) → Parenthesizer

unsafe def mkCategoryParenthesizerAttribute : IO (KeyedDeclsAttribute CategoryParenthesizer) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtin_category_parenthesizer,
    name := `category_parenthesizer,
    descr := "Register a parenthesizer for a syntax category.

  [category_parenthesizer cat] registers a declaration of type `Lean.PrettyPrinter.CategoryParenthesizer` for the category `cat`,
  which is used when parenthesizing calls of `categoryParser cat prec`. Implementations should call `maybeParenthesize`
  with the precedence and `cat`. If no category parenthesizer is registered, the category will never be parenthesized,
  but still be traversed for parenthesizing nested categories.",
    valueTypeName := `Lean.PrettyPrinter.CategoryParenthesizer,
    evalKey := fun _ stx => do
      let env ← getEnv
      let stx ← Attribute.Builtin.getIdent stx
      let id := stx.getId
      let some cat := (Parser.parserExtension.getState env).categories.find? id
        | throwError "invalid [category_parenthesizer] argument, unknown parser category '{toString id}'"
      if (← Elab.getInfoState).enabled && (← getEnv).contains cat.declName then
        Elab.addConstInfo stx cat.declName none
      pure id
  } `Lean.PrettyPrinter.categoryParenthesizerAttribute
@[builtin_init mkCategoryParenthesizerAttribute] opaque categoryParenthesizerAttribute : KeyedDeclsAttribute CategoryParenthesizer

unsafe def mkCombinatorParenthesizerAttribute : IO ParserCompiler.CombinatorAttribute :=
  ParserCompiler.registerCombinatorAttribute
    `combinator_parenthesizer
    "Register a parenthesizer for a parser combinator.

  [combinator_parenthesizer c] registers a declaration of type `Lean.PrettyPrinter.Parenthesizer` for the `Parser` declaration `c`.
  Note that, unlike with [parenthesizer], this is not a node kind since combinators usually do not introduce their own node kinds.
  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
  with `Parenthesizer` in the parameter types."
@[builtin_init mkCombinatorParenthesizerAttribute] opaque combinatorParenthesizerAttribute : ParserCompiler.CombinatorAttribute

namespace Parenthesizer

open Lean.Core Parser
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
  getCurrMacroScope   := pure default
  getMainModule       := pure default
  withFreshMacroScope := fun x => x
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

@[combinator_parenthesizer orelse] partial def orelse.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  -- `orelse` may produce `choice` nodes for antiquotations
  if stx.getKind == `choice then
    visitArgs $ stx.getArgs.size.forM fun _ => do
      orelse.parenthesizer p1 p2
  else
    -- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
    -- them in turn. Uses the syntax traverser non-linearly!
    p1 <|> p2

-- `mkAntiquot` is quite complex, so we'd rather have its parenthesizer synthesized below the actual parser definition.
-- Note that there is a mutual recursion
-- `categoryParser -> mkAntiquot -> termParser -> categoryParser`, so we need to introduce an indirection somewhere
-- anyway.
@[extern "lean_mk_antiquot_parenthesizer"]
opaque mkAntiquot.parenthesizer' (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : Parenthesizer

@[inline] def liftCoreM {α} (x : CoreM α) : ParenthesizerM α :=
  liftM x

-- break up big mutual recursion
@[extern "lean_pretty_printer_parenthesizer_interpret_parser_descr"]
opaque interpretParserDescr' : ParserDescr → CoreM Parenthesizer

unsafe def parenthesizerForKindUnsafe (k : SyntaxNodeKind) : Parenthesizer := do
  if k == `missing then
    pure ()
  else
    let p ← runForNodeKind parenthesizerAttribute k interpretParserDescr'
    p

@[implemented_by parenthesizerForKindUnsafe]
opaque parenthesizerForKind (k : SyntaxNodeKind) : Parenthesizer

@[combinator_parenthesizer withAntiquot]
def withAntiquot.parenthesizer (antiP p : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  -- early check as minor optimization that also cleans up the backtrack traces
  if stx.isAntiquot || stx.isAntiquotSplice then
    orelse.parenthesizer antiP p
  else
    p

@[combinator_parenthesizer withAntiquotSuffixSplice]
def withAntiquotSuffixSplice.parenthesizer (_ : SyntaxNodeKind) (p suffix : Parenthesizer) : Parenthesizer := do
  if (← getCur).isAntiquotSuffixSplice then
    visitArgs <| suffix *> p
  else
    p

@[combinator_parenthesizer tokenWithAntiquot]
def tokenWithAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  if (← getCur).isTokenAntiquot then
    visitArgs p
  else
    p

partial def parenthesizeCategoryCore (cat : Name) (_prec : Nat) : Parenthesizer :=
  withReader (fun ctx => { ctx with cat := cat }) do
    let stx ← getCur
    if stx.getKind == `choice then
      visitArgs $ stx.getArgs.size.forM fun _ => do
        parenthesizeCategoryCore cat _prec
    else
      withAntiquot.parenthesizer (mkAntiquot.parenthesizer' cat.toString cat (isPseudoKind := true)) (parenthesizerForKind stx.getKind)
    modify fun st => { st with contCat := cat }

@[combinator_parenthesizer categoryParser]
def categoryParser.parenthesizer (cat : Name) (prec : Nat) : Parenthesizer := do
  let env ← getEnv
  match categoryParenthesizerAttribute.getValues env cat with
  | p::_ => p prec
  -- Fall back to the generic parenthesizer.
  -- In this case this node will never be parenthesized since we don't know which parentheses to use.
  | _    => parenthesizeCategoryCore cat prec

@[combinator_parenthesizer parserOfStack]
def parserOfStack.parenthesizer (offset : Nat) (_prec : Nat := 0) : Parenthesizer := do
  let st ← get
  let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset)
  parenthesizerForKind stx.getKind

@[builtin_category_parenthesizer term]
def term.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `term true wrapParens prec $
    parenthesizeCategoryCore `term prec
where
  /-- Wraps the term `stx` in parentheses and then copies its `SourceInfo` to the result.
  The purpose of this is to copy synthetic delaborator positions from the `stx` node to the parentheses node,
  which causes the info view to view both of these nodes as referring to the same expression.
  If we did not copy info, the info view would consider the parentheses to belong to the outer term.
  Note: we do not do `withRef stx` because that causes the "(" and ")" tokens to have source info as well,
  causing the info view to highlight each parenthesis as an independent expression. -/
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

@[builtin_category_parenthesizer tactic]
def tactic.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `tactic false (fun stx => Unhygienic.run `(tactic|($(⟨stx⟩)))) prec $
    parenthesizeCategoryCore `tactic prec

@[builtin_category_parenthesizer level]
def level.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `level false (fun stx => Unhygienic.run `(level|($(⟨stx⟩)))) prec $
    parenthesizeCategoryCore `level prec

@[builtin_category_parenthesizer rawStx]
def rawStx.parenthesizer : CategoryParenthesizer | _ => do
  goLeft

@[combinator_parenthesizer error]
def error.parenthesizer (_msg : String) : Parenthesizer :=
  pure ()

@[combinator_parenthesizer errorAtSavedPos]
def errorAtSavedPos.parenthesizer (_msg : String) (_delta : Bool) : Parenthesizer :=
  pure ()

@[combinator_parenthesizer atomic]
def atomic.parenthesizer (p : Parenthesizer) : Parenthesizer :=
  p

@[combinator_parenthesizer lookahead]
def lookahead.parenthesizer (_ : Parenthesizer) : Parenthesizer :=
  pure ()

@[combinator_parenthesizer notFollowedBy]
def notFollowedBy.parenthesizer (_ : Parenthesizer) : Parenthesizer :=
  pure ()

@[combinator_parenthesizer andthen]
def andthen.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer :=
  p2 *> p1

def checkKind (k : SyntaxNodeKind) : Parenthesizer := do
  let stx ← getCur
  if k != stx.getKind then
    trace[PrettyPrinter.parenthesize.backtrack] "unexpected node kind '{stx.getKind}', expected '{k}'"
    -- HACK; see `orelse.parenthesizer`
    throwBacktrack

@[combinator_parenthesizer node]
def node.parenthesizer (k : SyntaxNodeKind) (p : Parenthesizer) : Parenthesizer := do
  checkKind k
  visitArgs p

@[combinator_parenthesizer checkPrec]
def checkPrec.parenthesizer (prec : Nat) : Parenthesizer :=
  addPrecCheck prec

@[combinator_parenthesizer withFn]
def withFn.parenthesizer (_ : ParserFn → ParserFn) (p : Parenthesizer) : Parenthesizer := p

@[combinator_parenthesizer leadingNode]
def leadingNode.parenthesizer (k : SyntaxNodeKind) (prec : Nat) (p : Parenthesizer) : Parenthesizer := do
  node.parenthesizer k p
  addPrecCheck prec
  -- Limit `cont` precedence to `maxPrec-1`.
  -- This is because `maxPrec-1` is the precedence of function application, which is the only way to turn a leading parser
  -- into a trailing one.
  modify fun st => { st with contPrec := Nat.min (Parser.maxPrec-1) prec }

@[combinator_parenthesizer trailingNode]
def trailingNode.parenthesizer (k : SyntaxNodeKind) (prec lhsPrec : Nat) (p : Parenthesizer) : Parenthesizer := do
  checkKind k
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

@[combinator_parenthesizer rawCh] def rawCh.parenthesizer (_ch : Char) := visitToken

@[combinator_parenthesizer symbolNoAntiquot] def symbolNoAntiquot.parenthesizer (_sym : String) := visitToken
@[combinator_parenthesizer unicodeSymbolNoAntiquot] def unicodeSymbolNoAntiquot.parenthesizer (_sym _asciiSym : String) := visitToken

@[combinator_parenthesizer identNoAntiquot] def identNoAntiquot.parenthesizer := do checkKind identKind; visitToken
@[combinator_parenthesizer rawIdentNoAntiquot] def rawIdentNoAntiquot.parenthesizer := visitToken
@[combinator_parenthesizer identEq] def identEq.parenthesizer (_id : Name) := visitToken
@[combinator_parenthesizer nonReservedSymbolNoAntiquot] def nonReservedSymbolNoAntiquot.parenthesizer (_sym : String) (_includeIdent : Bool) := visitToken

@[combinator_parenthesizer charLitNoAntiquot] def charLitNoAntiquot.parenthesizer := visitToken
@[combinator_parenthesizer strLitNoAntiquot] def strLitNoAntiquot.parenthesizer := visitToken
@[combinator_parenthesizer nameLitNoAntiquot] def nameLitNoAntiquot.parenthesizer := visitToken
@[combinator_parenthesizer numLitNoAntiquot] def numLitNoAntiquot.parenthesizer := visitToken
@[combinator_parenthesizer scientificLitNoAntiquot] def scientificLitNoAntiquot.parenthesizer := visitToken
@[combinator_parenthesizer fieldIdx] def fieldIdx.parenthesizer := visitToken

@[combinator_parenthesizer manyNoAntiquot]
def manyNoAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  visitArgs $ stx.getArgs.size.forM fun _ => p

@[combinator_parenthesizer many1NoAntiquot]
def many1NoAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  manyNoAntiquot.parenthesizer p

@[combinator_parenthesizer many1Unbox]
def many1Unbox.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  if stx.getKind == nullKind then
    manyNoAntiquot.parenthesizer p
  else
    p

@[combinator_parenthesizer optionalNoAntiquot]
def optionalNoAntiquot.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  visitArgs p

@[combinator_parenthesizer sepByNoAntiquot]
def sepByNoAntiquot.parenthesizer (p pSep : Parenthesizer) : Parenthesizer := do
  let stx ← getCur
  visitArgs <| (List.range stx.getArgs.size).reverse.forM fun i => if i % 2 == 0 then p else pSep

@[combinator_parenthesizer sepBy1NoAntiquot] def sepBy1NoAntiquot.parenthesizer := sepByNoAntiquot.parenthesizer

@[combinator_parenthesizer withPosition] def withPosition.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  -- We assume the formatter will indent syntax sufficiently such that parenthesizing a `withPosition` node is never necessary
  modify fun st => { st with contPrec := none }
  p
@[combinator_parenthesizer withPositionAfterLinebreak] def withPositionAfterLinebreak.parenthesizer (p : Parenthesizer) : Parenthesizer :=
  -- TODO: improve?
  withPosition.parenthesizer p

@[combinator_parenthesizer withoutInfo] def withoutInfo.parenthesizer (p : Parenthesizer) : Parenthesizer := p

@[combinator_parenthesizer checkStackTop] def checkStackTop.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkWsBefore] def checkWsBefore.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkNoWsBefore] def checkNoWsBefore.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkLinebreakBefore] def checkLinebreakBefore.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkTailWs] def checkTailWs.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkColEq] def checkColEq.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkColGe] def checkColGe.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkColGt] def checkColGt.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkLineEq] def checkLineEq.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer eoi] def eoi.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer checkNoImmediateColon] def checkNoImmediateColon.parenthesizer : Parenthesizer := pure ()
@[combinator_parenthesizer skip] def skip.parenthesizer : Parenthesizer := pure ()

@[combinator_parenthesizer pushNone] def pushNone.parenthesizer : Parenthesizer := goLeft
@[combinator_parenthesizer hygieneInfoNoAntiquot] def hygieneInfoNoAntiquot.parenthesizer : Parenthesizer := goLeft

@[combinator_parenthesizer interpolatedStr]
def interpolatedStr.parenthesizer (p : Parenthesizer) : Parenthesizer := do
  visitArgs $ (← getCur).getArgs.reverse.forM fun chunk =>
    if chunk.isOfKind interpolatedStrLitKind then
      goLeft
    else
      p

@[combinator_parenthesizer _root_.ite, macro_inline] def ite {_ : Type} (c : Prop) [Decidable c] (t e : Parenthesizer) : Parenthesizer :=
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

def parenthesizeCategory (cat : Name) := parenthesize <| categoryParser.parenthesizer cat 0

def parenthesizeTerm := parenthesizeCategory `term
def parenthesizeTactic := parenthesizeCategory `tactic
def parenthesizeCommand := parenthesizeCategory `command

builtin_initialize
  registerTraceClass `PrettyPrinter.parenthesize
  registerTraceClass `PrettyPrinter.parenthesize.backtrack (inherited := true)
  registerTraceClass `PrettyPrinter.parenthesize.input (inherited := true)

end PrettyPrinter
end Lean
