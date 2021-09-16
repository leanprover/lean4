/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.CoreM
import Lean.Parser.Extension
import Lean.KeyedDeclsAttribute
import Lean.ParserCompiler.Attribute
import Lean.PrettyPrinter.Basic

/-!
The formatter turns a `Syntax` tree into a `Format` object, inserting both mandatory whitespace (to separate adjacent
tokens) as well as "pretty" optional whitespace.

The basic approach works much like the parenthesizer: A right-to-left traversal over the syntax tree, driven by
parser-specific handlers registered via attributes. The traversal is right-to-left so that when emitting a token, we
already know the text following it and can decide whether or not whitespace between the two is necessary.
-/

namespace Lean
namespace PrettyPrinter
namespace Formatter

structure Context where
  options : Options
  table   : Parser.TokenTable

structure State where
  stxTrav  : Syntax.Traverser
  -- Textual content of `stack` up to the first whitespace (not enclosed in an escaped ident). We assume that the textual
  -- content of `stack` is modified only by `pushText` and `pushLine`, so `leadWord` is adjusted there accordingly.
  leadWord : String := ""
  -- Stack of generated Format objects, analogous to the Syntax stack in the parser.
  -- Note, however, that the stack is reversed because of the right-to-left traversal.
  stack    : Array Format := #[]

end Formatter

abbrev FormatterM := ReaderT Formatter.Context $ StateRefT Formatter.State CoreM

@[inline] def FormatterM.orElse {α} (p₁ : FormatterM α) (p₂ : Unit → FormatterM α) : FormatterM α := do
  let s ← get
  catchInternalId backtrackExceptionId
    p₁
    (fun _ => do set s; p₂ ())

instance {α} : OrElse (FormatterM α) := ⟨FormatterM.orElse⟩

abbrev Formatter := FormatterM Unit

unsafe def mkFormatterAttribute : IO (KeyedDeclsAttribute Formatter) :=
  KeyedDeclsAttribute.init {
    builtinName := `builtinFormatter,
    name := `formatter,
    descr := "Register a formatter for a parser.

  [formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.",
    valueTypeName := `Lean.PrettyPrinter.Formatter,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let id ← Attribute.Builtin.getId stx
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a formatter for it immediately, so we just check for a declaration in this case
      if (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id then pure id
      else throwError "invalid [formatter] argument, unknown syntax kind '{id}'"
  } `Lean.PrettyPrinter.formatterAttribute
@[builtinInit mkFormatterAttribute] constant formatterAttribute : KeyedDeclsAttribute Formatter

unsafe def mkCombinatorFormatterAttribute : IO ParserCompiler.CombinatorAttribute :=
  ParserCompiler.registerCombinatorAttribute
    `combinatorFormatter
    "Register a formatter for a parser combinator.

  [combinatorFormatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.
  Note that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.
  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
  with `Formatter` in the parameter types."
@[builtinInit mkCombinatorFormatterAttribute] constant combinatorFormatterAttribute : ParserCompiler.CombinatorAttribute

namespace Formatter

open Lean.Core
open Lean.Parser

def throwBacktrack {α} : FormatterM α :=
throw $ Exception.internal backtrackExceptionId

instance : Syntax.MonadTraverser FormatterM := ⟨{
  get       := State.stxTrav <$> get,
  set       := fun t => modify (fun st => { st with stxTrav := t }),
  modifyGet := fun f => modifyGet (fun st => let (a, t) := f st.stxTrav; (a, { st with stxTrav := t }))
}⟩

open Syntax.MonadTraverser

def getStack : FormatterM (Array Format) := do
  let st ← get
  pure st.stack

def getStackSize : FormatterM Nat := do
  let stack ← getStack;
  pure stack.size

def setStack (stack : Array Format) : FormatterM Unit :=
  modify fun st => { st with stack := stack }

def push (f : Format) : FormatterM Unit :=
  modify fun st => { st with stack := st.stack.push f }

def pushLine : FormatterM Unit := do
  push Format.line;
  modify fun st => { st with leadWord := "" }

/-- Execute `x` at the right-most child of the current node, if any, then advance to the left. -/
def visitArgs (x : FormatterM Unit) : FormatterM Unit := do
  let stx ← getCur
  if stx.getArgs.size > 0 then
    goDown (stx.getArgs.size - 1) *> x <* goUp
  goLeft

/-- Execute `x`, pass array of generated Format objects to `fn`, and push result. -/
def fold (fn : Array Format → Format) (x : FormatterM Unit) : FormatterM Unit := do
  let sp ← getStackSize
  x
  let stack ← getStack
  let f := fn $ stack.extract sp stack.size
  setStack $ (stack.shrink sp).push f

/-- Execute `x` and concatenate generated Format objects. -/
def concat (x : FormatterM Unit) : FormatterM Unit := do
  fold (Array.foldl (fun acc f => if acc.isNil then f else f ++ acc) Format.nil) x

def indent (x : Formatter) (indent : Option Int := none) : Formatter := do
  concat x
  let ctx ← read
  let indent := indent.getD $ Std.Format.getIndent ctx.options
  modify fun st => { st with stack := st.stack.modify (st.stack.size - 1) (Format.nest indent) }

def group (x : Formatter) : Formatter := do
  concat x
  modify fun st => { st with stack := st.stack.modify (st.stack.size - 1) Format.fill }

/-- If `pos?` has a position, run `x` and tag its results with that position. Otherwise just run `x`. -/
def withMaybeTag (pos? : Option String.Pos) (x : FormatterM Unit) : Formatter := do
  if let some p := pos? then
    concat x
    modify fun st => { st with stack := st.stack.modify (st.stack.size - 1) (Format.tag p) }
  else
    x

@[combinatorFormatter Lean.Parser.orelse] def orelse.formatter (p1 p2 : Formatter) : Formatter :=
  -- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
  -- them in turn. Uses the syntax traverser non-linearly!
  p1 <|> p2

-- `mkAntiquot` is quite complex, so we'd rather have its formatter synthesized below the actual parser definition.
-- Note that there is a mutual recursion
-- `categoryParser -> mkAntiquot -> termParser -> categoryParser`, so we need to introduce an indirection somewhere
-- anyway.
@[extern "lean_mk_antiquot_formatter"]
constant mkAntiquot.formatter' (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Formatter

-- break up big mutual recursion
@[extern "lean_pretty_printer_formatter_interpret_parser_descr"]
constant interpretParserDescr' : ParserDescr → CoreM Formatter

unsafe def formatterForKindUnsafe (k : SyntaxNodeKind) : Formatter := do
  if k == `missing then
    push "<missing>"
    goLeft
  else
    let stx ← getCur
    let f ← runForNodeKind formatterAttribute k interpretParserDescr'
    withMaybeTag stx.getPos? f

@[implementedBy formatterForKindUnsafe]
constant formatterForKind (k : SyntaxNodeKind) : Formatter

@[combinatorFormatter Lean.Parser.withAntiquot]
def withAntiquot.formatter (antiP p : Formatter) : Formatter :=
  -- TODO: could be optimized using `isAntiquot` (which would have to be moved), but I'd rather
  -- fix the backtracking hack outright.
  orelse.formatter antiP p

@[combinatorFormatter Lean.Parser.withAntiquotSuffixSplice]
def withAntiquotSuffixSplice.formatter (k : SyntaxNodeKind) (p suffix : Formatter) : Formatter := do
  if (← getCur).isAntiquotSuffixSplice then
    visitArgs <| suffix *> p
  else
    p

@[combinatorFormatter Lean.Parser.tokenWithAntiquot]
def tokenWithAntiquot.formatter (p : Formatter) : Formatter := do
  if (← getCur).isTokenAntiquot then
    visitArgs p
  else
    p

@[combinatorFormatter Lean.Parser.categoryParser]
def categoryParser.formatter (cat : Name) : Formatter := group $ indent do
  let stx ← getCur
  trace[PrettyPrinter.format] "formatting {indentD (format stx)}"
  if stx.getKind == `choice then
    visitArgs do
      -- format only last choice
      -- TODO: We could use elaborator data here to format the chosen child when available
      formatterForKind (← getCur).getKind
  else
    withAntiquot.formatter (mkAntiquot.formatter' cat.toString none) (formatterForKind stx.getKind)

@[combinatorFormatter Lean.Parser.categoryParserOfStack]
def categoryParserOfStack.formatter (offset : Nat) : Formatter := do
  let st ← get
  let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset)
  categoryParser.formatter stx.getId

@[combinatorFormatter Lean.Parser.parserOfStack]
def parserOfStack.formatter (offset : Nat) (prec : Nat := 0) : Formatter := do
  let st ← get
  let stx := st.stxTrav.parents.back.getArg (st.stxTrav.idxs.back - offset)
  formatterForKind stx.getKind

@[combinatorFormatter Lean.Parser.error]
def error.formatter (msg : String) : Formatter := pure ()
@[combinatorFormatter Lean.Parser.errorAtSavedPos]
def errorAtSavedPos.formatter (msg : String) (delta : Bool) : Formatter := pure ()
@[combinatorFormatter Lean.Parser.atomic]
def atomic.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.lookahead]
def lookahead.formatter (p : Formatter) : Formatter := pure ()

@[combinatorFormatter Lean.Parser.notFollowedBy]
def notFollowedBy.formatter (p : Formatter) : Formatter := pure ()

@[combinatorFormatter Lean.Parser.andthen]
def andthen.formatter (p1 p2 : Formatter) : Formatter := p2 *> p1

def checkKind (k : SyntaxNodeKind) : FormatterM Unit := do
  let stx ← getCur
  if k != stx.getKind then
    trace[PrettyPrinter.format.backtrack] "unexpected node kind '{stx.getKind}', expected '{k}'"
    throwBacktrack

@[combinatorFormatter Lean.Parser.node]
def node.formatter (k : SyntaxNodeKind) (p : Formatter) : Formatter := do
  checkKind k;
  visitArgs p

@[combinatorFormatter Lean.Parser.trailingNode]
def trailingNode.formatter (k : SyntaxNodeKind) (_ _ : Nat) (p : Formatter) : Formatter := do
  checkKind k
  visitArgs do
    p;
    -- leading term, not actually produced by `p`
    categoryParser.formatter `foo

def parseToken (s : String) : FormatterM ParserState := do
  -- include comment tokens, e.g. when formatting `- -0`
  (Parser.andthenFn Parser.whitespace (Parser.tokenFn [])) {
    input := s,
    fileName := "",
    fileMap := FileMap.ofString "",
    prec := 0,
    env := ← getEnv,
    options := ← getOptions,
    tokens := (← read).table } (Parser.mkParserState s)

def pushTokenCore (tk : String) : FormatterM Unit := do
  if tk.toSubstring.dropRightWhile (fun s => s == ' ') == tk.toSubstring then
    push tk
  else
    pushLine
    push tk.trimRight

def pushToken (info : SourceInfo) (tk : String) : FormatterM Unit := do
  match info with
  | SourceInfo.original _ _ ss _ =>
    -- preserve non-whitespace content (i.e. comments)
    let ss' := ss.trim
    if !ss'.isEmpty then
      let ws := { ss with startPos := ss'.stopPos }
      if ws.contains '\n' then
        push s!"\n{ss'}"
      else
        push s!"  {ss'}"
      modify fun st => { st with leadWord := "" }
  | _ => pure ()

  let st ← get
  -- If there is no space between `tk` and the next word, see if we would parse more than `tk` as a single token
  if st.leadWord != "" && tk.trimRight == tk then
    let tk' := tk.trimLeft
    let t ← parseToken $ tk' ++ st.leadWord
    if t.pos <= tk'.bsize then
      -- stopped within `tk` => use it as is, extend `leadWord` if not prefixed by whitespace
      pushTokenCore tk
      modify fun st => { st with leadWord := if tk.trimLeft == tk then tk ++ st.leadWord else "" }
    else
      -- stopped after `tk` => add space
      pushTokenCore $ tk ++ " "
      modify fun st => { st with leadWord := if tk.trimLeft == tk then tk else "" }
  else
    -- already separated => use `tk` as is
    pushTokenCore tk
    modify fun st => { st with leadWord := if tk.trimLeft == tk then tk else "" }

  match info with
  | SourceInfo.original ss _ _ _ =>
    -- preserve non-whitespace content (i.e. comments)
    let ss' := ss.trim
    if !ss'.isEmpty then
      let ws := { ss with startPos := ss'.stopPos }
      if ws.contains '\n' then do
        -- Indentation is automatically increased when entering a category, but comments should be aligned
        -- with the actual token, so dedent
        indent (push s!"{ss'}\n") (some ((0:Int) - Std.Format.getIndent (← getOptions)))
      else
        push s!"{ss'} "
      modify fun st => { st with leadWord := "" }
  | _ => pure ()

@[combinatorFormatter Lean.Parser.symbolNoAntiquot]
def symbolNoAntiquot.formatter (sym : String) : Formatter := do
  let stx ← getCur
  if stx.isToken sym then do
    let (Syntax.atom info _) ← pure stx | unreachable!
    pushToken info sym
    goLeft
  else do
    trace[PrettyPrinter.format.backtrack] "unexpected syntax '{format stx}', expected symbol '{sym}'"
    throwBacktrack

@[combinatorFormatter Lean.Parser.nonReservedSymbolNoAntiquot] def nonReservedSymbolNoAntiquot.formatter := symbolNoAntiquot.formatter

@[combinatorFormatter Lean.Parser.rawCh] def rawCh.formatter (ch : Char) := symbolNoAntiquot.formatter ch.toString

@[combinatorFormatter Lean.Parser.unicodeSymbolNoAntiquot]
def unicodeSymbolNoAntiquot.formatter (sym asciiSym : String) : Formatter := do
  let Syntax.atom info val ← getCur
    | throwError m!"not an atom: {← getCur}"
  if val == sym.trim then
    pushToken info sym
  else
    pushToken info asciiSym;
  goLeft

@[combinatorFormatter Lean.Parser.identNoAntiquot]
def identNoAntiquot.formatter : Formatter := do
  checkKind identKind
  let Syntax.ident info _ id _ ← getCur
    | throwError m!"not an ident: {← getCur}"
  let id := id.simpMacroScopes
  pushToken info id.toString
  goLeft

@[combinatorFormatter Lean.Parser.rawIdentNoAntiquot] def rawIdentNoAntiquot.formatter : Formatter := do
  checkKind identKind
  let Syntax.ident info _ id _ ← getCur
    | throwError m!"not an ident: {← getCur}"
  pushToken info id.toString
  goLeft

@[combinatorFormatter Lean.Parser.identEq] def identEq.formatter (id : Name) := rawIdentNoAntiquot.formatter

def visitAtom (k : SyntaxNodeKind) : Formatter := do
  let stx ← getCur
  if k != Name.anonymous then
    checkKind k
  let Syntax.atom info val ← pure $ stx.ifNode (fun n => n.getArg 0) (fun _ => stx)
    | throwError m!"not an atom: {stx}"
  pushToken info val
  goLeft

@[combinatorFormatter Lean.Parser.charLitNoAntiquot] def charLitNoAntiquot.formatter := visitAtom charLitKind
@[combinatorFormatter Lean.Parser.strLitNoAntiquot] def strLitNoAntiquot.formatter := visitAtom strLitKind
@[combinatorFormatter Lean.Parser.nameLitNoAntiquot] def nameLitNoAntiquot.formatter := visitAtom nameLitKind
@[combinatorFormatter Lean.Parser.numLitNoAntiquot] def numLitNoAntiquot.formatter := visitAtom numLitKind
@[combinatorFormatter Lean.Parser.scientificLitNoAntiquot] def scientificLitNoAntiquot.formatter := visitAtom scientificLitKind
@[combinatorFormatter Lean.Parser.fieldIdx] def fieldIdx.formatter := visitAtom fieldIdxKind

@[combinatorFormatter Lean.Parser.manyNoAntiquot]
def manyNoAntiquot.formatter (p : Formatter) : Formatter := do
  let stx ← getCur
  visitArgs $ stx.getArgs.size.forM fun _ => p

@[combinatorFormatter Lean.Parser.many1NoAntiquot] def many1NoAntiquot.formatter (p : Formatter) : Formatter := manyNoAntiquot.formatter p

@[combinatorFormatter Lean.Parser.optionalNoAntiquot]
def optionalNoAntiquot.formatter (p : Formatter) : Formatter := visitArgs p

@[combinatorFormatter Lean.Parser.many1Unbox]
def many1Unbox.formatter (p : Formatter) : Formatter := do
  let stx ← getCur
  if stx.getKind == nullKind then do
    manyNoAntiquot.formatter p
  else
    p

@[combinatorFormatter Lean.Parser.sepByNoAntiquot]
def sepByNoAntiquot.formatter (p pSep : Formatter) : Formatter := do
  let stx ← getCur
  visitArgs $ (List.range stx.getArgs.size).reverse.forM $ fun i => if i % 2 == 0 then p else pSep

@[combinatorFormatter Lean.Parser.sepBy1NoAntiquot] def sepBy1NoAntiquot.formatter := sepByNoAntiquot.formatter

@[combinatorFormatter Lean.Parser.withPosition] def withPosition.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.withoutPosition] def withoutPosition.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.withForbidden] def withForbidden.formatter (tk : Token) (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.withoutForbidden] def withoutForbidden.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.withoutInfo] def withoutInfo.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.setExpected]
def setExpected.formatter (expected : List String) (p : Formatter) : Formatter := p

@[combinatorFormatter Lean.Parser.incQuotDepth] def incQuotDepth.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.decQuotDepth] def decQuotDepth.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.suppressInsideQuot] def suppressInsideQuot.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.evalInsideQuot] def evalInsideQuot.formatter (declName : Name) (p : Formatter) : Formatter := p

@[combinatorFormatter Lean.Parser.checkWsBefore] def checkWsBefore.formatter : Formatter := do
  let st ← get
  if st.leadWord != "" then
    pushLine

@[combinatorFormatter Lean.Parser.checkPrec] def checkPrec.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkLhsPrec] def checkLhsPrec.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.setLhsPrec] def setLhsPrec.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkStackTop] def checkStackTop.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkNoWsBefore] def checkNoWsBefore.formatter : Formatter :=
  -- prevent automatic whitespace insertion
  modify fun st => { st with leadWord := "" }
@[combinatorFormatter Lean.Parser.checkLinebreakBefore] def checkLinebreakBefore.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkTailWs] def checkTailWs.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkColGe] def checkColGe.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkColGt] def checkColGt.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkLineEq] def checkLineEq.formatter : Formatter := pure ()

@[combinatorFormatter Lean.Parser.eoi] def eoi.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.notFollowedByCategoryToken] def notFollowedByCategoryToken.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkNoImmediateColon] def checkNoImmediateColon.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkInsideQuot] def checkInsideQuot.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.checkOutsideQuot] def checkOutsideQuot.formatter : Formatter := pure ()
@[combinatorFormatter Lean.Parser.skip] def skip.formatter : Formatter := pure ()

@[combinatorFormatter Lean.Parser.pushNone] def pushNone.formatter : Formatter := goLeft

@[combinatorFormatter Lean.Parser.withOpenDecl] def withOpenDecl.formatter (p : Formatter) : Formatter := p
@[combinatorFormatter Lean.Parser.withOpen] def withOpen.formatter (p : Formatter) : Formatter := p

@[combinatorFormatter Lean.Parser.interpolatedStr]
def interpolatedStr.formatter (p : Formatter) : Formatter := do
  visitArgs $ (← getCur).getArgs.reverse.forM fun chunk =>
    match chunk.isLit? interpolatedStrLitKind with
    | some str => push str *> goLeft
    | none     => p

@[combinatorFormatter Lean.Parser.dbgTraceState] def dbgTraceState.formatter (label : String) (p : Formatter) : Formatter := p

@[combinatorFormatter ite, macroInline] def ite {α : Type} (c : Prop) [h : Decidable c] (t e : Formatter) : Formatter :=
  if c then t else e

abbrev FormatterAliasValue := AliasValue Formatter

builtin_initialize formatterAliasesRef : IO.Ref (NameMap FormatterAliasValue) ← IO.mkRef {}

def registerAlias (aliasName : Name) (v : FormatterAliasValue) : IO Unit := do
  Parser.registerAliasCore formatterAliasesRef aliasName v

instance : Coe Formatter FormatterAliasValue := { coe := AliasValue.const }
instance : Coe (Formatter → Formatter) FormatterAliasValue := { coe := AliasValue.unary }
instance : Coe (Formatter → Formatter → Formatter) FormatterAliasValue := { coe := AliasValue.binary }

end Formatter
open Formatter

def format (formatter : Formatter) (stx : Syntax) : CoreM Format := do
  trace[PrettyPrinter.format.input] "{Std.format stx}"
  let options ← getOptions
  let table ← Parser.builtinTokenTable.get
  catchInternalId backtrackExceptionId
    (do
      let (_, st) ← (concat formatter { table := table, options := options }).run { stxTrav := Syntax.Traverser.fromSyntax stx };
      pure $ Format.fill $ st.stack.get! 0)
    (fun _ => throwError "format: uncaught backtrack exception")

def formatTerm := format $ categoryParser.formatter `term
def formatTactic := format $ categoryParser.formatter `tactic
def formatCommand := format $ categoryParser.formatter `command

builtin_initialize registerTraceClass `PrettyPrinter.format;

end PrettyPrinter
end Lean
