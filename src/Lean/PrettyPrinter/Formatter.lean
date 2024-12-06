/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.CoreM
import Lean.Parser.Extension
import Lean.Parser.StrInterpolation
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
  /-- Textual content of `stack` up to the first whitespace (not enclosed in an escaped ident). We assume that the textual
  content of `stack` is modified only by `pushText` and `pushLine`, so `leadWord` is adjusted there accordingly. -/
  leadWord : String := ""
  /-- When the `leadWord` is nonempty, whether it is an identifier. Identifiers get space inserted between them. -/
  leadWordIdent : Bool := false
  /-- Whether the generated format begins with the result of an ungrouped category formatter. -/
  isUngrouped : Bool := false
  /-- Whether the resulting format must be grouped when used in a category formatter.
  If the flag is set to false, then categoryParser omits the fill+nest operation. -/
  mustBeGrouped : Bool := true
  /-- Stack of generated Format objects, analogous to the Syntax stack in the parser.
  Note, however, that the stack is reversed because of the right-to-left traversal. -/
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
    builtinName := `builtin_formatter,
    name := `formatter,
    descr := "Register a formatter for a parser.

  [formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.",
    valueTypeName := `Lean.PrettyPrinter.Formatter,
    evalKey := fun builtin stx => do
      let env ← getEnv
      let stx ← Attribute.Builtin.getIdent stx
      let id := stx.getId
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a formatter for it immediately, so we just check for a declaration in this case
      unless (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id do
        throwError "invalid [formatter] argument, unknown syntax kind '{id}'"
      if (← getEnv).contains id && (← Elab.getInfoState).enabled then
        Elab.addConstInfo stx id none
      pure id
  } `Lean.PrettyPrinter.formatterAttribute
@[builtin_init mkFormatterAttribute] opaque formatterAttribute : KeyedDeclsAttribute Formatter

unsafe def mkCombinatorFormatterAttribute : IO ParserCompiler.CombinatorAttribute :=
  ParserCompiler.registerCombinatorAttribute
    `combinator_formatter
    "Register a formatter for a parser combinator.

  [combinator_formatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.
  Note that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.
  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
  with `Formatter` in the parameter types."
@[builtin_init mkCombinatorFormatterAttribute] opaque combinatorFormatterAttribute : ParserCompiler.CombinatorAttribute

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

private def push (f : Format) : FormatterM Unit :=
  modify fun st => { st with stack := st.stack.push f, isUngrouped := false }

def pushWhitespace (f : Format) : FormatterM Unit := do
  push f
  modify fun st => { st with leadWord := "", leadWordIdent := false, isUngrouped := false }

def pushLine : FormatterM Unit :=
  pushWhitespace Format.line

def pushAlign (force : Bool) : FormatterM Unit :=
  pushWhitespace (.align force)

/--
Execute `x` at the right-most child of the current node, if any, then advance to the left.
Runs `x` even if there are no children, in which case the current syntax node will be `.missing`.
-/
def visitArgs (x : FormatterM Unit) : FormatterM Unit := do
  let stx ← getCur
  goDown (stx.getArgs.size - 1) *> x <* goUp
  goLeft

/-- Execute `x`, pass array of generated Format objects to `fn`, and push result. -/
def fold (fn : Array Format → Format) (x : FormatterM Unit) : FormatterM Unit := do
  let sp ← getStackSize
  x
  let stack ← getStack
  let f := fn $ stack.extract sp stack.size
  setStack $ (stack.take sp).push f

/-- Execute `x` and concatenate generated Format objects. -/
def concat (x : FormatterM Unit) : FormatterM Unit := do
  fold (Array.foldl (fun acc f => if acc.isNil then f else f ++ acc) Format.nil) x

def indent (x : Formatter) (indent : Option Int := none) : Formatter := do
  concat x
  let ctx ← read
  let indent := indent.getD $ Std.Format.getIndent ctx.options
  modify fun st => { st with stack := st.stack.modify (st.stack.size - 1) (Format.nest indent) }

def fill (x : Formatter) : Formatter := do
  concat x
  modify fun st => { st with
    stack := st.stack.modify (st.stack.size - 1) Format.fill
    isUngrouped := false
  }

def group (x : Formatter) : Formatter := do
  concat x
  modify fun st => { st with
    stack := st.stack.modify (st.stack.size - 1) Format.group
    isUngrouped := false
  }

/-- If `pos?` has a position, run `x` and tag its results with that position,
if they are not already tagged. Otherwise just run `x`. -/
def withMaybeTag (pos? : Option String.Pos) (x : FormatterM Unit) : Formatter := do
  if let some p := pos? then
    concat x
    modify fun st => {
      st with stack := st.stack.modify (st.stack.size - 1) fun fmt =>
        if fmt matches Format.tag .. then fmt
        else Format.tag p.byteIdx fmt
    }
  else
    x

@[combinator_formatter orelse] partial def orelse.formatter (p1 p2 : Formatter) : Formatter := do
  let stx ← getCur
  -- `orelse` may produce `choice` nodes for antiquotations
  if stx.getKind == `choice then
    visitArgs do
      -- format only last choice
      -- TODO: We could use elaborator data here to format the chosen child when available
      orelse.formatter p1 p2
  else
    -- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
    -- them in turn. Uses the syntax traverser non-linearly!
    p1 <|> p2

@[combinator_formatter recover]
def recover.formatter (fmt : PrettyPrinter.Formatter) := fmt

@[combinator_formatter recover']
def recover'.formatter (fmt : PrettyPrinter.Formatter) := fmt

-- `mkAntiquot` is quite complex, so we'd rather have its formatter synthesized below the actual parser definition.
-- Note that there is a mutual recursion
-- `categoryParser -> mkAntiquot -> termParser -> categoryParser`, so we need to introduce an indirection somewhere
-- anyway.
@[extern "lean_mk_antiquot_formatter"]
opaque mkAntiquot.formatter' (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : Formatter

-- break up big mutual recursion
@[extern "lean_pretty_printer_formatter_interpret_parser_descr"]
opaque interpretParserDescr' : ParserDescr → CoreM Formatter

private def SourceInfo.getExprPos? : SourceInfo → Option String.Pos
  | SourceInfo.synthetic (pos := pos) .. => pos
  | _ => none

private def getExprPos? : Syntax → Option String.Pos
  | Syntax.node info _ _ => SourceInfo.getExprPos? info
  | Syntax.atom info _ => SourceInfo.getExprPos? info
  | Syntax.ident info _ _ _ => SourceInfo.getExprPos? info
  | Syntax.missing => none

unsafe def formatterForKindUnsafe (k : SyntaxNodeKind) : Formatter := do
  if k == `missing then
    push "<missing>"
    goLeft
  else
    let stx ← getCur
    let f ← runForNodeKind formatterAttribute k interpretParserDescr'
    withMaybeTag (getExprPos? stx) f

@[implemented_by formatterForKindUnsafe]
opaque formatterForKind (k : SyntaxNodeKind) : Formatter

@[combinator_formatter withAntiquot]
def withAntiquot.formatter (antiP p : Formatter) : Formatter :=
  -- TODO: could be optimized using `isAntiquot` (which would have to be moved), but I'd rather
  -- fix the backtracking hack outright.
  orelse.formatter antiP p

@[combinator_formatter withAntiquotSuffixSplice]
def withAntiquotSuffixSplice.formatter (_ : SyntaxNodeKind) (p suffix : Formatter) : Formatter := do
  if (← getCur).isAntiquotSuffixSplice then
    visitArgs <| suffix *> p
  else
    p

@[combinator_formatter tokenWithAntiquot]
def tokenWithAntiquot.formatter (p : Formatter) : Formatter := do
  if (← getCur).isTokenAntiquot then
    visitArgs p
  else
    p

def categoryFormatterCore (cat : Name) : Formatter := do
  modify fun st => { st with mustBeGrouped := true, isUngrouped := false }
  let stx ← getCur
  trace[PrettyPrinter.format] "formatting {indentD (format stx)}"
  if stx.getKind == `choice then
    visitArgs do
      -- format only last choice
      -- TODO: We could use elaborator data here to format the chosen child when available
      formatterForKind (← getCur).getKind
  else if cat == `rawStx then
    withAntiquot.formatter (mkAntiquot.formatter' cat.toString cat (isPseudoKind := true)) (push stx.formatStx *> goLeft)
  else
    withAntiquot.formatter (mkAntiquot.formatter' cat.toString cat (isPseudoKind := true)) (formatterForKind stx.getKind)
  modify fun st => { st with mustBeGrouped := true, isUngrouped := !st.mustBeGrouped }

@[combinator_formatter categoryParser]
def categoryParser.formatter (cat : Name) : Formatter := do
  concat <| categoryFormatterCore cat
  unless (← get).isUngrouped do
    let indent := Std.Format.getIndent (← read).options
    modify fun st => { st with
      stack := st.stack.modify (st.stack.size - 1) fun fmt =>
        fmt.nest indent |>.fill
    }

def categoryFormatter (cat : Name) : Formatter :=
  fill <| indent <| categoryFormatterCore cat

@[combinator_formatter parserOfStack]
def parserOfStack.formatter (offset : Nat) (_prec : Nat := 0) : Formatter := do
  let st ← get
  let stx := st.stxTrav.parents.back!.getArg (st.stxTrav.idxs.back! - offset)
  formatterForKind stx.getKind

@[combinator_formatter error]
def error.formatter (_msg : String) : Formatter := pure ()
@[combinator_formatter errorAtSavedPos]
def errorAtSavedPos.formatter (_msg : String) (_delta : Bool) : Formatter := pure ()
@[combinator_formatter lookahead]
def lookahead.formatter (_ : Formatter) : Formatter := pure ()

@[combinator_formatter notFollowedBy]
def notFollowedBy.formatter (_ : Formatter) : Formatter := pure ()

@[combinator_formatter andthen]
def andthen.formatter (p1 p2 : Formatter) : Formatter := p2 *> p1

def checkKind (k : SyntaxNodeKind) : FormatterM Unit := do
  let stx ← getCur
  if k != stx.getKind then
    trace[PrettyPrinter.format.backtrack] "unexpected node kind '{stx.getKind}', expected '{k}'"
    throwBacktrack

@[combinator_formatter node]
def node.formatter (k : SyntaxNodeKind) (p : Formatter) : Formatter := do
  checkKind k;
  visitArgs p

@[combinator_formatter withFn]
def withFn.formatter (_ : ParserFn → ParserFn) (p : Formatter) : Formatter := p

@[combinator_formatter trailingNode]
def trailingNode.formatter (k : SyntaxNodeKind) (_ _ : Nat) (p : Formatter) : Formatter := do
  checkKind k
  visitArgs do
    p;
    -- leading term, not actually produced by `p`
    categoryParser.formatter `foo

def parseToken (s : String) : FormatterM ParserState :=
  -- include comment tokens, e.g. when formatting `- -0`
  return (Parser.andthenFn Parser.whitespace (Parser.tokenFn [])).run {
    input := s,
    fileName := "",
    fileMap := FileMap.ofString ""
  } {
    env := ← getEnv,
    options := ← getOptions
  } ((← read).table) (Parser.mkParserState s)

def pushToken (info : SourceInfo) (tk : String) (ident : Bool) : FormatterM Unit := do
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
      modify fun st => { st with leadWord := "", leadWordIdent := false }
  | _ => pure ()

  let st ← get
  -- If there is no space between `tk` and the next word, see if we should insert a discretionary space.
  if st.leadWord != "" && tk.trimRight == tk then
    let insertSpace ← do
      if ident && st.leadWordIdent then
        -- Both idents => need space
        pure true
      else
        -- Check if we would parse more than `tk` as a single token
        let tk' := tk.trimLeft
        let t ← parseToken $ tk' ++ st.leadWord
        if t.pos ≤ tk'.endPos then
          -- stopped within `tk` => use it as is
          pure false
        else
          -- stopped after `tk` => add space
          pure true
    if !insertSpace then
      -- extend `leadWord` if not prefixed by whitespace
      push tk
      modify fun st => { st with leadWord := if tk.trimLeft == tk then tk ++ st.leadWord else "", leadWordIdent := ident }
    else
      pushLine
      push tk
      modify fun st => { st with leadWord := if tk.trimLeft == tk then tk else "", leadWordIdent := ident }
  else
    -- already separated => use `tk` as is
    if st.leadWord == "" then
      push tk.trimRight
    else if tk.endsWith " " then
      pushLine
      push tk.trimRight
    else
      push tk -- preserve special whitespace for tokens like ":=\n"
    modify fun st => { st with leadWord := if tk.trimLeft == tk then tk else "", leadWordIdent := ident }

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
        pushLine
        push ss'.toString
      modify fun st => { st with leadWord := "" }
  | _ => pure ()

@[combinator_formatter symbolNoAntiquot]
def symbolNoAntiquot.formatter (sym : String) : Formatter := do
  let stx ← getCur
  if stx.isToken sym then do
    let (Syntax.atom info _) ← pure stx | unreachable!
    withMaybeTag (getExprPos? stx) (pushToken info sym false)
    goLeft
  else do
    trace[PrettyPrinter.format.backtrack] "unexpected syntax '{format stx}', expected symbol '{sym}'"
    throwBacktrack

@[combinator_formatter nonReservedSymbolNoAntiquot] def nonReservedSymbolNoAntiquot.formatter := symbolNoAntiquot.formatter

@[combinator_formatter rawCh] def rawCh.formatter (ch : Char) := symbolNoAntiquot.formatter ch.toString

@[combinator_formatter unicodeSymbolNoAntiquot]
def unicodeSymbolNoAntiquot.formatter (sym asciiSym : String) : Formatter := do
  let Syntax.atom info val ← getCur
    | throwError m!"not an atom: {← getCur}"
  if val == sym.trim then
    pushToken info sym false
  else
    pushToken info asciiSym false
  goLeft

@[combinator_formatter identNoAntiquot]
def identNoAntiquot.formatter : Formatter := do
  checkKind identKind
  let stx@(Syntax.ident info _ id _) ← getCur
    | throwError m!"not an ident: {← getCur}"
  let id := id.simpMacroScopes
  let table := (← read).table
  let isToken (s : String) : Bool := (table.find? s).isSome
  withMaybeTag (getExprPos? stx) (pushToken info (id.toString (isToken := isToken)) true)
  goLeft

@[combinator_formatter rawIdentNoAntiquot] def rawIdentNoAntiquot.formatter : Formatter := do
  checkKind identKind
  let Syntax.ident info _ id _ ← getCur
    | throwError m!"not an ident: {← getCur}"
  pushToken info id.toString true
  goLeft

@[combinator_formatter identEq] def identEq.formatter (_id : Name) := rawIdentNoAntiquot.formatter

def visitAtom (k : SyntaxNodeKind) : Formatter := do
  let stx ← getCur
  if k != Name.anonymous then
    checkKind k
  let Syntax.atom info val ← pure $ stx.ifNode (fun n => n.getArg 0) (fun _ => stx)
    | throwError m!"not an atom: {stx}"
  pushToken info val false
  goLeft

@[combinator_formatter charLitNoAntiquot] def charLitNoAntiquot.formatter := visitAtom charLitKind
@[combinator_formatter strLitNoAntiquot] def strLitNoAntiquot.formatter := visitAtom strLitKind
@[combinator_formatter nameLitNoAntiquot] def nameLitNoAntiquot.formatter := visitAtom nameLitKind
@[combinator_formatter numLitNoAntiquot] def numLitNoAntiquot.formatter := visitAtom numLitKind
@[combinator_formatter scientificLitNoAntiquot] def scientificLitNoAntiquot.formatter := visitAtom scientificLitKind
@[combinator_formatter fieldIdx] def fieldIdx.formatter := visitAtom fieldIdxKind

@[combinator_formatter manyNoAntiquot]
def manyNoAntiquot.formatter (p : Formatter) : Formatter := do
  let stx ← getCur
  visitArgs $ stx.getArgs.size.forM fun _ _ => p

@[combinator_formatter many1NoAntiquot] def many1NoAntiquot.formatter (p : Formatter) : Formatter := manyNoAntiquot.formatter p

@[combinator_formatter optionalNoAntiquot]
def optionalNoAntiquot.formatter (p : Formatter) : Formatter := do
  let stx ← getCur
  visitArgs <| unless stx.getArgs.isEmpty do p

@[combinator_formatter many1Unbox]
def many1Unbox.formatter (p : Formatter) : Formatter := do
  let stx ← getCur
  if stx.getKind == nullKind then do
    manyNoAntiquot.formatter p
  else
    p

@[combinator_formatter sepByNoAntiquot]
def sepByNoAntiquot.formatter (p pSep : Formatter) : Formatter := do
  let stx ← getCur
  visitArgs <| stx.getArgs.size.forRevM fun i _ => if i % 2 == 0 then p else pSep

@[combinator_formatter sepBy1NoAntiquot] def sepBy1NoAntiquot.formatter := sepByNoAntiquot.formatter

@[combinator_formatter withoutInfo] def withoutInfo.formatter (p : Formatter) : Formatter := p
@[combinator_formatter checkWsBefore] def checkWsBefore.formatter : Formatter := do
  let st ← get
  if st.leadWord != "" then
    pushLine

@[combinator_formatter checkPrec] def checkPrec.formatter : Formatter := pure ()
@[combinator_formatter checkLhsPrec] def checkLhsPrec.formatter : Formatter := pure ()
@[combinator_formatter setLhsPrec] def setLhsPrec.formatter : Formatter := pure ()
@[combinator_formatter checkStackTop] def checkStackTop.formatter : Formatter := pure ()
@[combinator_formatter checkNoWsBefore] def checkNoWsBefore.formatter : Formatter :=
  -- prevent automatic whitespace insertion
  modify fun st => { st with leadWord := "", leadWordIdent := false }
@[combinator_formatter checkLinebreakBefore] def checkLinebreakBefore.formatter : Formatter := pure ()
@[combinator_formatter checkTailWs] def checkTailWs.formatter : Formatter := pure ()
@[combinator_formatter checkColEq] def checkColEq.formatter : Formatter := pure ()
@[combinator_formatter checkColGe] def checkColGe.formatter : Formatter := pure ()
@[combinator_formatter checkColGt] def checkColGt.formatter : Formatter := pure ()
@[combinator_formatter checkLineEq] def checkLineEq.formatter : Formatter := pure ()

@[combinator_formatter eoi] def eoi.formatter : Formatter := pure ()
@[combinator_formatter checkNoImmediateColon] def checkNoImmediateColon.formatter : Formatter := pure ()
@[combinator_formatter skip] def skip.formatter : Formatter := pure ()

@[combinator_formatter pushNone] def pushNone.formatter : Formatter := goLeft
@[combinator_formatter hygieneInfoNoAntiquot] def hygieneInfoNoAntiquot.formatter : Formatter := goLeft

@[combinator_formatter interpolatedStr]
def interpolatedStr.formatter (p : Formatter) : Formatter := do
  visitArgs $ (← getCur).getArgs.reverse.forM fun chunk =>
    match chunk.isLit? interpolatedStrLitKind with
    | some str => push str *> goLeft
    | none     => p

@[combinator_formatter _root_.ite, macro_inline] def ite {_ : Type} (c : Prop) [Decidable c] (t e : Formatter) : Formatter :=
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

register_builtin_option pp.oneline : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) elide all but first line of pretty printer output"
}

def format (formatter : Formatter) (stx : Syntax) : CoreM Format := do
  trace[PrettyPrinter.format.input] "{Std.format stx}"
  let options ← getOptions
  let table := Parser.getTokenTable (← getEnv)
  catchInternalId backtrackExceptionId
    (do
      let (_, st) ← (concat formatter { table, options }).run { stxTrav := .fromSyntax stx }
      let mut f := st.stack[0]!
      if pp.oneline.get options then
        let mut s := f.pretty' options |>.trim
        let lineEnd := s.find (· == '\n')
        if lineEnd < s.endPos then
          s := s.extract 0 lineEnd ++ " [...]"
        -- TODO: preserve `Format.tag`s?
        f := s
      return .fill f)
    (fun _ => throwError "format: uncaught backtrack exception")

def formatCategory (cat : Name) := format <| categoryFormatter cat

def formatTerm := formatCategory `term
def formatTactic := formatCategory `tactic
def formatCommand := formatCategory `command

builtin_initialize
  registerTraceClass `PrettyPrinter.format
  registerTraceClass `PrettyPrinter.format.backtrack (inherited := true)
  registerTraceClass `PrettyPrinter.format.input (inherited := true)

end PrettyPrinter
end Lean
