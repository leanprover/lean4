/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-!
The formatter turns a `Syntax` tree into a `Format` object, inserting both mandatory whitespace (to separate adjacent
tokens) as well as "pretty" optional whitespace.

The basic approach works much like the parenthesizer: A right-to-left traversal over the syntax tree and the parser that
produced it, driven by parser-specific handlers registered via an attribute. The traversal is right-to-left so that when
emitting a token, we already know the text following it and can decide whether or not whitespace between the two is
necessary.
-/

import Lean.Parser
import Lean.Meta.ReduceEval
import Lean.Elab.Quotation
import Lean.ParserCompiler.Attribute

namespace Lean
namespace PrettyPrinter
namespace Formatter

structure Context :=
(table : Parser.TokenTable)

structure State :=
(stxTrav  : Syntax.Traverser)
-- Textual content of `stack` up to the first whitespace (not enclosed in an escaped ident). We assume that the textual
-- content of `stack` is modified only by `pushText` and `pushLine`, so `leadWord` is adjusted there accordingly.
(leadWord : String := "")
-- Stack of generated Format objects, analogous to the Syntax stack in the parser.
-- Note, however, that the stack is reversed because of the right-to-left traversal.
(stack    : Array Format := #[])

end Formatter

abbrev FormatterM := ReaderT Formatter.Context $ StateT Formatter.State MetaM

abbrev Formatter := Expr → FormatterM Unit

unsafe def mkFormatterAttribute : IO (KeyedDeclsAttribute Formatter) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinFormatter,
  name := `formatter,
  descr := "Register a formatter for a parser.

[formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.",
  valueTypeName := `Lean.PrettyPrinter.Formatter,
  evalKey := fun builtin env args => match attrParamSyntaxToIdentifier args with
    | some id =>
      -- `isValidSyntaxNodeKind` is updated only in the next stage for new `[builtin*Parser]`s, but we try to
      -- synthesize a formatter for it immediately, so we just check for a declaration in this case
      if (builtin && (env.find? id).isSome) || Parser.isValidSyntaxNodeKind env id then pure id
      else throw ("invalid [formatter] argument, unknown syntax kind '" ++ toString id ++ "'")
    | none    => throw "invalid [formatter] argument, expected identifier"
} `Lean.PrettyPrinter.formatterAttribute
@[init mkFormatterAttribute] constant formatterAttribute : KeyedDeclsAttribute Formatter := arbitrary _

unsafe def mkCombinatorFormatterAttribute : IO ParserCompiler.CombinatorAttribute :=
ParserCompiler.registerCombinatorAttribute
  `combinatorFormatter
  "Register a formatter for a parser combinator.

[combinatorFormatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.
Note that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.
The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced
with `Formatter` in the parameter types."
@[init mkCombinatorFormatterAttribute] constant combinatorFormatterAttribute : ParserCompiler.CombinatorAttribute := arbitrary _

namespace Formatter

open Lean.Meta
open Lean.Format

instance FormatterM.monadTraverser : Syntax.MonadTraverser FormatterM := ⟨{
  get       := State.stxTrav <$> get,
  set       := fun t => modify (fun st => { st with stxTrav := t }),
  modifyGet := fun _ f => modifyGet (fun st => let (a, t) := f st.stxTrav; (a, { st with stxTrav := t })) }⟩

open Syntax.MonadTraverser

def getStack : FormatterM (Array Format) := do
st ← get;
pure st.stack

def getStackSize : FormatterM Nat := do
stack ← getStack;
pure stack.size

def setStack (stack : Array Format) : FormatterM Unit :=
modify fun st => { st with stack := stack }

def push (f : Format) : FormatterM Unit :=
modify fun st => { st with stack := st.stack.push f }

/-- Execute `x` at the right-most child of the current node, if any, then advance to the left. -/
def visitArgs (x : FormatterM Unit) : FormatterM Unit := do
stx ← getCur;
when (stx.getArgs.size > 0) $
  goDown (stx.getArgs.size - 1) *> x <* goUp;
goLeft

/-- Execute `x`, pass array of generated Format objects to `fn`, and push result. -/
def fold (fn : Array Format → Format) (x : FormatterM Unit) : FormatterM Unit := do
sp ← getStackSize;
x;
stack ← getStack;
let f := fn $ stack.extract sp stack.size;
setStack $ (stack.shrink sp).push f

/-- Execute `x` and concatenate generated Format objects. -/
def concat (x : FormatterM Unit) : FormatterM Unit := do
fold (Array.foldl (fun acc f => f ++ acc) Format.nil) x

def concatArgs (x : FormatterM Unit) : FormatterM Unit :=
concat (visitArgs x)

set_option class.instance_max_depth 100 -- TODO delete

/--
  Call an appropriate `[formatter]` depending on the `Parser` `Expr` `p`. After the call, the traverser position
  should be to the left of all nodes produced by `p`, or at the left-most child if there are no other nodes left. -/
partial def visit : Formatter | p => do
stx ← getCur;
-- do reductions _except_ for definition unfolding
p ← liftM $ whnfCore p;
trace! `PrettyPrinter.format ("formatting" ++ MessageData.nest 2 (line ++ stx) ++ line ++ "using" ++ MessageData.nest 2 (line ++ p));
sp ← getStackSize;
let c := Expr.constName? p.getAppFn;
-- TODO: delete after adapting parenthesizer compiler approach
let p := match c with
| `ident => mkConst `Lean.Parser.Term.ident
| `charLit => mkConst `Lean.Parser.Term.char
| `numLit => mkConst `Lean.Parser.Term.num
| `strLit => mkConst `Lean.Parser.Term.str
| _ => p;
env ← liftM getEnv;
match c >>= (formatterAttribute.ext.getState env).table.find? with
| some (f::_) => do
  -- call first matching formatter
  f p
| _           =>
  -- `choice` is not an actual parser, so special-case it here
  if c == some `choice then do
    visitArgs do {
      stx ← getCur;
      sp ← getStackSize;
      stx.getArgs.forM fun _ => visit (mkConst stx.getKind);
      stack ← getStack;
      when (stack.size > sp && stack.anyRange sp stack.size fun f => pretty f != pretty (stack.get! sp))
        panic! "Formatter.visit: inequal choice children";
      -- discard all but one child format
      setStack $ stack.extract 0 (sp+1)
    }
  else do {
    -- (try to) unfold definition and recurse
    some p' ← liftM $ unfoldDefinition? p
      | throw $ Exception.other Syntax.missing $ "no known formatter for '" ++ toString p ++ "'";
    visit p'
  };
stack ← getStack;
trace! `PrettyPrinter.format (" => " ++ (stack.extract sp stack.size).foldl (fun acc f => repr (toString f) ++ " " ++ acc) "")

open Lean.Parser

@[builtinFormatter categoryParser]
def categoryParser.formatter : Formatter | p => do
stx ← getCur;
-- visit `(mkCategoryAntiquotParser $(p.getArg! 0) <|> $(mkConst stx.getKind))
visit (mkAppN (mkConst `Lean.Parser.orelse) #[
  mkApp (mkConst `Lean.Parser.mkCategoryAntiquotParser) (p.getArg! 0),
  mkConst stx.getKind])

@[builtinFormatter termParser]
def termParser.formatter : Formatter | p => do
stx ← getCur;
-- this can happen at `termParser <|> many1 commandParser` in `Term.stxQuot`
if stx.getKind == nullKind then
  throw $ Exception.other Syntax.missing "BACKTRACK"
else
  categoryParser.formatter p

@[builtinFormatter withAntiquot]
def withAntiquot.formatter : Formatter | p =>
-- deoptimize
visit (mkAppN (mkConst `Lean.Parser.orelse) #[p.getArg! 0, p.getArg! 1])

@[builtinFormatter try]
def try.formatter : Formatter | p =>
visit p.appArg!

@[builtinFormatter andthen]
def andthen.formatter : Formatter | p =>
visit (p.getArg! 1) *> visit (p.getArg! 0)

def checkKind (k : SyntaxNodeKind) : FormatterM Unit := do
stx ← getCur;
when (k != stx.getKind) $ do {
  trace! `PrettyPrinter.format.backtrack ("unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'");
  -- HACK; see `orelse.formatter`
  throw $ Exception.other Syntax.missing "BACKTRACK"
}

@[builtinFormatter node]
def node.formatter : Formatter | p => do
k ← liftM $ reduceEval $ p.getArg! 0;
checkKind k;
concatArgs $ visit p.appArg!

@[builtinFormatter trailingNode]
def trailingNode.formatter : Formatter | p => do
k ← liftM $ reduceEval $ p.getArg! 0;
checkKind k;
concatArgs do
  visit p.appArg!;
  -- leading term, not actually produced by `p`
  categoryParser.formatter p

def parseToken (s : String) : FormatterM ParserState := do
ctx ← read;
env ← liftM getEnv;
pure $ Parser.tokenFn { input := s, fileName := "", fileMap := FileMap.ofString "", prec := 0, env := env, tokens := ctx.table } (Parser.mkParserState s)

def pushToken (tk : String) : FormatterM Unit := do
st ← get;
-- If there is no space between `tk` and the next word, compare parsing `tk` with and without the next word
if st.leadWord != "" && tk.trimRight == tk then do
  t1 ← parseToken tk.trimLeft;
  t2 ← parseToken $ tk.trimLeft ++ st.leadWord;
  if t1.pos == t2.pos then do
    -- same result => use `tk` as is, extend `leadWord` if not prefixed by whitespace
    modify fun st => { st with leadWord := if tk.trimLeft == tk then tk ++ st.leadWord else "" };
    push tk
  else do
    -- different result => add space
    modify fun st => { st with leadWord := if tk.trimLeft == tk then tk else "" };
    push $ tk ++ " "
else do {
  -- already separated => use `tk` as is
  modify fun st => { st with leadWord := if tk.trimLeft == tk then tk else "" };
  push tk
}

@[builtinFormatter symbol]
def symbol.formatter : Formatter | p => do
let sym := p.getArg! 0;
sym ← liftM $ reduceEval sym;
pushToken sym;
goLeft

@[builtinFormatter symbolNoWs] def symbolNoWs.formatter := symbol.formatter
@[builtinFormatter unicodeSymbol] def unicodeSymbol.formatter := symbol.formatter
@[builtinFormatter nonReservedSymbol] def nonReservedSymbol.formatter := symbol.formatter

@[builtinFormatter identNoAntiquot]
def identNoAntiquot.formatter : Formatter | _ => do
checkKind identKind;
stx ← getCur;
let s := stx.getId.toString;
-- try to parse `s` as-is; if it fails, escape
pst ← parseToken s;
let s := if pst.stxStack == #[stx] then s else match stx.getId with
  | Name.str Name.anonymous s _ => "«" ++ s ++ "»"
  | _                           => panic! "unimplemented: escaping non-atomic identifiers (is anyone even using those?)";
pushToken s;
goLeft

@[builtinFormatter rawIdent] def rawIdent.formatter : Formatter | _ => do
checkKind identKind;
stx ← getCur;
pushToken stx.getId.toString;
goLeft

def visitAtom (k : SyntaxNodeKind) : Formatter | p => do
stx ← getCur;
when (k != Name.anonymous) $
  checkKind k;
Syntax.atom _ val ← pure $ stx.ifNode (fun n => n.getArg 0) (fun _ => stx)
  | throw $ Exception.other Syntax.missing $ "not an atom: " ++ toString stx;
pushToken val;
goLeft

@[builtinFormatter charLitNoAntiquot] def charLitNoAntiquot.formatter := visitAtom charLitKind
@[builtinFormatter strLitNoAntiquot] def strLitNoAntiquot.formatter := visitAtom strLitKind
@[builtinFormatter nameLitNoAntiquot] def nameLitNoAntiquot.formatter := visitAtom nameLitKind
@[builtinFormatter numLitNoAntiquot] def numLitNoAntiquot.formatter := visitAtom numLitKind
@[builtinFormatter fieldIdx] def fieldIdx.formatter := visitAtom fieldIdxKind

@[builtinFormatter many]
def many.formatter : Formatter | p => do
stx ← getCur;
concatArgs $ stx.getArgs.size.forM $ fun _ => visit (p.getArg! 0)

@[builtinFormatter many1] def many1.formatter : Formatter | p => do
stx ← getCur;
if stx.getKind == nullKind then do
  many.formatter p
else
  -- can happen with `unboxSingleton = true`
  visit (p.getArg! 0)

@[builtinFormatter Parser.optional]
def optional.formatter : Formatter | p => do
concatArgs $ visit (p.getArg! 0)

@[builtinFormatter sepBy]
def sepBy.formatter : Formatter | p => do
stx ← getCur;
concatArgs $ (List.range stx.getArgs.size).reverse.forM $ fun i => visit (p.getArg! (i % 2))

@[builtinFormatter sepBy1] def sepBy1.formatter := sepBy.formatter

@[builtinFormatter orelse] def orelse.formatter : Formatter | p => do
st ← get;
-- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
-- them in turn. Uses the syntax traverser non-linearly!
catch (visit (p.getArg! 0)) $ fun e => match e with
  | Exception.other _ "BACKTRACK" => set st *> visit (p.getArg! 1)
  | _                             => throw e

@[builtinFormatter withPosition] def withPosition.formatter : Formatter | p => do
-- call closure with dummy position
visit $ mkApp (p.getArg! 0) (mkConst `sorryAx [levelZero])

@[builtinFormatter setExpected] def setExpected.formatter : Formatter | p => visit (p.getArg! 1)

@[builtinFormatter checkWsBefore] def checkWsBefore.formatter : Formatter | p => do
modify fun st => { st with leadWord := "" };
push " "

@[builtinFormatter checkPrec] def checkPrec.formatter : Formatter | p => pure ()
@[builtinFormatter checkStackTop] def checkStackTop.formatter : Formatter | p => pure ()
@[builtinFormatter checkNoWsBefore] def checkNoWsBefore.formatter : Formatter | p => pure ()
@[builtinFormatter checkTailWs] def checkTailWs.formatter : Formatter | p => pure ()
@[builtinFormatter checkColGe] def checkColGe.formatter : Formatter | p => pure ()
@[builtinFormatter checkNoImmediateColon] def checkNoImmediateColon.formatter : Formatter | p => pure ()

@[builtinFormatter pushNone] def pushNone.formatter : Formatter | p => goLeft

open Lean.Parser.Command
@[builtinFormatter commentBody] def commentBody.formatter := visitAtom Name.anonymous

-- TODO: delete with old frontend
@[builtinFormatter quotedSymbol] def quotedSymbol.formatter : Formatter | p => do
checkKind quotedSymbolKind;
concatArgs do
  push "`"; goLeft;
  visitAtom Name.anonymous p;
  push "`"; goLeft

@[builtinFormatter unquotedSymbol] def unquotedSymbol.formatter := visitAtom Name.anonymous

end Formatter

def format (table : Parser.TokenTable) (parser : Expr) (stx : Syntax) : MetaM Format := Meta.withAtLeastTransparency Meta.TransparencyMode.default do
(_, st) ← Formatter.visit parser { table := table } { stxTrav := Syntax.Traverser.fromSyntax stx };
pure $ st.stack.get! 0

def formatTerm (table) := format table (mkApp (mkConst `Lean.Parser.termParser) (mkNatLit 0))

def formatCommand (table) := format table (mkApp (mkConst `Lean.Parser.commandParser) (mkNatLit 0))

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `PrettyPrinter.format;
pure ()

end PrettyPrinter
end Lean
