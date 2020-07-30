/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

import Lean.Parser
import Lean.Meta
import Lean.Elab.Quotation

namespace Lean
namespace PrettyPrinter
namespace Formatter

structure Context :=
(table : Parser.TokenTable)

structure State :=
(stxTrav : Syntax.Traverser)
(leadWord : String := "")

end Formatter

abbrev FormatterM := ReaderT Formatter.Context $ StateT Formatter.State MetaM

abbrev Formatter := Expr → FormatterM Format

unsafe def mkFormatterAttribute : IO (KeyedDeclsAttribute Formatter) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinFormatter,
  name := `formatter,
  descr := "Register a formatter.

[formatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.",
  valueTypeName := `Lean.PrettyPrinter.Formatter,
  evalKey := fun env args => match attrParamSyntaxToIdentifier args with
    | some id => match env.find? id with
      | some _ => pure id
      | none   => throw ("invalid [formatter] argument, unknown identifier '" ++ toString id ++ "'")
    | none    => throw "invalid [formatter] argument, expected identifier"
} `Lean.PrettyPrinter.formatterAttribute
@[init mkFormatterAttribute] constant formatterAttribute : KeyedDeclsAttribute Formatter := arbitrary _

namespace Formatter

open Lean.Meta
open Lean.Format

instance FormatterM.monadTraverser : Syntax.MonadTraverser FormatterM := ⟨{
  get       := State.stxTrav <$> get,
  set       := fun t => modify (fun st => { st with stxTrav := t }),
  modifyGet := fun _ f => modifyGet (fun st => let (a, t) := f st.stxTrav; (a, { st with stxTrav := t })) }⟩

open Syntax.MonadTraverser

/-- Execute `x` at the right-most child of the current node, if any, then advance to the left. -/
def visitArgs (x : FormatterM Format) : FormatterM Format := do
stx ← getCur;
f ← if (stx.getArgs.size > 0)
  then goDown (stx.getArgs.size - 1) *> x <* goUp
  else pure Format.nil;
goLeft;
pure f

def concatArgs (x : FormatterM Format) : FormatterM Format := do
stx ← getCur;
visitArgs $ Array.foldl Format.append Format.nil <$> stx.getArgs.mapM fun _ => x

/--
  Call an appropriate `[formatter]` depending on the `Parser` `Expr` `p`. After the call, the traverser position
  should be to the left of all nodes produced by `p`, or at the left-most child if there are no other nodes left. -/
partial def visit : Formatter | p => do
stx ← getCur;
-- do reductions _except_ for definition unfolding
p ← liftM $ whnfCore p;
trace! `PrettyPrinter.format ("formatting" ++ MessageData.nest 2 (line ++ stx) ++ line ++ "using" ++ MessageData.nest 2 (line ++ p));
let c := Expr.constName? p.getAppFn;
env ← liftM getEnv;
f ← match c >>= (formatterAttribute.ext.getState env).table.find? with
| some (f::_) => do
  -- call first matching formatter
  f p
| _           =>
  -- `choice` is not an actual parser, so special-case it here
  if c == some `choice then do
    visitArgs do {
      stx ← getCur;
      fs ← stx.getArgs.mapM fun _ => visit (mkConst stx.getKind);
      when (¬ fs.all fun f => pretty f == pretty (fs.get! 0))
        panic! "Formatter.visit: inequal choice children";
      pure $ fs.get! 0
    }
  else do {
    -- (try to) unfold definition and recurse
    some p' ← liftM $ unfoldDefinition? p
      | throw $ Exception.other $ "no known formatter for '" ++ toString p ++ "'";
    visit p'
  };
trace! `PrettyPrinter.format ("=> " ++ f);
pure f

open Lean.Parser

def visitAntiquot : Formatter | _ => do
stx ← getCur;
if Elab.Term.Quotation.isAntiquot stx then
  visit (mkAppN (mkConst `Lean.Parser.mkAntiquot) #[mkNatLit 0, mkNatLit 0])
else
  throw $ Exception.other $ "not an antiquotation"

@[builtinFormatter categoryParser]
def categoryParser.formatter : Formatter | p => visitAntiquot p <|> do
stx ← getCur;
visit (mkConst stx.getKind)

@[builtinFormatter termParser]
def termParser.formatter : Formatter | p => do
stx ← getCur;
-- this can happen at `termParser <|> many1 commandParser` in `Term.stxQuot`
if stx.getKind == nullKind then
  throw $ Exception.other "BACKTRACK"
else
  categoryParser.formatter p

@[builtinFormatter withAntiquot]
def withAntiquot.formatter : Formatter | p =>
visitAntiquot p <|> visit (p.getArg! 1)

@[builtinFormatter try]
def try.formatter : Formatter | p =>
visit p.appArg!

@[builtinFormatter andthen]
def andthen.formatter : Formatter | p => do
f2 ← visit (p.getArg! 1);
f1 ← visit (p.getArg! 0);
pure $ f1 ++ f2

@[builtinFormatter node]
def node.formatter : Formatter | p => do
stx ← getCur;
k ← liftM $ reduceEval $ p.getArg! 0;
when (k != stx.getKind) $ do {
  trace! `PrettyPrinter.format.backtrack ("unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'");
  -- HACK; see `orelse.formatter`
  throw $ Exception.other "BACKTRACK"
};
visitArgs $ visit p.appArg!

@[builtinFormatter checkPrec]
def checkPrec.formatter : Formatter | p => pure Format.nil

@[builtinFormatter trailingNode]
def trailingNode.formatter : Formatter | p => do
stx ← getCur;
k ← liftM $ reduceEval $ p.getArg! 0;
when (k != stx.getKind) $ do {
  trace! `PrettyPrinter.format.backtrack ("unexpected node kind '" ++ toString stx.getKind ++ "', expected '" ++ toString k ++ "'");
  -- HACK; see `orelse.formatter`
  throw $ Exception.other "BACKTRACK"
};
visitArgs do
  f2 ← visit p.appArg!;
  -- leading term, not actually produced by `p`
  f1 ← categoryParser.formatter p;
  pure $ f1 ++ f2

def visitToken (tk : String) : FormatterM Format := do
-- TODO: use leadWord
-- TODO: (try to) preserve whitespace
goLeft;
pure tk

@[builtinFormatter symbol]
def symbol.formatter : Formatter | p => do
let sym := p.getArg! 0;
sym ← liftM $ reduceEval sym;
visitToken sym

@[builtinFormatter symbolNoWs] def symbolNoWs.formatter := symbol.formatter
@[builtinFormatter unicodeSymbol] def unicodeSymbol.formatter := symbol.formatter

@[builtinFormatter identNoAntiquot]
def identNoAntiquot.formatter : Formatter | _ => do
stx ← getCur;
-- TODO: pretty-print Name using «»
visitToken stx.getId.toString

@[builtinFormatter rawIdent] def rawIdent.formatter := identNoAntiquot.formatter
@[builtinFormatter nonReservedSymbol] def nonReservedSymbol.formatter := identNoAntiquot.formatter

def visitAtom : Formatter | p => do
stx ← getCur;
Syntax.atom _ val ← pure $ stx.getArg 0
  | throw $ Exception.other $ "not an atom: " ++ toString stx;
goLeft;
pure val

@[builtinFormatter charLitNoAntiquot] def charLitNoAntiquot.formatter := visitAtom
@[builtinFormatter strLitNoAntiquot] def strLitNoAntiquot.formatter := visitAtom
@[builtinFormatter nameLitNoAntiquot] def nameLitNoAntiquot.formatter := visitAtom
@[builtinFormatter numLitNoAntiquot] def numLitNoAntiquot.formatter := visitAtom
@[builtinFormatter fieldIdx] def fieldIdx.formatter := visitAtom

@[builtinFormatter many]
def many.formatter : Formatter | p =>
concatArgs $ visit (p.getArg! 0)

@[builtinFormatter many1] def many1.formatter : Formatter | p => do
stx ← getCur;
if stx.getKind == nullKind then
  concatArgs $ visit (p.getArg! 0)
else
  -- can happen with `unboxSingleton = true`
  visit (p.getArg! 0)

@[builtinFormatter Parser.optional]
def optional.formatter : Formatter | p => do
visitArgs $ visit (p.getArg! 0)

@[builtinFormatter sepBy]
def sepBy.formatter : Formatter | p => do
stx ← getCur;
concatArgs do
  idx ← getIdx;
  visit (p.getArg! (idx % 2))

@[builtinFormatter sepBy1] def sepBy1.formatter := sepBy.formatter

@[builtinFormatter orelse] def orelse.formatter : Formatter | p => do
st ← get;
-- HACK: We have no (immediate) information on which side of the orelse could have produced the current node, so try
-- them in turn. Uses the syntax traverser non-linearly!
catch (visit (p.getArg! 0)) $ fun e => match e with
  | Exception.other "BACKTRACK" => set st *> visit (p.getArg! 1)
  | _                           => throw e

@[builtinFormatter withPosition] def withPosition.formatter : Formatter | p => do
-- call closure with dummy position
visit $ mkApp (p.getArg! 0) (mkConst `sorryAx [levelZero])

@[builtinFormatter checkStackTop] def checkStackTop.formatter : Formatter | p => pure Format.nil
@[builtinFormatter checkWsBefore] def checkWsBefore.formatter : Formatter | p => pure Format.nil
@[builtinFormatter checkNoWsBefore] def checkNoWsBefore.formatter : Formatter | p => pure Format.nil
@[builtinFormatter checkTailWs] def checkTailWs.formatter : Formatter | p => pure Format.nil
@[builtinFormatter checkColGe] def checkColGe.formatter : Formatter | p => pure Format.nil

open Lean.Parser.Command
@[builtinFormatter commentBody] def commentBody.formatter := visitAtom
@[builtinFormatter quotedSymbol] def quotedSymbol.formatter := visitAtom
@[builtinFormatter unquotedSymbol] def unquotedSymbol.formatter := visitAtom

end Formatter

def format (table : Parser.TokenTable) (parser : Expr) (stx : Syntax) : MetaM Format := do
(f, _) ← Formatter.visit parser { table := table } { stxTrav := Syntax.Traverser.fromSyntax stx };
pure f

def formatTerm (table) := format table (mkApp (mkConst `Lean.Parser.termParser) (mkNatLit 0))

def formatCommand (table) := format table (mkApp (mkConst `Lean.Parser.commandParser) (mkNatLit 0))

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `PrettyPrinter.format;
pure ()

end PrettyPrinter
end Lean
