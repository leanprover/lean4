/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Lean.Syntax
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Term
import Init.Lean.Parser -- TODO: remove after removing old elaborator

namespace Lean

/-- A monad that supports syntax quotations. -/
class MonadQuotation (m : Type → Type) :=
-- Get the fresh scope of the current macro invocation
(getCurrMacroScope : m Nat)
-- Execute action in a new macro invocation context
(withFreshMacroScope {α : Type} : m α → m α)
export MonadQuotation

/-- Simplistic MonadQuotation that does not guarantee globally fresh names. It is only safe
    if the syntax quotations do not introduce bindings around antiquotations, and
    if references to globals are prefixed with `_root_.`. -/
abbrev Unhygienic := ReaderT (List Nat) $ StateM Nat
namespace Unhygienic
instance MonadQuotation : MonadQuotation Unhygienic := {
  getCurrMacroScope := do
    stack ← read;
    pure $ stack.head!,
  withFreshMacroScope := fun α x => do
    fresh ← modifyGet (fun n => (n, n + 1));
    adaptReader (fun stack => fresh::stack) x
}
protected def run {α : Type} (x : Unhygienic α) : α := run x [0] 1
end Unhygienic

/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class HasQuote (α : Type) :=
(quote : α → Syntax)

export HasQuote (quote)

instance Syntax.HasQuote : HasQuote Syntax := ⟨id⟩
instance String.HasQuote : HasQuote String := ⟨mkStxStrLit⟩
instance Nat.HasQuote : HasQuote Nat := ⟨fun n => mkStxNumLit $ toString n⟩

private def quoteName : Name → Syntax
| Name.anonymous => Unhygienic.run `(_root_.Lean.Name.anonymous)
| Name.str n s _ => Unhygienic.run `(_root_.Lean.mkNameStr %%(quoteName n) %%(Lean.HasQuote.quote s))
| Name.num n i _ => Unhygienic.run `(_root_.Lean.mkNameStr %%(quoteName n) %%(Lean.HasQuote.quote i))

instance Name.HasQuote : HasQuote Name := ⟨quoteName⟩

private def appN (fn : Syntax) (args : Array Syntax) : Syntax :=
args.foldl (fun fn arg => Unhygienic.run `(%%fn %%arg)) fn

instance Prod.HasQuote {α β : Type} [HasQuote α] [HasQuote β] : HasQuote (α × β) :=
⟨fun ⟨a, b⟩ => Unhygienic.run `(_root_.Prod.mk %%(Lean.HasQuote.quote a) %%(Lean.HasQuote.quote b))⟩

private def quoteList {α : Type} [HasQuote α] : List α → Syntax
| [] =>      Unhygienic.run `(_root_.List.nil)
| (x::xs) => Unhygienic.run `(_root_.List.cons %%(Lean.HasQuote.quote x) %%(quoteList xs))

instance List.HasQuote {α : Type} [HasQuote α] : HasQuote (List α) := ⟨quoteList⟩

instance Array.HasQuote {α : Type} [HasQuote α] : HasQuote (Array α) :=
⟨fun xs => let stx := quote xs.toList; Unhygienic.run `(_root_.List.toArray %%stx)⟩

namespace Elab
namespace Term

instance TermElabM.MonadQuotation : MonadQuotation TermElabM := {
-- FIXME: actually allocate macro scopes when we actually make use of them
  getCurrMacroScope := pure 0,
  withFreshMacroScope := fun α => id
}

private partial def quoteSyntax {m : Type → Type} [Monad m] [MonadQuotation m] (env : Environment) (msc : Syntax) : Nat → Syntax → m Syntax
| _, Syntax.ident info rawVal val preresolved =>
  -- TODO: pass scope information
  let ns := Name.anonymous;
  let openDecls := [];
  let preresolved := resolveGlobalName env ns openDecls val <|> preresolved;
  -- TODO: hygiene
  -- `(Name.mkNumeral %%val %%msc)
  let val := quote val;
  let args := quote preresolved;
  `(Lean.Syntax.ident Option.none (String.toSubstring %%(Lean.mkStxStrLit (HasToString.toString rawVal))) %%val %%args)
| 0, Syntax.node `Lean.Parser.Term.antiquot args => pure $ args.get! 1
| lvl, Syntax.node k args => do
  let lvl := match k with
    | `Lean.Parser.Term.stxQuot => lvl + 1
    | `Lean.Parser.Term.antiquot => lvl - 1
    | _ => lvl;
  let k := quote k;
  args ← quote <$> args.mapM (quoteSyntax lvl);
  `(Lean.Syntax.node %%k %%args)
| _, Syntax.atom info val =>
  `(Lean.Syntax.atom Option.none %%(Lean.mkStxStrLit val))
| _, Syntax.missing => unreachable!

def stxQuot.expand {m : Type → Type} [Monad m] [MonadQuotation m] (env : Environment) (stx : Syntax) : m Syntax := do
  -- TODO: hygiene
  -- `(do msc ← getCurMacroScope; pure %(quote `(msc) quoted))
  stx ← quoteSyntax env Syntax.missing 0 $ stx.getArg 1;
  `(HasPure.pure %%stx)

@[builtinTermElab stxQuot] def elabStxQuot : TermElab :=
fun stx expectedType? => do
  env ← getEnv;
  stx ← stxQuot.expand env (stx.getArg 1);
  elabTerm stx expectedType?

-- REMOVE with old frontend
private partial def toPreterm (env : Environment) : Syntax → Except String Expr
| stx =>
  let args := stx.getArgs;
  match stx.getKind with
  | `Lean.Parser.Term.id =>
    match args.get! 0 with
    | Syntax.ident _ _ val preresolved =>
      -- TODO: pass scope information
      let ns := Name.anonymous;
      let openDecls := [];
      let resolved := resolveGlobalName env ns openDecls val <|> preresolved;
      match resolved with
      | (pre,[])::_ => pure $ Lean.mkConst pre
      | [] => pure $ mkFVar val
      | _ => throw "stxQuot: unimplemented: projection notation"
    | _ => unreachable!
  | `Lean.Parser.Term.app => do
    fn ← toPreterm $ args.get! 0;
    arg ← toPreterm $ args.get! 1;
    pure $ mkApp fn arg
  | `Lean.Parser.Term.paren => toPreterm $ (args.get! 1).getArg 0
  | `strLit => pure $ mkStrLit $ stx.isStrLit?.getD ""
  | `numLit => pure $ mkNatLit $ stx.isNatLit?.getD 0
  | k => throw $ "stxQuot: unimplemented kind " ++ toString k

@[export lean_parse_expr]
def oldParseExpr (env : Environment) (input : String) (pos : String.Pos) : Except String (Syntax × String.Pos) := do
let c := Parser.mkParserContextCore env input "<foo>";
let c := c.toParserContext env;
let s := Parser.mkParserState c.input;
let s := s.setPos pos;
let s := (Parser.termParser : Parser.Parser).fn (0 : Nat) c s;
let stx := s.stxStack.back;
match s.errorMsg with
| some errorMsg =>
  Except.error $ toString errorMsg
| none =>
  Except.ok (stx, s.pos)

@[export lean_expand_stx_quot]
unsafe def oldExpandStxQuot (env : Environment) (stx : Syntax) : Except String Expr := do
let stx := Unhygienic.run $ stxQuot.expand env stx;
toPreterm env stx

end Term
end Elab
end Lean
