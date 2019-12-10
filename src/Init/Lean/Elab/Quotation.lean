/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Lean.Syntax
import Init.Lean.Elab.ResolveName
import Init.Lean.Parser -- TODO: remove after removing old elaborator

namespace Lean
namespace Elab

/-- A monad that supports syntax quotations. -/
class MonadQuotation (m : Type → Type) :=
-- Get the fresh scope of the current macro invocation
(getCurrMacroScope : m Nat)

/-- Simplistic MonadQuotation that does not guarantee fresh names. -/
abbrev Unhygienic := Id
namespace Unhygienic
instance MonadQuotation : MonadQuotation Unhygienic := ⟨pure 0⟩
def run {α : Type} : Unhygienic α → α := Id.run
end Unhygienic

private def appN (fn : Syntax) (args : Array Syntax) : Syntax :=
args.foldl (fun fn arg => Unhygienic.run `(%%fn %%arg)) fn

-- TODO: unclear if the following functions could also be useful to other code
private def quoteName : Name → Syntax
| Name.anonymous => Unhygienic.run `(Lean.Name.anonymous)
| Name.str n s _ => Unhygienic.run `(Lean.mkNameStr %%(quoteName n) %%(Lean.mkStxStrLit s))
| Name.num n i _ => Unhygienic.run `(Lean.mkNameStr %%(quoteName n) %%(Lean.mkStxNumLit (HasToString.toString i)))

private def quoteList : List Syntax → Syntax
| [] =>      Unhygienic.run `(List.nil)
| (x::xs) => Unhygienic.run `(List.cons %%x %%(quoteList xs))

private def quoteArray : Array Syntax → Syntax
| xs =>
  let stx := quoteList xs.toList;
  Unhygienic.run `(List.toArray %%stx)

private partial def quote (env : Environment) (msc : Syntax) : Syntax → Syntax
| Syntax.ident info rawVal val preresolved =>
  -- TODO: pass scope information
  let ns := Name.anonymous;
  let openDecls := [];
  let preresolved := resolveGlobalName env ns openDecls val <|> preresolved;
  -- TODO: hygiene
  -- `(Name.mkNumeral %%val %%msc)
  let val := quoteName val;
  let args := quoteList $ preresolved.map $ fun ⟨n, ss⟩ => appN (Unhygienic.run `(Prod.mk)) #[quoteName n, quoteList $ ss.map mkStxStrLit];
  Unhygienic.run `(Lean.Syntax.ident Option.none (String.toSubstring %%(Lean.mkStxStrLit (HasToString.toString rawVal))) %%val %%args)
| Syntax.node `Lean.Parser.Term.antiquot args => args.get! 1
| Syntax.node k args =>
  let k := quoteName k;
  let args := quoteArray $ args.map quote;
  Unhygienic.run `(Lean.Syntax.node %%k %%args)
| Syntax.atom info val =>
  Unhygienic.run `(Lean.Syntax.atom Option.none %%(Lean.mkStxStrLit val))
| Syntax.missing => unreachable!

def stxQuot.expand (env : Environment) (stx : Syntax) : Syntax :=
-- TODO: hygiene
-- `(do msc ← getCurMacroScope; pure %(quote `(msc) quoted))
let stx := quote env Syntax.missing $ stx.getArg 1;
Unhygienic.run `(HasPure.pure %%stx)

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
      | (pre,[])::_ => pure $ mkConst pre
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
  | k => panic! "stxQuot: unimplemented kind " ++ toString k

@[export lean_parse_stx_quot]
def oldParseStxQuot (env : Environment) (input : String) (pos : String.Pos) : Except String (Expr × String.Pos) := do
let c := Parser.mkParserContextCore env input "<foo>";
let c := c.toParserContext env;
let s := Parser.mkParserState c.input;
let s := s.setPos pos;
let s := (Parser.termParser : Parser.Parser).fn (0 : Nat) c s;
let stx := s.stxStack.back;
let stx := quote env Syntax.missing stx;
let stx := Unhygienic.run `(HasPure.pure %%stx);
expr ← toPreterm env stx;
match s.errorMsg with
| some errorMsg =>
  Except.error $ toString errorMsg
| none =>
  Except.ok (expr, s.pos)

end Elab
end Lean
