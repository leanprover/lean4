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

-- TODO: replace with quotations where possible
private def const (n : Name) : Syntax :=
Syntax.node `Lean.Parser.Term.id #[Syntax.ident none n.toString.toSubstring n [(n, [])]]

private def app (fn arg : Syntax) : Syntax :=
Syntax.node `Lean.Parser.Term.app #[fn, arg]

private def appN (fn : Syntax) (args : Array Syntax) : Syntax :=
args.foldl app fn

-- TODO: unclear if the following functions could also be useful to other code
private def quoteName : Name → Syntax
| Name.anonymous => const `Lean.Name.anonymous
| Name.str n s _ => appN (const `Lean.mkNameStr) #[quoteName n, mkStxStrLit s]
| Name.num n i _ => appN (const `Lean.mkNameNum) #[quoteName n, mkStxNumLit $ toString i]

private def quoteList : List Syntax → Syntax
| [] => const `List.nil
| (x::xs) => appN (const `List.cons) #[x, quoteList xs]

private def quoteArray : Array Syntax → Syntax
| xs => app (const `List.toArray) $ quoteList xs.toList

private partial def quote (env : Environment) (msc : Syntax) : Syntax → Syntax
| Syntax.ident info rawVal val preresolved =>
  -- TODO: pass scope information
  let ns := Name.anonymous;
  let openDecls := [];
  let preresolved := resolveGlobalName env ns openDecls val <|> preresolved;
  --`(Syntax.ident none (String.toSubstring %(rawVal.toString)) (Name.mkNumeral %val %msc))
  appN (const `Lean.Syntax.ident) #[
    const `Option.none,
    app (const `String.toSubstring) (mkStxStrLit rawVal.toString),
    --appN (const `Lean.Name.mkNumeral) #[quoteName val, msc]
    -- TODO: hygiene
    quoteName val,
    quoteList $ preresolved.map $ fun ⟨n, ss⟩ => appN (const `Prod.mk) #[quoteName n, quoteList $ ss.map mkStxStrLit]
  ]
| Syntax.node `Lean.Parser.Term.antiquot args => args.get! 1
| Syntax.node k args =>
  --`(Syntax.node %k %args...)
  let args := quoteArray $ args.map quote;
  appN (const `Lean.Syntax.node) $ #[quoteName k, args]
| Syntax.atom info val => --`(Syntax.atom none %val)
  appN (const `Lean.Syntax.atom) #[
    const `Option.none,
    mkStxStrLit val
  ]
| Syntax.missing => unreachable!

-- TODO: hygiene
def stxQuot.expand (env : Environment) (stx : Syntax) : Syntax :=
-- `(do msc ← getCurMacroScope; pure %(quote `(msc) quoted))
app (const `HasPure.pure) $ quote env Syntax.missing $ stx.getArg 1

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
  | `strLit => pure $ mkStrLit $ stx.isStrLit.getD ""
  | `numLit => pure $ mkNatLit $ stx.isNatLit.getD 0
  | k => panic! "stxQuot: unimplemented kind " ++ toString k

@[export lean_parse_stx_quot]
def oldParseStxQuot (env : Environment) (input : String) (pos : String.Pos) : Except String (Expr × String.Pos) := do
let c := Parser.mkParserContextCore env input "<foo>";
let c := c.toParserContext env;
let s := Parser.mkParserState c.input;
let s := s.setPos pos;
let s := (Parser.termParser : Parser.Parser).fn (0 : Nat) c s;
let stx := s.stxStack.back;
let stx := app (const `HasPure.pure) $ quote env Syntax.missing stx;
expr ← toPreterm env stx;
match s.errorMsg with
| some errorMsg =>
  Except.error $ toString errorMsg
| none =>
  Except.ok (expr, s.pos)

end Elab
end Lean
