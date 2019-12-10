/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Lean.Syntax
import Init.Lean.Elab.ResolveName

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

end Elab
end Lean
