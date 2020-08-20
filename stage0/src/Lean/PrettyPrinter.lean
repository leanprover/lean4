/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter

namespace Lean
namespace PrettyPrinter

def ppTerm (table : Parser.TokenTable) : Syntax → MetaM Format :=
parenthesizeTerm >=> formatTerm table

def ppExpr (table : Parser.TokenTable) : Expr → MetaM Format :=
delab >=> ppTerm table

def ppCommand (table : Parser.TokenTable) : Syntax → MetaM Format :=
parenthesizeCommand >=> formatCommand table

def ppModule (table : Parser.TokenTable) (stx : Syntax) : MetaM Format := do
let header := stx.getArg 0;
f ← arbitrary _; --format table (mkConst `Lean.Parser.Module.header) header;
let cmds := stx.getArgs.extract 1 stx.getArgs.size;
cmds.foldlM (fun f cmd => do
  cmdF ← ppCommand table cmd;
  pure $ f ++ "\n\n" ++ cmdF) f

-- TODO: activate when ready
/-@[init]-/ def registerPPTerm : IO Unit := do
table ← Parser.builtinTokenTable.get;
ppExprFnRef.set $ fun env mctx lctx opts e => match
  ppExpr table e { currRecDepth := 0, maxRecDepth := 1000, lctx := lctx, config := { opts := opts } } { env := env, mctx := mctx } with
  | EStateM.Result.ok f st    => f
  | EStateM.Result.error e st => "<pretty printer error: " ++ toString e ++ ">"

end PrettyPrinter
end Lean
