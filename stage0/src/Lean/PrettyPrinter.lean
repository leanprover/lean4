/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter
import Lean.Parser.Module

namespace Lean
namespace PrettyPrinter

def ppTerm (stx : Syntax) : CoreM Format :=
parenthesizeTerm stx >>= formatTerm

def ppExpr (e : Expr) : MetaM Format := do
stx ← delab e;
liftM $ ppTerm stx

def ppCommand (stx : Syntax) : CoreM Format :=
parenthesizeCommand stx >>= formatCommand

def ppModule (stx : Syntax) : CoreM Format := do
parenthesize Lean.Parser.Module.module.parenthesizer stx >>= format Lean.Parser.Module.module.formatter

/-
Kha: this is a temporary hack since ppExprFnRef contains a pure function.
Possible solution: we change the type of
```
abbrev PPExprFn := Environment → MetavarContext → LocalContext → Options → Expr → Format
```
to
```
abbrev PPExprFn := Environment → MetavarContext → LocalContext → Options → Expr → CoreM Format
```
-/
unsafe def ppExprFnUnsafe (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : Format :=
match unsafeIO $ (ppExpr e).toIO { options := opts } { env := env } { lctx := lctx } { mctx := mctx }  with
| Except.ok  (fmt, _, _) => fmt
| Except.error e         => "<pretty printer error: " ++ toString e ++ ">"

@[implementedBy ppExprFnUnsafe]
constant ppExprFn (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : Format := arbitrary _

-- TODO: activate when ready
/-@[init]-/ def registerPPTerm : IO Unit := do
ppExprFnRef.set ppExprFn

end PrettyPrinter
end Lean
