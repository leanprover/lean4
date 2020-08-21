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

def ppTerm (stx : Syntax) : CoreM Format :=
parenthesizeTerm stx >>= formatTerm

def ppExpr (e : Expr) : MetaM Format :=
delab e >>= Meta.liftCoreM ∘ ppTerm

def ppCommand (stx : Syntax) : CoreM Format :=
parenthesizeCommand stx >>= formatCommand

def ppModule (stx : Syntax) : CoreM Format := do
let header := stx.getArg 0;
f ← format Lean.Parser.Module.header.formatter header;
let cmds := stx.getArgs.extract 1 stx.getArgs.size;
cmds.foldlM (fun f cmd => do
  cmdF ← ppCommand cmd;
  pure $ f ++ "\n\n" ++ cmdF) f

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
let x : MetaM Format := do { Meta.setMCtx mctx; ppExpr e };
let x : MetaM Format := adaptReader (fun (ctx : Meta.Context) => { ctx with lctx := lctx }) x;
let x : IO Format    := (x.run).run env opts;
match unsafeIO x with
| Except.ok  fmt => fmt
| Except.error e => "<pretty printer error: " ++ toString e ++ ">"

@[implementedBy ppExprFnUnsafe]
constant ppExprFn (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : Format := arbitrary _

-- TODO: activate when ready
/-@[init]-/ def registerPPTerm : IO Unit := do
ppExprFnRef.set ppExprFn

end PrettyPrinter
end Lean
