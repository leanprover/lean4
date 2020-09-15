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

def ppExpr (currNamespace : Name) (openDecls : List OpenDecl) (e : Expr) : MetaM Format := do
stx ← delab currNamespace openDecls e;
liftM $ ppTerm stx

def ppCommand (stx : Syntax) : CoreM Format :=
parenthesizeCommand stx >>= formatCommand

def ppModule (stx : Syntax) : CoreM Format := do
parenthesize Lean.Parser.Module.module.parenthesizer stx >>= format Lean.Parser.Module.module.formatter

private partial def noContext : MessageData → MessageData
| MessageData.withContext ctx msg => noContext msg
| msg => msg

def ppExprFn (ppCtx : PPContext) (e : Expr) : IO Format := do
let pp : MetaM Format := adaptExcept (fun ex => match ex with
  -- strip context (including environments with registered pretty printers) to prevent infinite recursion when pretty printing pretty printer error
  | Exception.error ref msg => Exception.error ref (noContext msg)
  | e                       => e)
  (ppExpr ppCtx.currNamespace ppCtx.openDecls e);
(fmt, _, _) ← pp.toIO { options := ppCtx.opts } { env := ppCtx.env } { lctx := ppCtx.lctx } { mctx := ppCtx.mctx };
pure fmt

@[init] def registerPPTerm : IO Unit := do
ppExprFnRef.set ppExprFn

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `PrettyPrinter;
pure ()

end PrettyPrinter
end Lean
