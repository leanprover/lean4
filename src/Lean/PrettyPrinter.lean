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
namespace Meta end Meta -- HACK for old frontend
open Meta (MetaM) -- HACK for old frontend

def PPContext.runCoreM {α : Type} (ppCtx : PPContext) (x : CoreM α) : IO α :=
Prod.fst <$> x.toIO { options := ppCtx.opts } { env := ppCtx.env }

def PPContext.runMetaM {α : Type} (ppCtx : PPContext) (x : MetaM α) : IO α :=
ppCtx.runCoreM $ x.run' { lctx := ppCtx.lctx } { mctx := ppCtx.mctx }

namespace PrettyPrinter

def ppTerm (stx : Syntax) : CoreM Format := do
opts ← getOptions;
let stx := (sanitizeSyntax stx).run' { options := opts };
parenthesizeTerm stx >>= formatTerm

def ppExpr (currNamespace : Name) (openDecls : List OpenDecl) (e : Expr) : MetaM Format := do
lctx ← getLCtx;
opts ← getOptions;
let lctx := lctx.sanitizeNames.run' { options := opts };
Meta.withLCtx lctx #[] $ do
  stx ← delab currNamespace openDecls e;
  liftM $ ppTerm stx

@[export lean_pp_expr]
def ppExprLegacy (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : IO Format :=
Prod.fst <$> ((ppExpr Name.anonymous [] e).run' { lctx := lctx } { mctx := mctx }).toIO { options := opts } { env := env }

def ppCommand (stx : Syntax) : CoreM Format :=
parenthesizeCommand stx >>= formatCommand

def ppModule (stx : Syntax) : CoreM Format := do
parenthesize Lean.Parser.Module.module.parenthesizer stx >>= format Lean.Parser.Module.module.formatter

private partial def noContext : MessageData → MessageData
| MessageData.withContext ctx msg => noContext msg
| msg => msg

-- strip context (including environments with registered pretty printers) to prevent infinite recursion when pretty printing pretty printer error
private def withoutContext {m} [MonadExceptAdapter Exception Exception m m] (x : m Format) : m Format :=
adaptExcept (fun ex => match ex with
  | Exception.error ref msg => Exception.error ref (noContext msg)
  | e                       => e)
  x

@[builtinInit] def registerPPExt : IO Unit := do
ppFnsRef.set {
  ppExpr := fun ctx e   => ctx.runMetaM $ withoutContext $ ppExpr ctx.currNamespace ctx.openDecls e,
  ppTerm := fun ctx stx => ctx.runCoreM $ withoutContext $ ppTerm stx,
}

@[builtinInit] private def regTraceClasses : IO Unit := do
registerTraceClass `PrettyPrinter;
pure ()

end PrettyPrinter
end Lean
