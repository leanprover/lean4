/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.PrettyPrinter.Delaborator
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter
import Lean.Parser.Module
import Lean.ParserCompiler

namespace Lean

def PPContext.runCoreM {α : Type} (ppCtx : PPContext) (x : CoreM α) : IO α :=
  Prod.fst <$> x.toIO { options := ppCtx.opts, currNamespace := ppCtx.currNamespace, openDecls := ppCtx.openDecls }
                      { env := ppCtx.env, ngen := { namePrefix := `_pp_uniq } }

def PPContext.runMetaM {α : Type} (ppCtx : PPContext) (x : MetaM α) : IO α :=
  ppCtx.runCoreM <| x.run' { lctx := ppCtx.lctx } { mctx := ppCtx.mctx }

namespace PrettyPrinter

def ppTerm (stx : Syntax) : CoreM Format := do
  let opts ← getOptions
  let stx := (sanitizeSyntax stx).run' { options := opts }
  parenthesizeTerm stx >>= formatTerm

def ppExpr (currNamespace : Name) (openDecls : List OpenDecl) (e : Expr) : MetaM Format := do
  let lctx ← getLCtx
  let opts ← getOptions
  let lctx := lctx.sanitizeNames.run' { options := opts }
  Meta.withLCtx lctx #[] do
    let stx ← delab currNamespace openDecls e
    ppTerm stx

@[export lean_pp_expr]
def ppExprLegacy (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : IO Format :=
  Prod.fst <$> ((ppExpr Name.anonymous [] e).run' { lctx := lctx } { mctx := mctx }).toIO { options := opts } { env := env }

def ppCommand (stx : Syntax) : CoreM Format :=
  parenthesizeCommand stx >>= formatCommand

def ppModule (stx : Syntax) : CoreM Format := do
  parenthesize Lean.Parser.Module.module.parenthesizer stx >>= format Lean.Parser.Module.module.formatter

private partial def noContext : MessageData → MessageData
  | MessageData.withContext ctx msg => noContext msg
  | MessageData.withNamingContext ctx msg => MessageData.withNamingContext ctx (noContext msg)
  | MessageData.nest n msg => MessageData.nest n (noContext msg)
  | MessageData.group msg  => MessageData.group (noContext msg)
  | MessageData.compose msg₁ msg₂ => MessageData.compose (noContext msg₁) (noContext msg₂)
  | MessageData.tagged tag msg => MessageData.tagged tag (noContext msg)
  | MessageData.node msgs => MessageData.node (msgs.map noContext)
  | msg => msg

-- strip context (including environments with registered pretty printers) to prevent infinite recursion when pretty printing pretty printer error
private def withoutContext {m} [MonadExcept Exception m] (x : m Format) : m Format :=
  tryCatch x fun
    | Exception.error ref msg => throw $ Exception.error ref (noContext msg)
    | ex                      => throw ex

builtin_initialize
  ppFnsRef.set {
    ppExpr := fun ctx e      => ctx.runMetaM $ withoutContext $ ppExpr ctx.currNamespace ctx.openDecls e,
    ppTerm := fun ctx stx    => ctx.runCoreM $ withoutContext $ ppTerm stx,
    ppGoal := fun ctx mvarId => ctx.runMetaM $ withoutContext $ Meta.ppGoal mvarId
  }

builtin_initialize
  registerTraceClass `PrettyPrinter

@[builtinInit]
unsafe def registerParserCompilers : IO Unit := do
  ParserCompiler.registerParserCompiler ⟨`parenthesizer, parenthesizerAttribute, combinatorParenthesizerAttribute⟩
  ParserCompiler.registerParserCompiler ⟨`formatter, formatterAttribute, combinatorFormatterAttribute⟩

end PrettyPrinter
end Lean
