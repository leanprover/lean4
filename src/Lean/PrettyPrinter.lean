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
  Prod.fst <$> x.toIO { options := ppCtx.opts, currNamespace := ppCtx.currNamespace, openDecls := ppCtx.openDecls, fileName := "<PrettyPrinter>", fileMap := default }
                      { env := ppCtx.env, ngen := { namePrefix := `_pp_uniq } }

def PPContext.runMetaM {α : Type} (ppCtx : PPContext) (x : MetaM α) : IO α :=
  ppCtx.runCoreM <| x.run' { lctx := ppCtx.lctx } { mctx := ppCtx.mctx }

namespace PrettyPrinter

def ppCategory (cat : Name) (stx : Syntax) : CoreM Format := do
  let opts ← getOptions
  let stx := (sanitizeSyntax stx).run' { options := opts }
  parenthesizeCategory cat stx >>= formatCategory cat

def ppTerm (stx : Term) : CoreM Format := ppCategory `term stx

def ppUsing (e : Expr) (delab : Expr → MetaM Term) : MetaM Format := do
  let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx lctx #[] do
    ppTerm (← delab e)

def ppExpr (e : Expr) : MetaM Format := do
  ppUsing e delab

/-- Return a `fmt` representing pretty-printed `e` together with a map from tags in `fmt`
to `Elab.Info` nodes produced by the delaborator at various subexpressions of `e`. -/
def ppExprWithInfos (e : Expr) (optsPerPos : Delaborator.OptionsPerPos := {}) (delab := Delaborator.delab)
    : MetaM (Format × RBMap Nat Elab.Info compare) := do
  let lctx := (← getLCtx).sanitizeNames.run' { options := (← getOptions) }
  Meta.withLCtx lctx #[] do
    let (stx, infos) ← delabCore e optsPerPos delab
    let fmt ← ppTerm stx
    return (fmt, infos)

def ppConst (e : Expr) : MetaM Format := do
  ppUsing e fun e => return (← delabCore e (delab := Delaborator.delabConst)).1

@[export lean_pp_expr]
def ppExprLegacy (env : Environment) (mctx : MetavarContext) (lctx : LocalContext) (opts : Options) (e : Expr) : IO Format :=
  Prod.fst <$> ((ppExpr e).run' { lctx := lctx } { mctx := mctx }).toIO { options := opts, fileName := "<PrettyPrinter>", fileMap := default } { env := env }

def ppTactic (stx : TSyntax `tactic) : CoreM Format := ppCategory `tactic stx

def ppCommand (stx : Syntax.Command) : CoreM Format := ppCategory `command stx

def ppModule (stx : TSyntax ``Parser.Module.module) : CoreM Format := do
  parenthesize Lean.Parser.Module.module.parenthesizer stx >>= format Lean.Parser.Module.module.formatter

private partial def noContext : MessageData → MessageData
  | MessageData.withContext _   msg => noContext msg
  | MessageData.withNamingContext ctx msg => MessageData.withNamingContext ctx (noContext msg)
  | MessageData.nest n msg => MessageData.nest n (noContext msg)
  | MessageData.group msg  => MessageData.group (noContext msg)
  | MessageData.compose msg₁ msg₂ => MessageData.compose (noContext msg₁) (noContext msg₂)
  | MessageData.tagged tag msg => MessageData.tagged tag (noContext msg)
  | MessageData.trace cls header children collapsed =>
    MessageData.trace cls (noContext header) (children.map noContext) collapsed
  | msg => msg

-- strip context (including environments with registered pretty printers) to prevent infinite recursion when pretty printing pretty printer error
private def withoutContext {m} [MonadExcept Exception m] (x : m Format) : m Format :=
  tryCatch x fun
    | Exception.error ref msg => throw <| Exception.error ref (noContext msg)
    | ex                      => throw ex

builtin_initialize
  ppFnsRef.set {
    ppExpr := fun ctx e      => ctx.runMetaM <| withoutContext <| ppExpr e,
    ppTerm := fun ctx stx    => ctx.runCoreM <| withoutContext <| ppTerm stx,
    ppGoal := fun ctx mvarId => ctx.runMetaM <| withoutContext <| Meta.ppGoal mvarId
  }

builtin_initialize
  registerTraceClass `PrettyPrinter

@[builtin_init]
unsafe def registerParserCompilers : IO Unit := do
  ParserCompiler.registerParserCompiler ⟨`parenthesizer, parenthesizerAttribute, combinatorParenthesizerAttribute⟩
  ParserCompiler.registerParserCompiler ⟨`formatter, formatterAttribute, combinatorFormatterAttribute⟩

end PrettyPrinter
end Lean
