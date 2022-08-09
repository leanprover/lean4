/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Linter.UnusedVariables
import Lean.Server.Utils
import Lean.Widget.InteractiveGoal

namespace Lean.Widget
open Lsp Server

inductive StrictOrLazy (α β : Type) : Type
  | strict : α → StrictOrLazy α β
  | lazy : β → StrictOrLazy α β
  deriving Inhabited, RpcEncodable

structure LazyTraceChildren where
  indent : Nat
  children : Array (WithRpcRef MessageData)
  deriving Std.TypeName

inductive MsgEmbed where
  | expr : CodeWithInfos → MsgEmbed
  | goal : InteractiveGoal → MsgEmbed
  | trace (indent : Nat) (cls : Name) (msg : TaggedText MsgEmbed) (collapsed : Bool)
      (children : StrictOrLazy (Array (TaggedText MsgEmbed)) (WithRpcRef LazyTraceChildren))
  deriving Inhabited, RpcEncodable

/-- We embed objects in LSP diagnostics by storing them in the tag of an empty subtree (`text ""`).
In other words, we terminate the `MsgEmbed`-tagged tree at embedded objects and instead store
the pretty-printed embed (which can itself be a `TaggedText`) in the tag. -/
abbrev InteractiveDiagnostic := Lsp.DiagnosticWith (TaggedText MsgEmbed)

deriving instance RpcEncodable for Lsp.DiagnosticWith

namespace InteractiveDiagnostic
open MsgEmbed

def toDiagnostic (diag : InteractiveDiagnostic) : Lsp.Diagnostic :=
  { diag with message := prettyTt diag.message }
where
  prettyTt (tt : TaggedText MsgEmbed) : String :=
    let tt : TaggedText MsgEmbed := tt.rewrite fun
      | .expr tt,           _ => .text tt.stripTags
      | .goal g,            _ => .text (toString g.pretty)
      | .trace ..,          _ => .text "(trace)"
    tt.stripTags

end InteractiveDiagnostic

private def mkPPContext (nCtx : NamingContext) (ctx : MessageDataContext) : PPContext := {
  env := ctx.env, mctx := ctx.mctx, lctx := ctx.lctx, opts := ctx.opts,
  currNamespace := nCtx.currNamespace, openDecls := nCtx.openDecls
}

private inductive EmbedFmt
  | /-- Tags denote `Info` objects. -/
    expr (ctx : Elab.ContextInfo) (infos : Std.RBMap Nat Elab.Info compare)
  | goal (ctx : Elab.ContextInfo) (lctx : LocalContext) (g : MVarId)
  | /-- Some messages (in particular, traces) are too costly to print eagerly. Instead, we allow
    the user to expand sub-traces interactively. -/
    trace (cls : Name) (msg : Format) (collapsed : Bool)
      (children : StrictOrLazy (Array Format) (Array MessageData))
  | /-- Ignore any tags in this subtree. -/ ignoreTags
  deriving Inhabited

private abbrev MsgFmtM := StateT (Array EmbedFmt) IO

open MessageData in
/-- We first build a `Nat`-tagged `Format` with the most shallow tag, if any,
in every branch indexing into the array of embedded objects. -/
private partial def msgToInteractiveAux (msgData : MessageData) : IO (Format × Array EmbedFmt) :=
  go { currNamespace := Name.anonymous, openDecls := [] } none msgData #[]
where
  pushEmbed (e : EmbedFmt) : MsgFmtM Nat :=
    modifyGet fun es => (es.size, es.push e)

  withIgnoreTags (x : MsgFmtM Format) : MsgFmtM Format := do
    let fmt ← x
    let t ← pushEmbed EmbedFmt.ignoreTags
    return Format.tag t fmt

  mkContextInfo (nCtx : NamingContext) (ctx : MessageDataContext) : Elab.ContextInfo := {
    env           := ctx.env
    mctx          := ctx.mctx
    fileMap       := default
    options       := ctx.opts
    currNamespace := nCtx.currNamespace
    openDecls     := nCtx.openDecls
    -- Hack: to make sure unique ids created at `ppExprWithInfos` do not collide with ones in `ctx.mctx`
    ngen          := { namePrefix := `_diag }
  }

  go : NamingContext → Option MessageDataContext → MessageData → MsgFmtM Format
  | _,    _,         ofFormat fmt             => withIgnoreTags (pure fmt)
  | _,    _,         ofLevel u                => return format u
  | _,    _,         ofName n                 => return format n
  | nCtx, some ctx,  ofSyntax s               => withIgnoreTags (ppTerm (mkPPContext nCtx ctx) ⟨s⟩) -- HACK: might not be a term
  | _,    none,      ofSyntax s               => withIgnoreTags (pure s.formatStx)
  | _,    none,      ofExpr e                 => return format (toString e)
  | nCtx, some ctx,  ofExpr e                 => do
    let ci := mkContextInfo nCtx ctx
    let (fmt, infos) ← ci.runMetaM ctx.lctx <| PrettyPrinter.ppExprWithInfos e
    let t ← pushEmbed <| EmbedFmt.expr ci infos
    return Format.tag t fmt
  | _,    none,      ofGoal mvarId            => pure $ "goal " ++ format (mkMVar mvarId)
  | nCtx, some ctx,  ofGoal mvarId            =>
    return .tag (← pushEmbed (.goal (mkContextInfo nCtx ctx) ctx.lctx mvarId)) "\n"
  | nCtx, _,         withContext ctx d        => go nCtx ctx d
  | _,    ctx,       withNamingContext nCtx d => go nCtx ctx d
  | nCtx, ctx,       tagged _ d               => go nCtx ctx d
  | nCtx, ctx,       nest n d                 => Format.nest n <$> go nCtx ctx d
  | nCtx, ctx,       compose d₁ d₂            => do let d₁ ← go nCtx ctx d₁; let d₂ ← go nCtx ctx d₂; pure $ d₁ ++ d₂
  | nCtx, ctx,       group d                  => Format.group <$> go nCtx ctx d
  | nCtx, ctx,       .trace cls header children collapsed => do
    let header := (← go nCtx ctx header).nest 4
    let nodes ←
      if collapsed && !children.isEmpty then
        let children := children.map fun child =>
          MessageData.withNamingContext nCtx <|
            match ctx with
            | some ctx => MessageData.withContext ctx child
            | none     => child
        pure (.lazy children)
      else
        pure (.strict (← children.mapM (go nCtx ctx)))
    let e := .trace cls header collapsed nodes
    pure (.tag (← pushEmbed e) ".\n")

partial def msgToInteractive (msgData : MessageData) (hasWidgets : Bool) (indent : Nat := 0) : IO (TaggedText MsgEmbed) := do
  if !hasWidgets then
    return (TaggedText.prettyTagged (← msgData.format)).rewrite fun _ tt => .text tt.stripTags
  let (fmt, embeds) ← msgToInteractiveAux msgData
  /- Here we rewrite a `TaggedText Nat` corresponding to a whole `MessageData` into one where
  the tags are `TaggedText MsgEmbed`s corresponding to embedded objects with their subtree
  empty (`text ""`). In other words, we terminate the `MsgEmbed`-tagged -tree at embedded objects
  and store the pretty-printed embed (which can itself be a `TaggedText`) in the tag. -/
  let rec fmtToTT (fmt : Format) (indent : Nat) : IO (TaggedText MsgEmbed) :=
    (TaggedText.prettyTagged fmt indent).rewriteM fun (n, col) tt =>
      match embeds[n]! with
        | .expr ctx infos =>
          return .tag (.expr (tagExprInfos ctx infos tt)) default
        | .goal ctx lctx g =>
          ctx.runMetaM lctx do
            return .tag (.goal (← goalToInteractive g)) default
        | .trace cls msg collapsed children => do
          let col := col + tt.stripTags.length - 2
          let children ←
            match children with
              | .lazy children => pure <| .lazy ⟨{indent := col+2, children := children.map .mk}⟩
              | .strict children => pure <| .strict (← children.mapM (fmtToTT · (col+2)))
          return .tag (.trace indent cls (← fmtToTT msg col) collapsed children) default
        | .ignoreTags => return .text tt.stripTags
  fmtToTT fmt indent

/-- Transform a Lean Message concerning the given text into an LSP Diagnostic. -/
def msgToInteractiveDiagnostic (text : FileMap) (m : Message) (hasWidgets : Bool) : IO InteractiveDiagnostic := do
  let low : Lsp.Position := text.leanPosToLspPos m.pos
  let fullHigh := text.leanPosToLspPos <| m.endPos.getD m.pos
  let high : Lsp.Position := match m.endPos with
    | some endPos =>
      /-
        Truncate messages that are more than one line long.
        This is a workaround to avoid big blocks of "red squiggly lines" on VS Code.
        TODO: should it be a parameter?
      -/
      let endPos := if endPos.line > m.pos.line then { line := m.pos.line + 1, column := 0 } else endPos
      text.leanPosToLspPos endPos
    | none        => low
  let range : Range := ⟨low, high⟩
  let fullRange : Range := ⟨low, fullHigh⟩
  let severity? := some <| match m.severity with
    | .information => .information
    | .warning     => .warning
    | .error       => .error
  let source? := some "Lean 4"
  let tags? :=
    if m.data.isDeprecationWarning then some #[.deprecated]
    else if m.data.isUnusedVariableWarning then some #[.unnecessary]
    else none
  let message ← try
      msgToInteractive m.data hasWidgets
    catch ex =>
      pure <| TaggedText.text s!"[error when printing message: {ex.toString}]"
  pure { range, fullRange, severity?, source?, message, tags? }

end Lean.Widget
