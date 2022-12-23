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
  deriving TypeName

inductive MsgEmbed where
  /-- A piece of Lean code with elaboration/typing data.
  Note: does not necessarily correspond to an `Expr`, the name is for RPC API compatibility. -/
  | expr : CodeWithInfos → MsgEmbed
  /-- An interactive goal display. -/
  | goal : InteractiveGoal → MsgEmbed
  /-- Some messages (in particular, traces) are too costly to print eagerly. Instead, we allow
  the user to expand sub-traces interactively. -/
  | trace (indent : Nat) (cls : Name) (msg : TaggedText MsgEmbed) (collapsed : Bool)
      (children : StrictOrLazy (Array (TaggedText MsgEmbed)) (WithRpcRef LazyTraceChildren))
  deriving Inhabited, RpcEncodable

/-- The `message` field is the text of a message possibly containing interactive *embeds* of type
`MsgEmbed`. We maintain the invariant that embeds are stored in `.tag`s with empty `.text` subtrees,
i.e. `.tag embed (.text "")`, because a `MsgEmbed` display involve more than just text. -/
abbrev InteractiveDiagnostic := Lsp.DiagnosticWith (TaggedText MsgEmbed)

deriving instance RpcEncodable for Lsp.DiagnosticWith

namespace InteractiveDiagnostic
open MsgEmbed

def toDiagnostic (diag : InteractiveDiagnostic) : Lsp.Diagnostic :=
  { diag with message := prettyTt diag.message }
where
  prettyTt (tt : TaggedText MsgEmbed) : String :=
    let tt : TaggedText MsgEmbed := tt.rewrite fun
      | .expr tt,  _ => .text tt.stripTags
      | .goal g,   _ => .text (toString g.pretty)
      | .trace .., _ => .text "(trace)"
    tt.stripTags

end InteractiveDiagnostic

private def mkPPContext (nCtx : NamingContext) (ctx : MessageDataContext) : PPContext := {
  env := ctx.env, mctx := ctx.mctx, lctx := ctx.lctx, opts := ctx.opts,
  currNamespace := nCtx.currNamespace, openDecls := nCtx.openDecls
}

/-! The `msgToInteractive` algorithm turns a `MessageData` into `TaggedText MsgEmbed` in two stages.

First, in `msgToInteractiveAux` we produce a `Format` object whose `.tag` nodes refer to `EmbedFmt`
objects stored in an auxiliary array. Only the most shallow `.tag` in every branch through the
`Format` corresponds to an `EmbedFmt`. The kind of this tag determines how the nested `Format`
object (possibly including further `.tag`s), is processed. For example, if the output is
`.tag (.expr ctx infos) fmt` then tags in the nested `fmt` object refer to elements of `infos`.

In the second stage, we recursively transform such a `Format` into `TaggedText MsgEmbed` according
to the rule above by first pretty-printing it and then grabbing data referenced by the tags from
all the nested arrays (such as the `infos` array in the example above).

We cannot easily do the translation in a single `MessageData → TaggedText MsgEmbed` step because
that would effectively require reimplementing the (stateful, to keep track of indentation)
`Format.prettyM` algorithm.
-/

private inductive EmbedFmt
  /-- Nested tags denote `Info` objects in `infos`. -/
  | code (ctx : Elab.ContextInfo) (infos : RBMap Nat Elab.Info compare)
  /-- Nested text is ignored. -/
  | goal (ctx : Elab.ContextInfo) (lctx : LocalContext) (g : MVarId)
  /-- Nested text is ignored. -/
  | trace (cls : Name) (msg : Format) (collapsed : Bool)
    (children : StrictOrLazy (Array Format) (Array MessageData))
  /-- Nested tags are ignored, show nested text as-is. -/
  | ignoreTags
  deriving Inhabited

private abbrev MsgFmtM := StateT (Array EmbedFmt) IO

open MessageData in
private partial def msgToInteractiveAux (msgData : MessageData) : IO (Format × Array EmbedFmt) :=
  go { currNamespace := Name.anonymous, openDecls := [] } none msgData #[]
where
  pushEmbed (e : EmbedFmt) : MsgFmtM Nat :=
    modifyGet fun es => (es.size, es.push e)

  withIgnoreTags (fmt : Format) : MsgFmtM Format := do
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

  go (nCtx : NamingContext) : Option MessageDataContext → MessageData → MsgFmtM Format
  | _,         ofFormat fmt             => withIgnoreTags fmt
  | none,      ofPPFormat fmt           => (·.fmt) <$> fmt.pp none
  | some ctx,  ofPPFormat fmt           => do
    let ⟨fmt, infos⟩ ← fmt.pp (mkPPContext nCtx ctx)
    let t ← pushEmbed <| EmbedFmt.code (mkContextInfo nCtx ctx) infos
    return Format.tag t fmt
  | none,      ofGoal mvarId            => pure $ "goal " ++ format (mkMVar mvarId)
  | some ctx,  ofGoal mvarId            =>
    return .tag (← pushEmbed (.goal (mkContextInfo nCtx ctx) ctx.lctx mvarId)) "\n"
  | _,         withContext ctx d        => go nCtx ctx d
  | ctx,       withNamingContext nCtx d => go nCtx ctx d
  | ctx,       tagged _ d               => go nCtx ctx d
  | ctx,       nest n d                 => Format.nest n <$> go nCtx ctx d
  | ctx,       compose d₁ d₂            => do let d₁ ← go nCtx ctx d₁; let d₂ ← go nCtx ctx d₂; pure $ d₁ ++ d₂
  | ctx,       group d                  => Format.group <$> go nCtx ctx d
  | ctx,       .trace cls header children collapsed => do
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
    return .tag (← pushEmbed e) ".\n"

partial def msgToInteractive (msgData : MessageData) (hasWidgets : Bool) (indent : Nat := 0) : IO (TaggedText MsgEmbed) := do
  if !hasWidgets then
    return (TaggedText.prettyTagged (← msgData.format)).rewrite fun _ tt => .text tt.stripTags
  let (fmt, embeds) ← msgToInteractiveAux msgData
  let rec fmtToTT (fmt : Format) (indent : Nat) : IO (TaggedText MsgEmbed) :=
    (TaggedText.prettyTagged fmt indent).rewriteM fun (n, col) tt =>
      match embeds[n]! with
        | .code ctx infos =>
          return .tag (.expr (tagCodeInfos ctx infos tt)) default
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
  pure { range, fullRange? := some fullRange, severity?, source?, message, tags? }

end Lean.Widget
