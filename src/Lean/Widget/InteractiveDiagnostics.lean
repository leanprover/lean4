/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Lsp
import Lean.Message
import Lean.Server.Rpc.Basic
import Lean.Widget.TaggedText
import Lean.Widget.ExprWithCtx

namespace Lean.Widget
open Lsp Server

structure MsgEmbed where
  -- TODO(WN): other variants, e.g. `ofGoal`
  ef : ExprText
  deriving Inhabited, RpcEncoding

private def mkPPContext (nCtx : NamingContext) (ctx : MessageDataContext) : PPContext := {
  env := ctx.env, mctx := ctx.mctx, lctx := ctx.lctx, opts := ctx.opts,
  currNamespace := nCtx.currNamespace, openDecls := nCtx.openDecls
}

private inductive EmbedFmt
  | ofExpr (e : ExprWithCtx)
  deriving Inhabited

private abbrev MsgFmtM := StateT (Array EmbedFmt) IO

open MessageData in
/-- We first build a `Nat`-tagged `Format` with the most shallow tag, if any,
in every branch indexing into the array of embedded objects. -/
private partial def msgToInteractiveAux (msgData : MessageData) : IO (Format × Array EmbedFmt) :=
  go { currNamespace := Name.anonymous, openDecls := [] } none msgData #[]
where
  pushEmbedExpr (e : ExprWithCtx) : MsgFmtM Nat :=
    modifyGet fun es => (es.size, es.push (EmbedFmt.ofExpr e))

  go : NamingContext → Option MessageDataContext → MessageData → MsgFmtM Format
  | _,    _,         ofFormat fmt             => pure fmt
  | _,    _,         ofLevel u                => pure $ format u
  | _,    _,         ofName n                 => pure $ format n
  | nCtx, some ctx,  ofSyntax s               => ppTerm (mkPPContext nCtx ctx) s  -- HACK: might not be a term
  | _,    none,      ofSyntax s               => pure $ s.formatStx
  | _,    none,      ofExpr e                 => pure $ format (toString e)
  | nCtx, some ctx,  ofExpr e                 => do
    let f ← ppExpr (mkPPContext nCtx ctx) e
    let t ← pushEmbedExpr {
      expr := e
      env := ctx.env
      mctx := ctx.mctx
      lctx := ctx.lctx
      options := ctx.opts
      currNamespace := nCtx.currNamespace
      openDecls := nCtx.openDecls }
    return Format.tag t f
  | _,    none,      ofGoal mvarId            => pure $ "goal " ++ format (mkMVar mvarId)
  | nCtx, some ctx,  ofGoal mvarId            => ppGoal (mkPPContext nCtx ctx) mvarId
  | nCtx, _,         withContext ctx d        => go nCtx ctx d
  | _,    ctx,       withNamingContext nCtx d => go nCtx ctx d
  | nCtx, ctx,       tagged _ d               => go nCtx ctx d
  | nCtx, ctx,       nest n d                 => Format.nest n <$> go nCtx ctx d
  | nCtx, ctx,       compose d₁ d₂            => do let d₁ ← go nCtx ctx d₁; let d₂ ← go nCtx ctx d₂; pure $ d₁ ++ d₂
  | nCtx, ctx,       group d                  => Format.group <$> go nCtx ctx d
  | nCtx, ctx,       node ds                  => Format.nest 2 <$> ds.foldlM (fun r d => do let d ← go nCtx ctx d; pure $ r ++ Format.line ++ d) Format.nil

private def msgToInteractive (msgData : MessageData) : IO (TaggedText MsgEmbed) := do
  let (fmt, embeds) ← msgToInteractiveAux msgData
  let tt := TaggedText.prettyTagged fmt
  /- Here we rewrite a `TaggedText Nat` corresponding to a whole `MessageData` into one where
  the tags are `TaggedText MsgEmbed`s corresponding to embedded objects with their subtree being
  empty (`text ""`). In other words, we terminate the `MsgEmbed`-tree at embedded objects
  and store the pretty-printed embed (which is itself a `TaggedText (WithRpcRef LazyExprWithCtx)`,
  for example) in the tag. -/
  tt.rewriteM fun n subTt =>
    match embeds.get! n with
    | EmbedFmt.ofExpr e =>
      TaggedText.tag
        { ef := subTt.map fun n => ⟨fun () => e.runMetaM (e.traverse n)⟩ }
        (TaggedText.text "")

private partial def stripEmbeds (tt : TaggedText MsgEmbed) : String :=
  let tt : TaggedText MsgEmbed := tt.rewrite fun ⟨et⟩ _ => TaggedText.text et.stripTags
  tt.stripTags

/-- Transform a Lean Message concerning the given text into an LSP Diagnostic. -/
def msgToDiagnostic (text : FileMap) (m : Message) : ReaderT RpcSession IO Diagnostic := do
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
  let severity := match m.severity with
    | MessageSeverity.information => DiagnosticSeverity.information
    | MessageSeverity.warning     => DiagnosticSeverity.warning
    | MessageSeverity.error       => DiagnosticSeverity.error
  let source := "Lean 4 server"
  let tt ← msgToInteractive m.data
  let ttJson ← toJson <$> rpcEncode tt
  pure {
    range := range
    fullRange := fullRange
    severity? := severity
    source? := source
    message := stripEmbeds tt
    taggedMsg? := ttJson
  }

def publishMessages (m : DocumentMeta) (msgLog : MessageLog) (hOut : IO.FS.Stream) (rpcSesh : RpcSession) : IO Unit := do
  let diagnostics ← msgLog.msgs.mapM (msgToDiagnostic m.text · rpcSesh)
  let diagParams : PublishDiagnosticsParams :=
    { uri := m.uri
      version? := some m.version
      diagnostics := diagnostics.toArray }
  hOut.writeLspNotification {
    method := "textDocument/publishDiagnostics"
    param := toJson diagParams
  }

end Lean.Widget
