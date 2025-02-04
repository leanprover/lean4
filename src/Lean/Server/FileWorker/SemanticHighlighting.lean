/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
prelude
import Lean.Server.Requests

namespace Lean.Server.FileWorker
open Lsp
open RequestM

/--
`SyntaxNodeKind`s for which the syntax node and its children receive no semantic highlighting.
-/
def noHighlightKinds : Array SyntaxNodeKind := #[
  -- usually have special highlighting by the client
  ``Lean.Parser.Term.sorry,
  ``Lean.Parser.Term.type,
  ``Lean.Parser.Term.prop,
  -- not really keywords
  `antiquotName,
  ``Lean.Parser.Command.docComment,
  ``Lean.Parser.Command.moduleDoc]

-- TODO: make extensible, or don't
/-- Keywords for which a specific semantic token is provided. -/
def keywordSemanticTokenMap : RBMap String SemanticTokenType compare :=
  RBMap.empty
    |>.insert "sorry" .leanSorryLike
    |>.insert "admit" .leanSorryLike
    |>.insert "stop" .leanSorryLike
    |>.insert "#exit" .leanSorryLike

/-- Semantic token information for a given `Syntax`. -/
structure LeanSemanticToken where
  /-- Syntax of the semantic token. -/
  stx  : Syntax
  /-- Type of the semantic token. -/
  type : SemanticTokenType

/-- Semantic token information with absolute LSP positions. -/
structure AbsoluteLspSemanticToken where
  /-- Start position of the semantic token. -/
  pos     : Lsp.Position
  /-- End position of the semantic token. -/
  tailPos : Lsp.Position
  /-- Start position of the semantic token. -/
  type    : SemanticTokenType
  deriving BEq, Hashable, FromJson, ToJson

/--
Given a set of `LeanSemanticToken`, computes the `AbsoluteLspSemanticToken` with absolute
LSP position information for each token.
-/
def computeAbsoluteLspSemanticTokens
    (text     : FileMap)
    (beginPos : String.Pos)
    (endPos?  : Option String.Pos)
    (tokens   : Array LeanSemanticToken)
    : Array AbsoluteLspSemanticToken :=
  tokens.filterMap fun ⟨stx, tokenType⟩ => do
    let (pos, tailPos) := (← stx.getPos?, ← stx.getTailPos?)
    guard <| beginPos <= pos && endPos?.all (pos < ·)
    let (lspPos, lspTailPos) := (text.utf8PosToLspPos pos, text.utf8PosToLspPos tailPos)
    return ⟨lspPos, lspTailPos, tokenType⟩

/-- Filters all duplicate semantic tokens with the same `pos`, `tailPos` and `type`. -/
def filterDuplicateSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : Array AbsoluteLspSemanticToken :=
  tokens.groupByKey id |>.toArray.map (·.1)

/--
Given a set of `AbsoluteLspSemanticToken`, computes the LSP `SemanticTokens` data with
token-relative positioning.
See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens.
-/
def computeDeltaLspSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : SemanticTokens := Id.run do
  let tokens := tokens.qsort fun ⟨pos1, tailPos1, _⟩ ⟨pos2, tailPos2, _⟩ =>
    pos1 < pos2 || pos1 == pos2 && tailPos1 <= tailPos2
  let mut data : Array Nat := Array.mkEmpty (5*tokens.size)
  let mut lastPos : Lsp.Position := ⟨0, 0⟩
  for ⟨pos, tailPos, tokenType⟩ in tokens do
    let deltaLine := pos.line - lastPos.line
    let deltaStart := pos.character - (if pos.line == lastPos.line then lastPos.character else 0)
    let length := tailPos.character - pos.character
    let tokenType := tokenType.toNat
    let tokenModifiers := 0
    data := data ++ #[deltaLine, deltaStart, length, tokenType, tokenModifiers]
    lastPos := pos
  return { data }

/--
Collects all semantic tokens that can be deduced purely from `Syntax`
without elaboration information.
-/
partial def collectSyntaxBasedSemanticTokens : (stx : Syntax) → Array LeanSemanticToken
  | `($e.$id:ident)    =>
    let tokens := collectSyntaxBasedSemanticTokens e
    tokens.push ⟨id, SemanticTokenType.property⟩
  | `($e |>.$field:ident) =>
    let tokens := collectSyntaxBasedSemanticTokens e
    tokens.push ⟨field, SemanticTokenType.property⟩
  | stx => Id.run do
    if noHighlightKinds.contains stx.getKind then
      return #[]
    let mut tokens :=
      if stx.isOfKind choiceKind then
        collectSyntaxBasedSemanticTokens stx[0]
      else
        stx.getArgs.map collectSyntaxBasedSemanticTokens |>.flatten
    let Syntax.atom _ val := stx
      | return tokens
    let isRegularKeyword := val.length > 0 && val.front.isAlpha
    let isHashKeyword := val.length > 1 && val.front == '#' && (val.get ⟨1⟩).isAlpha
    if ! isRegularKeyword && ! isHashKeyword then
      return tokens
    return tokens.push ⟨stx, keywordSemanticTokenMap.findD val .keyword⟩

/-- Collects all semantic tokens from the given `Elab.InfoTree`. -/
def collectInfoBasedSemanticTokens (i : Elab.InfoTree) : Array LeanSemanticToken :=
  List.toArray <| i.deepestNodes fun _ i _ => do
    let .ofTermInfo ti := i
      | none
    let .original .. := ti.stx.getHeadInfo
      | none
    if let `($_:ident) := ti.stx then
      if let Expr.fvar fvarId .. := ti.expr then
        if let some localDecl := ti.lctx.find? fvarId then
          -- Recall that `isAuxDecl` is an auxiliary declaration used to elaborate a recursive definition.
          if localDecl.isAuxDecl then
            if ti.isBinder then
              return ⟨ti.stx, SemanticTokenType.function⟩
          else if ! localDecl.isImplementationDetail then
            return ⟨ti.stx, SemanticTokenType.variable⟩
    if ti.stx.getKind == Parser.Term.identProjKind then
      return ⟨ti.stx, SemanticTokenType.property⟩
    none

/-- Computes the semantic tokens in the range [beginPos, endPos?). -/
def handleSemanticTokens (beginPos : String.Pos) (endPos? : Option String.Pos)
    : RequestM (RequestTask (LspResponse SemanticTokens)) := do
  let doc ← readDoc
  match endPos? with
  | none =>
    -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
    -- for the full file before sending a response. This means that the response will be incomplete,
    -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
    -- `FileWorker` to tell the client to re-compute the semantic tokens.
    let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 2000
    asTask <| do
      return { response := ← run doc snaps, isComplete }
  | some endPos =>
    let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
    mapTask t fun (snaps, _) => do
      return { response := ← run doc snaps, isComplete := true }
where
  run doc snaps : RequestM SemanticTokens := do
    let mut leanSemanticTokens := #[]
    for s in snaps do
      if s.endPos <= beginPos then
        continue
      let syntaxBasedSemanticTokens := collectSyntaxBasedSemanticTokens s.stx
      let infoBasedSemanticTokens := collectInfoBasedSemanticTokens s.infoTree
      leanSemanticTokens := leanSemanticTokens ++ syntaxBasedSemanticTokens ++ infoBasedSemanticTokens
    let absoluteLspSemanticTokens := computeAbsoluteLspSemanticTokens doc.meta.text beginPos endPos? leanSemanticTokens
    let absoluteLspSemanticTokens := filterDuplicateSemanticTokens absoluteLspSemanticTokens
    let semanticTokens := computeDeltaLspSemanticTokens absoluteLspSemanticTokens
    return semanticTokens

structure SemanticTokensState where
  deriving TypeName, Inhabited

/-- Computes all semantic tokens for the document. -/
def handleSemanticTokensFull (_ : SemanticTokensParams) (_ : SemanticTokensState)
    : RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let t ← handleSemanticTokens 0 none
  match t.get with
  | .error e => throw e
  | .ok r => return (r, ⟨⟩)

def handleSemanticTokensDidChange (_ : DidChangeTextDocumentParams)
    : StateT SemanticTokensState RequestM Unit := do
  return

/-- Computes the semantic tokens in the range provided by `p`. -/
def handleSemanticTokensRange (p : SemanticTokensRangeParams)
    : RequestM (RequestTask SemanticTokens) := do
  let doc ← readDoc
  let text := doc.meta.text
  let beginPos := text.lspPosToUtf8Pos p.range.start
  let endPos := text.lspPosToUtf8Pos p.range.end
  let t ← handleSemanticTokens beginPos endPos
  return t.map fun r => r.map (·.response)

builtin_initialize
  registerLspRequestHandler
    "textDocument/semanticTokens/range"
    SemanticTokensRangeParams
    SemanticTokens
    handleSemanticTokensRange
  registerPartialStatefulLspRequestHandler
    "textDocument/semanticTokens/full"
    "workspace/semanticTokens/refresh"
    SemanticTokensParams
    SemanticTokens
    SemanticTokensState
    ⟨⟩
    handleSemanticTokensFull
    handleSemanticTokensDidChange

end Lean.Server.FileWorker
