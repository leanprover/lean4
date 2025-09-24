/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
module

prelude
public import Lean.Server.Requests
import Lean.DocString.Syntax

public section

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
  `antiquotName]

def docKinds : Array SyntaxNodeKind := #[
  ``Lean.Parser.Command.plainDocComment,
  ``Lean.Parser.Command.docComment,
  ``Lean.Parser.Command.moduleDoc
]

-- TODO: make extensible, or don't
/-- Keywords for which a specific semantic token is provided. -/
def keywordSemanticTokenMap : Std.TreeMap String SemanticTokenType :=
  Std.TreeMap.empty
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

open Lean.Doc.Syntax in
def isVersoKind (k : SyntaxNodeKind) : Bool :=
  (`Lean.Doc.Syntax).isPrefixOf k


open Lean.Doc.Syntax in
private partial def collectVersoTokens
    (stx : Syntax) (getTokens : (stx : Syntax) → Array LeanSemanticToken) :
    Array LeanSemanticToken :=
  go stx |>.run #[] |>.2
where
  tok (tk : Syntax) (k : SemanticTokenType) : StateM (Array LeanSemanticToken) Unit :=
    modify (·.push ⟨tk, k⟩)

  go (stx : Syntax) : StateM (Array LeanSemanticToken) Unit := do
  match stx with
  | `(arg_val| $x:ident )
  | `(arg_val| $x:str )
  | `(arg_val| $x:num ) =>
    tok x .parameter
  | `(named| (%$tk1 $x:ident :=%$tk2 $v:arg_val )%$tk3) =>
    tok tk1 .keyword
    tok x .property
    tok tk2 .keyword
    go v
    tok tk3 .keyword
  | `(named_no_paren| $x:ident :=%$tk $v:arg_val ) =>
    tok x .property
    tok tk .keyword
    go v
  | `(flag_on| +%$tk$x)  | `(flag_off| -%$tk$x) =>
    tok tk .keyword
    tok x .property
  | `(link_target| [%$tk1 $s ]%$tk2) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
  | `(link_target| (%$tk1 $s )%$tk2) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
  | `(inline|$_:str) | `(inline|line! $_) => pure () -- No tokens for plain text or line breaks
  | `(inline| *[%$tk1 $inls* ]%$tk2) | `(inline|_[%$tk1 $inls* ]%$tk2) =>
    tok tk1 .keyword
    inls.forM go
    tok tk2 .keyword
  | `(inline| link[%$tk1 $inls* ]%$tk2 $ref) =>
    tok tk1 .keyword
    inls.forM go
    tok tk2 .keyword
    go ref
  | `(inline| image(%$tk1 $s )%$tk2 $ref) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
    go ref
  | `(inline| footnote(%$tk1 $s )%$tk2) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
  | `(inline| code(%$tk1 $s )%$tk2) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
  | `(inline| role{%$tk1 $x $args* }%$tk2 [%$tk3 $inls* ]%$tk4) =>
    tok tk1 .keyword
    tok x .function
    args.forM go
    tok tk2 .keyword
    tok tk3 .keyword
    inls.forM go
    tok tk4 .keyword
  | `(inline| \math%$tk1 code(%$tk2 $s )%$tk3)
  | `(inline| \displaymath%$tk1 code(%$tk2 $s )%$tk3) =>
    tok tk1 .keyword
    tok s .string
    tok tk2 .keyword
    tok tk3 .keyword
  | `(list_item| *%$tk $inls*) =>
    tok tk .keyword
    inls.forM go
  | `(desc| :%$tk $inls* => $blks*) =>
    tok tk .keyword
    inls.forM go
    blks.forM go
  | `(block|para[$inl*]) => inl.forM go
  | `(block| ```%$tk1 $x $args* | $s ```%$tk2)=>
    tok tk1 .keyword
    tok x .function
    args.forM go
    tok s .string
    tok tk2 .keyword
  | `(block| :::%$tk1 $x $args* { $blks* }%$tk2)=>
    tok tk1 .keyword
    tok x .function
    args.forM go
    blks.forM go
    tok tk2 .keyword
  | `(block| command{%$tk1 $x $args*}%$tk2)=>
    tok tk1 .keyword
    tok x .function
    args.forM go
    tok tk2 .keyword
  | `(block| %%%%$tk1 $vals* %%%%$tk2)=>
    tok tk1 .keyword
    modify (· ++ getTokens (mkNullNode vals))
    tok tk2 .keyword
  | `(block| [%$tk1 $s ]:%$tk2 $url) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
    tok url .string
  | `(block| [^%$tk1 $s ]:%$tk2 $inls*) =>
    tok tk1 .keyword
    tok s .property
    tok tk2 .keyword
    inls.forM go
  | `(block| header(%$tk $_ ){ $inls* })=>
    tok tk .keyword
    inls.forM go
  | `(block|ul{$items*}) | `(block|ol($_){$items*}) | `(block|dl{$items*}) =>
    items.forM go
  | _ =>
    pure ()

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
    if docKinds.contains stx.getKind then
      -- Docs are only highlighted in Verso format, in which case `stx[1]` is a node.
      if stx[1].isAtom then
        return #[]
      else
        return collectVersoTokens stx[1] collectSyntaxBasedSemanticTokens
    let mut tokens :=
      if stx.isOfKind choiceKind then
        collectSyntaxBasedSemanticTokens stx[0]
      else
        stx.getArgs.map collectSyntaxBasedSemanticTokens |>.flatten
    let Syntax.atom _ val := stx
      | return tokens
    let isRegularKeyword := val.length > 0 && isIdFirst val.front
    let isHashKeyword := val.length > 1 && val.front == '#' && isIdFirst (val.get ⟨1⟩)
    if ! isRegularKeyword && ! isHashKeyword then
      return tokens
    return tokens.push ⟨stx, keywordSemanticTokenMap.getD val .keyword⟩


open Lean.Doc.Syntax in
/-- Collects all semantic tokens from the given `Elab.InfoTree`. -/
def collectInfoBasedSemanticTokens (i : Elab.InfoTree) : Array LeanSemanticToken :=
  List.toArray <| i.deepestNodes fun _ info _ => do
    let .ofTermInfo ti := info
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

def computeSemanticTokens  (doc : EditableDocument) (beginPos : String.Pos)
    (endPos? : Option String.Pos) (snaps : List Snapshots.Snapshot) : RequestM SemanticTokens := do
  let mut leanSemanticTokens := #[]
  for s in snaps do
    if s.endPos <= beginPos then
      continue
    let syntaxBasedSemanticTokens := collectSyntaxBasedSemanticTokens s.stx
    let infoBasedSemanticTokens := collectInfoBasedSemanticTokens s.infoTree
    leanSemanticTokens := leanSemanticTokens ++ syntaxBasedSemanticTokens ++ infoBasedSemanticTokens
    RequestM.checkCancelled
  let absoluteLspSemanticTokens := computeAbsoluteLspSemanticTokens doc.meta.text beginPos endPos? leanSemanticTokens
  RequestM.checkCancelled
  let absoluteLspSemanticTokens := filterDuplicateSemanticTokens absoluteLspSemanticTokens
  RequestM.checkCancelled
  let semanticTokens := computeDeltaLspSemanticTokens absoluteLspSemanticTokens
  return semanticTokens

structure SemanticTokensState where
  deriving TypeName, Inhabited

/-- Computes all semantic tokens for the document. -/
def handleSemanticTokensFull (_ : SemanticTokensParams) (_ : SemanticTokensState)
    : RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let ctx ← read
  let doc ← readDoc
  -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
  -- for the full file before sending a response. This means that the response will be incomplete,
  -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
  -- `FileWorker` to tell the client to re-compute the semantic tokens.
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 3000 (cancelTks := ctx.cancelTk.cancellationTasks)
  let response ← computeSemanticTokens doc 0 none snaps
  return ({ response, isComplete }, ⟨⟩)

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
  let t := doc.cmdSnaps.waitUntil (·.endPos >= endPos)
  mapTaskCostly t fun (snaps, _) =>
    computeSemanticTokens doc beginPos endPos snaps

builtin_initialize
  registerLspRequestHandler
    "textDocument/semanticTokens/range"
    SemanticTokensRangeParams
    SemanticTokens
    handleSemanticTokensRange
  registerPartialStatefulLspRequestHandler
    "textDocument/semanticTokens/full"
    "workspace/semanticTokens/refresh"
    2000
    SemanticTokensParams
    SemanticTokens
    SemanticTokensState
    ⟨⟩
    handleSemanticTokensFull
    handleSemanticTokensDidChange

end Lean.Server.FileWorker
