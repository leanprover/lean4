/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
module

prelude
public import Lean.Server.Requests

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
  /-- In case of overlap, higher-priority tokens will take precendence -/
  priority : Nat := 5

/-- Semantic token information with absolute LSP positions. -/
structure AbsoluteLspSemanticToken where
  /-- Start position of the semantic token. -/
  pos     : Lsp.Position
  /-- End position of the semantic token. -/
  tailPos : Lsp.Position
  /-- Start position of the semantic token. -/
  type    : SemanticTokenType
  /-- In case of overlap, higher-priority tokens will take precendence -/
  priority : Nat := 5
  deriving BEq, Hashable, FromJson, ToJson

/--
Given a set of `LeanSemanticToken`, computes the `AbsoluteLspSemanticToken` with absolute
LSP position information for each token.
-/
def computeAbsoluteLspSemanticTokens
    (text     : FileMap)
    (beginPos : String.Pos.Raw)
    (endPos?  : Option String.Pos.Raw)
    (tokens   : Array LeanSemanticToken)
    : Array AbsoluteLspSemanticToken :=
  tokens.filterMap fun tok => do
    let (pos, tailPos) := (← tok.stx.getPos?, ← tok.stx.getTailPos?)
    guard <| beginPos <= pos && endPos?.all (pos < ·)
    let (lspPos, lspTailPos) := (text.utf8PosToLspPos pos, text.utf8PosToLspPos tailPos)
    return { tok with pos := lspPos, tailPos := lspTailPos }

/--
The state used to handle computing non-overlapping semantic tokens. See
`handleOverlappingSemanticTokens` for a description of the problem.

Tokens are computed by iterating over every token _boundary_. At a given boundary, one of the
following things may happen:
1. We leave the range of a token, and there is no current token
2. We leave the range of a token, starting a new one
3. We start a token when there was none before

To do this, we maintain a set of tokens that could in principle occupy the interval from the last
token boundary to the one being considered. This includes tokens that are already in progress, and
potentially a new one from the input. The one with the highest priority is selected to be the next
one at each transition.
-/
private structure HandleOverlapState where
  /-- The non-overlapping tokens that have been definitively produced -/
  nonOverlapping : Array AbsoluteLspSemanticToken
  /--
  The current interval's token, with its start position suitably adjusted. The current interval's
  token always has a priority that's at least as high as all tokens in `surrounding` (they may be
  equal if overlapping tokens had the same priority, and a tiebreaker such as length was used).

  When a token is replaced by a higher-priority token in part of its interval, its start position is
  set to the end position of the overriding token when it is resumed.
  -/
  current? : Option AbsoluteLspSemanticToken
  /--
  The other tokens whose intervals include the current token's start position.

  Sorted by end position (increasing), because we've already passed their start positions. Only
  their end positions may contribute new token boundaries.
  -/
  surrounding : List AbsoluteLspSemanticToken
deriving Inhabited

/--
Adds a surrounding token to the set. These are tokens whose interval includes the boundaries being
processed, but are superseded by the current token.
-/
private def HandleOverlapState.insertSurrounding
    (st : HandleOverlapState) (s : AbsoluteLspSemanticToken) : HandleOverlapState :=
  { st with surrounding := go st.surrounding }
where
  go
    | [] => [s]
    | x :: xs =>
      if s.tailPos < x.tailPos then s :: x :: xs else x :: go xs

/--
Handles state transitions that are not due to a new token. If `nextToken?` is `none`, then there are
no more tokens to process, so all remaining transitions occur. If it is `some t`, then state
transitions only occur for token boundaries less than the `t`'s start.
-/
private def HandleOverlapState.untilToken (st : HandleOverlapState) (nextToken? : Option AbsoluteLspSemanticToken) : HandleOverlapState := Id.run do
  let mut st := st
  repeat
    if let some curr := st.current? then
      -- We know that the current token is higher priority (modulo tiebreaking criteria) than
      -- surrounding tokens, so we should discard any surrounding tokens that end before it does.
      -- This ensures that the surrounding tokens always end strictly later than the current token.
      st := { st with surrounding := st.surrounding.dropWhile (·.tailPos ≤ curr.tailPos) }
      -- If the current token ends before the next token starts, or if there are no new tokens, then
      -- we end it now
      let endNow : Bool :=
        if let some t := nextToken? then curr.tailPos ≤ t.pos else true
      if endNow then
        st := { st with
          nonOverlapping := st.nonOverlapping.push curr,
          -- Because all surrounding tokens end later than the current token, the new current token
          -- is non-empty.
          current? := takeBest st.surrounding |>.map ({ · with pos := curr.tailPos })
        }
      -- If the current token extends past the start of the next token,
      -- then all remaining surrounding tokens also extend past the start of the next token,
      -- which are all lower priority than the current token.
      -- Hence, we are ready to handle the next token.
      else
        break
    else
      -- Check whether the surrounding tokens need to become current.
      -- Make the highest-priority surrounding token into the new current one.
      if let some best := takeBest st.surrounding then
        -- No need to remove it from surrounding because this will happen at its end position
        st := { st with current? := best }
      else
        -- Nothing is current, and nothing is surrounding. We're done.
        break
  st
where
  /--
  The best token is the nonempty token with the highest priority; given equal priorities, earlier
  tokens win. Breaking ties in favor of shorter tokens means that more information has the chance to
  be displayed.
  -/
  takeBest (toks : List AbsoluteLspSemanticToken) : Option AbsoluteLspSemanticToken :=
    toks.foldl (init := none) fun
      | none, t =>
        some t
      | some soFar, t =>
        if better t soFar then
          some t
        else
          some soFar

  better (t soFar : AbsoluteLspSemanticToken) : Bool :=
    (t.priority > soFar.priority || (t.priority == soFar.priority && t.tailPos < soFar.tailPos))

/--
Handles a new token. First, `untilToken` is called, which takes care of all transitions that are due
to token boundaries prior to the start of `t`. After that `t`'s priority is compared to the current
token (if any), and then the highest-priority of the two is made current with the other relegated to
the surrounding tokens list. If `t` and the current token have the same priority, then the one that
starts later or ends earlier is made into the new current token.
-/
private def HandleOverlapState.token (st : HandleOverlapState) (t : AbsoluteLspSemanticToken) : HandleOverlapState := Id.run do
  let st := st.untilToken (some t)
  -- Now we know that the current token, if present, overlaps with `t`
  let some curr := st.current?
    | -- If there was no current token, then there's no surrounding tokens either
      return { st with current? := some t }
  if curr.priority > t.priority then
    -- Insert t into surrounding, continue with current
    return st.insertSurrounding t
  -- Tied priorities: make the token that starts later or ends earlier current.
  if curr.priority == t.priority then
    if curr.pos == t.pos then -- if `t` starts later, transition to it. Same start, keep the one that ends first.
      if curr.tailPos < t.tailPos then
        return st.insertSurrounding t

  -- Transition to t, save current if it's longer than t
  let st := { st with
    current? := some t,
    nonOverlapping :=
      let curr := { curr with tailPos := t.pos }
      -- Only save the token if it actually takes up space. This step is what filters out
      -- actual duplicates.
      if curr.pos < curr.tailPos then
        st.nonOverlapping.push curr
      else
        st.nonOverlapping
  }
  if curr.tailPos > t.tailPos then
    return st.insertSurrounding curr
  else
    return st



/--
Eliminates overlapping tokens by selecting a single “best” token for each interval between token
boundaries.

While LSP allows clients to state they they can handle overlapping tokens, widely used clients such
as VS Code cannot handle them. Thus, we need to make them non-overlapping (this strictly generalizes
removal of duplicates).

Given tokens A, B, C, D as in:
```
|-----A------|  |----D----|
    |------B----------|
        |----C----|
```
with priorities C > B, B > A, B > D, we want to emit the tokens:
```
|-A-|-B-|----C----|-B-|-D--|
```
In other words, `B` is split into two regions: before and after `C`.

If two overlapping tokens have the same priority, then ties are broken as follows:
 * If the tokens start at the same position, then the shorter one is used.
 * If they have the same start position and are the same length, then the one that occurs later in
   the original input array is used.
 * If a new token starts in the middle of an existing one, and they have the same priority, then the
   new token is used.

Callers should ensure that all tokens in `tokens` designate non-empty regions of the file. In other
words, it should be true that `∀ t ∈ tokens, t.pos < t.tailPos`.
-/
def handleOverlappingSemanticTokens (tokens : Array AbsoluteLspSemanticToken) :
    Array AbsoluteLspSemanticToken := Id.run do
  -- `insertionSort` is used because a stable sort is needed here in order to allow the final
  -- tiebreaker to be position in the input array
  let count := tokens.size
  let tokens := tokens.toList.mergeSort fun ⟨pos1, tailPos1, _, _⟩ ⟨pos2, tailPos2, _, _⟩ =>
    pos1 < pos2 || pos1 == pos2 && tailPos1 ≤ tailPos2
  let mut st : HandleOverlapState := {
    current? := none
    -- Reserve 10% for overlaps
    nonOverlapping := Array.mkEmpty ((count * 11) / 10)
    surrounding := []
  }
  for t in tokens do
    st := st.token t
  st := st.untilToken none
  return st.nonOverlapping


/--
Given a set of `AbsoluteLspSemanticToken`, computes the LSP `SemanticTokens` data with
token-relative positioning.
See https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_semanticTokens.
-/
def computeDeltaLspSemanticTokens (tokens : Array AbsoluteLspSemanticToken) : SemanticTokens := Id.run do
  let tokens := tokens.qsort fun ⟨pos1, tailPos1, _, _⟩ ⟨pos2, tailPos2, _, _⟩ =>
    pos1 < pos2 || pos1 == pos2 && tailPos1 <= tailPos2
  let mut data : Array Nat := Array.mkEmpty (5*tokens.size)
  let mut lastPos : Lsp.Position := ⟨0, 0⟩
  for ⟨pos, tailPos, tokenType, _⟩ in tokens do
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

/--
Split the token at newline boundaries to support LSP clients such as VS Code that can't deal with
newline-spanning tokens.
-/
private def splitStr (text : FileMap) (stx : Syntax) : Array Syntax := Id.run do
  let some ⟨pos, tailPos⟩ := stx.getRange?
    | return #[]
  -- Construct fake syntax with the right source spans
  let mut pos := pos
  let mut stxs := #[]
  -- Gets the line number of the syntax's position, to avoid iterating over lines that don't include
  -- the region of interest. As an index into `text.positions`, this line number is the index of
  -- the position of the _next_ line's start.
  let startLine := text.toPosition pos |>.line
  for h : i in [startLine:text.positions.size] do
    let l := text.positions[i]
    if l > tailPos then
      stxs := stxs.push <| Syntax.ofRange ⟨pos, tailPos⟩
      break
    -- Here, `l` is the position of the first character of the next line. This means that
    -- terminating the token at `l` includes the newline. If the semantic token includes the
    -- newline, then VS Code ignores it (it doesn't support multi-line tokens), so the token
    -- should be terminated one character earlier.
    let l' := l.prev text.source
    stxs := stxs.push <| .ofRange ⟨pos, l'⟩
    pos := l
  return stxs



open Lean.Doc.Syntax in
private partial def collectVersoTokens
    (text : FileMap)
    (stx : Syntax) (getTokens : (stx : Syntax) → Array LeanSemanticToken) :
    Array LeanSemanticToken :=
  go stx |>.run #[] |>.2
where
  tok (tk : Syntax) (k : SemanticTokenType) : StateM (Array LeanSemanticToken) Unit :=
    let priority :=
      match k with
      -- String tokens occur as the default highlighting of code element contents. They should be
      -- overridden by anything more specific, like variable names, that occurs in these elements,
      -- so they get a lower priority.
      | .string => 3
      | _ => 5
    modify (·.push { stx := tk, type := k, priority })

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
    tok s .property
    tok tk2 .keyword
  | `(link_target| (%$tk1 $s )%$tk2) =>
    tok tk1 .keyword
    tok s .string
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
    for line in splitStr text s do tok line .string
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
  | other =>
    let k := other.getKind
    if k == nullKind || k == ``Lean.Parser.Command.versoCommentBody then
      other.getArgs.forM go

/--
Collects all semantic tokens that can be deduced purely from `Syntax`
without elaboration information.
-/
partial def collectSyntaxBasedSemanticTokens (text : FileMap) : (stx : Syntax) → Array LeanSemanticToken
  | `($e.$id:ident)    =>
    let tokens := collectSyntaxBasedSemanticTokens text e
    tokens.push { stx := id, type := SemanticTokenType.property }
  | `($e |>.$field:ident) =>
    let tokens := collectSyntaxBasedSemanticTokens text e
    tokens.push { stx := field, type := SemanticTokenType.property }
  | stx => Id.run do
    if noHighlightKinds.contains stx.getKind then
      return #[]
    if docKinds.contains stx.getKind then
      -- Docs are only highlighted in Verso format, in which case `stx[1]` is a node.
      if stx[1].isAtom then
        return #[]
      else
        return collectVersoTokens text stx[1] (collectSyntaxBasedSemanticTokens text)
    let mut tokens :=
      if stx.isOfKind choiceKind then
        collectSyntaxBasedSemanticTokens text stx[0]
      else
        stx.getArgs.map (collectSyntaxBasedSemanticTokens text) |>.flatten
    let Syntax.atom _ val := stx
      | return tokens
    let isRegularKeyword := !val.isEmpty && isIdFirst val.front
    let isHashKeyword := isHashKeyword val
    if ! isRegularKeyword && ! isHashKeyword then
      return tokens
    return tokens.push { stx, type := keywordSemanticTokenMap.getD val .keyword }
where
  isHashKeyword (val : String) : Bool :=
    match (val.chars.take 2).toList with
    | ['#', c] => isIdFirst c
    | _ => false

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
              return { stx := ti.stx, type := SemanticTokenType.function }
          else if ! localDecl.isImplementationDetail then
            return { stx := ti.stx, type := SemanticTokenType.variable }
    if ti.stx.getKind == Parser.Term.identProjKind then
      return {stx := ti.stx, type := SemanticTokenType.property }
    none

/--
A debugging utility for inspecting sets of collected tokens, classified by line and sorted by
column.
-/
def dbgShowTokens (text : FileMap) (toks : Array LeanSemanticToken) : String := Id.run do
  let mut byLine : Std.HashMap Nat (Array (Nat × Nat × LeanSemanticToken)) := {}
  for ⟨stx, tok, prio⟩ in toks do
    if let some ⟨⟨l, c1⟩, ⟨_, c2⟩⟩ := text.lspRangeOfStx? stx then
      byLine := byLine.alter l fun x? => some (x?.getD #[] |>.push (c1, c2, ⟨stx, tok, prio⟩))
  let mut out := ""
  for (l, vals) in byLine.toList.mergeSort (fun x y => x.1 ≤ y.1) do
    let vals := vals.toList.mergeSort fun x y => x.1 ≤ y.1
    out := out ++ s!"{l}:\t{vals.map (fun (c1, c2, ⟨stx, tok, prio⟩) => (c1, c2, stx, toJson tok, prio))}\n"
  out

def computeSemanticTokens  (doc : EditableDocument) (beginPos : String.Pos.Raw)
    (endPos? : Option String.Pos.Raw) (snaps : List Snapshots.Snapshot) : RequestM SemanticTokens := do
  let mut leanSemanticTokens := #[]
  for s in snaps do
    if s.endPos <= beginPos then
      continue
    let syntaxBasedSemanticTokens := collectSyntaxBasedSemanticTokens doc.meta.text s.stx
    let infoBasedSemanticTokens := collectInfoBasedSemanticTokens s.infoTree
    leanSemanticTokens := leanSemanticTokens ++ syntaxBasedSemanticTokens ++ infoBasedSemanticTokens
    RequestM.checkCancelled
  let absoluteLspSemanticTokens := computeAbsoluteLspSemanticTokens doc.meta.text beginPos endPos? leanSemanticTokens
  RequestM.checkCancelled
  let absoluteLspSemanticTokens := handleOverlappingSemanticTokens absoluteLspSemanticTokens
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
