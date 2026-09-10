/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Marc Huisinga
-/
module

prelude
public import Lean.Server.Requests
import Lean.DocString.View

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
  /-- In case of overlap, higher-priority tokens will take precedence -/
  priority : Nat := 5

/-- Semantic token information with absolute LSP positions. -/
structure AbsoluteLspSemanticToken where
  /-- Start position of the semantic token. -/
  pos     : Lsp.Position
  /-- End position of the semantic token. -/
  tailPos : Lsp.Position
  /-- Start position of the semantic token. -/
  type    : SemanticTokenType
  /-- In case of overlap, higher-priority tokens will take precedence -/
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
    (tokens   : Array LeanSemanticToken) :
    Array AbsoluteLspSemanticToken :=
  tokens.filterMap fun tok => do
    let (pos, tailPos) := (← tok.stx.getPos?, ← tok.stx.getTailPos?)
    guard <| beginPos <= pos && endPos?.all (pos < ·)
    -- Every token should be non-empty
    guard <| pos < tailPos
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




open Lean.Doc in
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

  /--
  The region of a code block line to highlight. The line's final newline is omitted because some LSP
  clients (including VS Code) ignore a token that spans a line break.
  -/
  codeLine (line : Syntax) (value : String) : Option Syntax := do
    let ⟨pos, tailPos⟩ ← line.getRange?
    let tailPos := if value.endsWith "\n" then tailPos.prev text.source else tailPos
    return .ofRange ⟨pos, tailPos⟩

  goVal (val : TSyntax ``Parser.argVal) :
      StateM (Array LeanSemanticToken) Unit := do
    match ArgValView.of val with
    | some (.name x) => tok x.raw .parameter
    | some (.str s _) => tok s.raw .parameter
    | some (.num n _) => tok n.raw .parameter
    | none => pure ()

  goArg (arg : TSyntax ``Parser.arg) :
      StateM (Array LeanSemanticToken) Unit := do
    match ArgView.of arg with
    | some (.named _ (some (tk1, tk3)) x tk2 v) =>
      tok tk1 .keyword
      tok x.raw .property
      tok tk2 .keyword
      goVal v
      tok tk3 .keyword
    | some (.named _ none x tk v) =>
      tok x.raw .property
      tok tk .keyword
      goVal v
    | some (.flag _ tk x _) =>
      tok tk .keyword
      tok x.raw .property
    | some (.anon _ v) => goVal v
    | none => pure ()

  goTarget (tgt : LinkTargetView) : StateM (Array LeanSemanticToken) Unit := do
    match tgt with
    | .ref _ tk1 name tk2 =>
      tok tk1 .keyword
      tok name.raw .property
      tok tk2 .keyword
    | .url _ tk1 url tk2 =>
      tok tk1 .keyword
      tok url.raw .string
      tok tk2 .keyword

  goCode (code : CodeView) : StateM (Array LeanSemanticToken) Unit := do
    tok code.opener .keyword
    for line in code.content.getVersoCodeLines do
      if let some region := codeLine line.raw line.getVersoCodeLine then tok region .string
    tok code.closer .keyword

  goUnorderedItem (item : UnorderedListItemView) : StateM (Array LeanSemanticToken) Unit := do
    tok item.marker .keyword
    for b in item.contents do go b.raw

  goOrderedItem (item : OrderedListItemView) : StateM (Array LeanSemanticToken) Unit := do
    tok item.marker .keyword
    for b in item.contents do go b.raw

  goDesc (item : DescItemView) : StateM (Array LeanSemanticToken) Unit := do
    tok item.marker .keyword
    for i in item.term do go i.raw
    for b in item.desc do go b.raw

  go (stx : Syntax) : StateM (Array LeanSemanticToken) Unit := do
  if let some v := InlineView.of ⟨stx⟩ then
    match v with
    | .text .. | .linebreak .. => pure () -- No tokens for plain text or line breaks
    | .bold v =>
      tok v.opener .keyword
      for i in v.content do go i.raw
      tok v.closer .keyword
    | .emph v =>
      tok v.opener .keyword
      for i in v.content do go i.raw
      tok v.closer .keyword
    | .link v =>
      tok v.opener .keyword
      for i in v.content do go i.raw
      tok v.closer .keyword
      goTarget v.target
    | .image v =>
      tok v.opener .keyword
      tok v.alt.raw .string
      tok v.closer .keyword
      goTarget v.target
    | .footnote v =>
      tok v.opener .keyword
      tok v.name.raw .property
      tok v.closer .keyword
    | .code v =>
      goCode v
    | .role v =>
      tok v.braceOpen .keyword
      tok v.name.raw .function
      for a in v.args do goArg a
      tok v.braceClose .keyword
      if let some (o, _) := v.brackets then tok o .keyword
      for i in v.content do go i.raw
      if let some (_, c) := v.brackets then tok c .keyword
    | .math v =>
      tok v.marker .keyword
      goCode v.code
  else if let some v := BlockView.of ⟨stx⟩ then
    match v with
    | .para v =>
      for i in v.content do go i.raw
    | .codeblock v =>
      tok v.openFence .keyword
      if let some x := v.name? then
        tok x.raw .function
        for a in v.args do goArg a
      for line in v.content.getVersoCodeBlockLines do
        if let some region := codeLine line.raw line.getVersoCodeLine then tok region .string
      tok v.closeFence .keyword
    | .directive v =>
      tok v.opener .keyword
      tok v.name.raw .function
      for a in v.args do goArg a
      for b in v.content do go b.raw
      tok v.closer .keyword
    | .command v =>
      tok v.braceOpen .keyword
      tok v.name.raw .function
      for a in v.args do goArg a
      tok v.braceClose .keyword
    | .metadata v =>
      tok v.opener .keyword
      modify (· ++ getTokens v.contents.raw)
      tok v.closer .keyword
    | .linkRef v =>
      tok v.opener .keyword
      tok v.name.raw .property
      tok v.closer .keyword
      tok v.url.raw .string
    | .footnoteRef v =>
      tok v.opener .keyword
      tok v.name.raw .property
      tok v.closer .keyword
      for i in v.content do go i.raw
    | .header v =>
      tok v.marker .keyword
      for i in v.content do go i.raw
    | .ul v =>
      for item in v.items do goUnorderedItem item
    | .ol v =>
      for item in v.items do goOrderedItem item
    | .dl v =>
      for item in v.items do goDesc item
    | .blockquote v =>
      tok v.marker .keyword
      for b in v.content do go b.raw
  else
    stx.getArgs.forM go

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
    let isRegularKeyword := val.front?.any isIdFirst
    let isHashKeyword := ((val.dropPrefix? '#').bind (·.front?)).any isIdFirst
    if ! isRegularKeyword && ! isHashKeyword then
      return tokens
    return tokens.push { stx, type := keywordSemanticTokenMap.getD val .keyword }

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
def handleSemanticTokensFull (_ : SemanticTokensParams) (_ : SemanticTokensState) :
    RequestM (LspResponse SemanticTokens × SemanticTokensState) := do
  let ctx ← read
  let doc ← readDoc
  -- Only grabs the finished prefix so that we do not need to wait for elaboration to complete
  -- for the full file before sending a response. This means that the response will be incomplete,
  -- which we mitigate by regularly sending `workspace/semanticTokens/refresh` requests in the
  -- `FileWorker` to tell the client to re-compute the semantic tokens.
  let (snaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefixWithTimeout 3000 (cancelTks := ctx.cancelTk.cancellationTasks)
  let response ← computeSemanticTokens doc 0 none snaps
  return ({ response, isComplete }, ⟨⟩)

def handleSemanticTokensDidChange (_ : DidChangeTextDocumentParams) :
    StateT SemanticTokensState RequestM Unit := do
  return

/-- Computes the semantic tokens in the range provided by `p`. -/
def handleSemanticTokensRange (p : SemanticTokensRangeParams) :
    RequestM (RequestTask SemanticTokens) := do
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
