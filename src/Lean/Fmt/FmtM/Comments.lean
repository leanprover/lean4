/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Syntax
public import Lean.Fmt.FmtM.Error
public import Lean.Fmt.Util.Basic
import Lean.Fmt.Util.RangeTree
import Init.Data.String.Search
import Init.Control.Basic
import Std.Data.HashMap.AdditionalOperations
public import Lean.Fmt.FmtM.LineInfo
public import Lean.Environment
public import Lean.Data.Options
public import Lean.Fmt.FmtM.Primitives

/-- Indents all lines in `s` by `numSpaces` spaces. -/
def String.indent (s : String) (numSpaces : Nat) (skipFirstLine : Bool := false) : String :=
  s.split "\n"
    |>.toArray
    |>.mapIdx (fun i line =>
      if skipFirstLine && i == 0 then line.toString else "".pushn ' ' numSpaces ++ line.toString)
    |>.toList
    |> "\n".intercalate

namespace Lean.Fmt

/-- Symbol that the comment starts with. -/
def Comment.Kind.startSymbol (kind : Comment.Kind) : String :=
  match kind with
  | .lineComment => "--"
  | .blockComment => "/-"

/-- Symbol that the comment is terminated with. -/
def Comment.Kind.endSymbol (kind : Comment.Kind) : String :=
  match kind with
  | .lineComment => "\n"
  | .blockComment => "-/"

/-- Whether this kind of comment can be nested, e.g. `/-/-foo-/-/`. -/
def Comment.Kind.hasNesting (kind : Comment.Kind) : Bool :=
  match kind with
  | .lineComment => false
  | .blockComment => true

/-- Prefix that lines after the first line of the comment are prefixed with. -/
def Comment.Kind.linePrefix? (kind : Comment.Kind) : Option String :=
  match kind with
  | .lineComment => some "--"
  | .blockComment => none

public structure Comment.Rendering where
  rendered : String
  isMultiLine : Bool
deriving Inhabited

/--
Renders this comment to a set of string alternatives, sorted descendingly by priority.
If a specific rendering does not fit into the line it is placed at, a lower priority rendering is
preferred.
-/
public def Comment.render (c : Comment) : Array Rendering :=
  match c.kind with
  | .lineComment =>
    let lines :=
      c.content.map fun content =>
        if content.chars.all (· == '-') then
          s!"--{content}"
        else
          s!"-- {content}"
    #[⟨lines.toList |> "\n".intercalate, lines.size > 1⟩]
  | .blockComment =>
    let singleLineRendering :=
      if c.content[0]!.chars.all (· == '-') then
        s!"/-{c.content[0]!}-/"
      else
        s!"/- {c.content[0]!} -/"
    let multiLineRendering :=
      s!"/-\
        \n{"\n".intercalate c.content.toList}\
        \n-/"
    if c.content.size == 1 then
      #[⟨singleLineRendering, false⟩, ⟨multiLineRendering, true⟩]
    else
      #[⟨multiLineRendering, true⟩]

/-- Where this comment should be placed in the rendered document. -/
public inductive Comment.RenderedPlacementKind where
  /-- Placed on a separate line before the token that this comment is attached to. -/
  | afterClosestPreviousNewline
  /-- Placed on the end of the same line as the token that this comment is attached to. -/
  | beforeClosestNextNewline
  /-- Placed after the token that this comment is attached to. -/
  | afterToken

structure Comment.RenderedPlacement where
  kind : RenderedPlacementKind
  rendering : Rendering

/--
Yields a set of alternative placements of this comment in a rendered output, sorted descendingly
by priority.
If a specific placement cannot be placed into the line it is placed at, a lower priority placement
is preferred.
Ensures that the lowest priority placement can always be placed into a line.
-/
def Comment.renderedPlacements (c : Comment) : Array RenderedPlacement :=
  c.render.flatMap fun rendering =>
    let kinds : Array RenderedPlacementKind :=
      match c.kind, c.placement with
      | .lineComment, .afterToken =>
        #[.beforeClosestNextNewline, .afterClosestPreviousNewline]
      | .lineComment, .onLineBeforeToken =>
        #[.afterClosestPreviousNewline]
      | .blockComment, .afterToken =>
        if rendering.isMultiLine then
          #[.afterClosestPreviousNewline]
        else
          #[.beforeClosestNextNewline, .afterClosestPreviousNewline]
      | .blockComment, .onLineBeforeToken =>
        #[.afterClosestPreviousNewline]
    kinds.map (⟨·, rendering⟩)

section Extraction

structure PendingComment extends Comment where
  raw : String
  startColumnOffset : Nat
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
deriving Inhabited, Repr

public def normalizeCommentContent
    (s : String) (startSymbol endSymbol : String) (startColumnOffset : Nat) (isLineComment : Bool)
    : Array String :=
  let s := s.toSlice.dropPrefix startSymbol |>.dropSuffix endSymbol
  let lines := s.split "\n" |>.toArray
  let indentation := contentColumnOffset lines
  let deindentedLines :=
    lines[0]! :: (lines[1:].toList.map (dropIndentation · indentation) |>.map dropLinePrefix)
  let deindentedLines := deindentedLines.map (·.toString)
  let content := "\n".intercalate deindentedLines |>.toSlice |> normalizeContent |>.toString
  content.split "\n" |>.toArray.map (·.toString)
where
  contentColumnOffset (lines : Array String.Slice) : Nat := Id.run do
    let mut offset? : Option Nat := none
    for (line, i) in lines.zipIdx do
      let indentation := line.takeWhile (· == ' ') |>.chars.length
      if indentation == line.chars.length then
        continue
      let lineColumnOffset := if i == 0 then startColumnOffset + startSymbol.chars.length else 0
      let columnOffset := lineColumnOffset + indentation
      offset? :=
        some <| match offset? with
          | none => columnOffset
          | some offset => min offset columnOffset
    return offset?.getD startColumnOffset
  normalizeContent (s : String.Slice) : String.Slice := Id.run do
    if isLineComment then
      s.dropPrefix " " |>.dropSuffix "\n"
    else
      s.dropWhile (fun c => c = ' ' || c = '\n') |>.dropEndWhile (fun c => c = ' ' || c = '\n')
  dropIndentation (line : String.Slice) (amount : Nat) : String.Slice := Id.run do
    let mut line := line
    let mut amount := amount
    while !line.isEmpty && amount > 0 do
      let c := line.front
      if c != ' ' then
        break
      line := line.drop 1
      amount := amount - 1
    return line
  dropLinePrefix (line : String.Slice) : String.Slice := Id.run do
    if !isLineComment then
      return line
    let some line := line.dropPrefix? startSymbol
      | return line
    return line.dropPrefix " "

/--
Finalizes a pending comment, extracting `Comment.content` from `PendingComment.raw` by
removing start, end and line separators, erasing all indentation relative to the least indented
line with content in the comment and dropping stylistic whitespace at the start and the end of the
comment (e.g. the separation space in `-- ` or the newlines in a multi-line `/-\n...\n-/`).
-/
def PendingComment.finalize (p : PendingComment) : Comment :=
  let content :=
    normalizeCommentContent p.raw p.kind.startSymbol p.kind.endSymbol p.startColumnOffset <|
      p.kind matches .lineComment
  {
    kind := p.kind
    placement := p.placement
    originalTokenRange := p.originalTokenRange
    originalWhitespaceRange := ⟨p.startPos, p.endPos⟩
    originalWhitespaceKind := p.originalWhitespaceKind
    content
  }

/--
Advances `columnOffset` by pretending that `s` is appended at `columnOffset`.
If `s` contains newlines, `columnOffset` is reset to 0 at the last newline in `s` and advanced
from there with the remainder of `s`.
-/
def advanceColumnOffset (columnOffset : Nat) (s : String.Slice) : Nat :=
  match s.revFind? '\n' with
  | none => columnOffset + s.positions.length
  | some nlPos => s.sliceFrom nlPos.next! |>.positions.length

structure parseComments.State where
  -- Read-only
  firstNewlinePos : String.Pos.Raw
  -- State
  ws : String.Slice
  closedComments : Array PendingComment
  openComment? : Option PendingComment
  commentNestingLevel : Nat

/--
Parses the comments in `initialWs` at a current column offset of `initialColumnOffset`.
Yields the set of comments and the column offset after `initialWs`.
-/
public def parseComments
    (lineInfos : Array SyntaxLineInfo) (originalTokenRange : Syntax.Range)
    (originalWhitespaceKind : Comment.Whitespace) (initialWs : String.Slice)
    : Array Comment := Id.run do
  let (_, s) :=
    StateT.run go {
      firstNewlinePos := initialWs.find '\n' |>.str.offset
      ws := initialWs
      closedComments := #[]
      openComment? := none
      commentNestingLevel := 0
    }
  let comments := groupComments s.closedComments
  let finalized := comments.map (·.finalize)
  return finalized

where

  go : StateM parseComments.State Unit := do
    let kinds := #[Comment.Kind.lineComment, Comment.Kind.blockComment]
    while !(← get).ws.isEmpty do
      match (← get).openComment? with
      | none =>
        let mut anySuccess := false
        for kind in kinds do
          let success ← tryOpenComment kind
          if success then
            anySuccess := true
            break
        if !anySuccess then
          skip
      | some _openComment =>
        let success ← tryCloseComment
        if success then
          continue
        let success ← tryNestComment
        if success then
          continue
        skip
    terminateEndOfWhitespaceComment

  advanceBy (pre : String) : StateM parseComments.State Unit := do
    modify fun s => {
      s with
      ws := s.ws.dropPrefix pre
      openComment? :=
        s.openComment?.map fun openComment => {
          openComment with
          raw := openComment.raw ++ pre
          endPos := openComment.endPos + pre
        }
    }

  skip : StateM parseComments.State Unit := do
    let some c := (← get).ws.front?
      | return
    advanceBy c.toString

  tryParse (pat : String) : StateM parseComments.State Bool := do
    if ! (← get).ws.startsWith pat then
      return false
    advanceBy pat
    return true

  tryOpenComment (kind : Comment.Kind) : StateM parseComments.State Bool := do
    let ws := (← get).ws
    let commentStartPos := ws.startPos.str
    let commentRawStartPos := commentStartPos.offset
    let (_, commentStartLineInfo) :=
      binSearchRightmost lineInfos commentRawStartPos (·.startPos) (· < ·) |>.get!
    let commentLineStartPos := ws.str.pos! commentStartLineInfo.startPos
    let commentStartColumnOffset :=
      ws.str.slice! commentLineStartPos commentStartPos |>.chars.length
    let isAfterNewline := commentRawStartPos >= (← get).firstNewlinePos
    let success ← tryParse kind.startSymbol
    if !success then
      return false
    modify fun s => {
      s with
      openComment? :=
        some {
          kind
          placement :=
            if originalWhitespaceKind matches .leading || isAfterNewline then
              .onLineBeforeToken
            else
              .afterToken
          originalTokenRange
          originalWhitespaceRange := ⟨0, 0⟩
          originalWhitespaceKind
          raw := kind.startSymbol
          content := #[]
          startColumnOffset := commentStartColumnOffset
          startPos := commentRawStartPos
          endPos := commentRawStartPos + kind.startSymbol
        }
      commentNestingLevel := 1
    }
    return true

  tryCloseComment : StateM parseComments.State Bool := do
    let some openComment := (← get).openComment?
      | return false
    let kind := openComment.kind
    let success ← tryParse kind.endSymbol
    if !success then
      return false
    let closedComment := (← get).openComment?.get!
    let commentNestingLevel := (← get).commentNestingLevel - 1
    if !kind.hasNesting || commentNestingLevel == 0 then
      modify fun s => {
        s with
        closedComments := s.closedComments.push closedComment
        openComment? := none
        commentNestingLevel
      }
    else
      modify fun s => { s with openComment? := some closedComment, commentNestingLevel }
    return true

  tryNestComment : StateM parseComments.State Bool := do
    let some openComment := (← get).openComment?
      | return false
    let kind := openComment.kind
    if !kind.hasNesting then
      return false
    let success ← tryParse kind.startSymbol
    if !success then
      return false
    modify fun s => { s with commentNestingLevel := s.commentNestingLevel + 1 }
    return true

  terminateEndOfWhitespaceComment : StateM parseComments.State Unit := do
    let some openComment := (← get).openComment?
      | return
    if ! openComment.kind.endSymbol.chars.all Char.isWhitespace then
      return
    let closedComment := openComment
    modify fun s => {
      s with
      closedComments := s.closedComments.push closedComment
      openComment? := none
    }

  groupComments (comments : Array PendingComment) : Array PendingComment := Id.run do
    if comments.isEmpty then
      return #[]
    let newlinePositions :=
      String.Slice.Pattern.ToForwardSearcher.toSearcher '\n' initialWs
        |>.filterMap fun
          | .matched startPos _ => some startPos.str.offset
          | .rejected .. => none
    let newlinePositions := newlinePositions.toArray
    let mut grouped := #[]
    let mut group := comments[0]!
    for c in comments[1:] do
      if ! isGroupable newlinePositions group c then
        grouped := grouped.push group
        group := c
        continue
      group := {
        kind := .lineComment
        placement := group.placement
        originalTokenRange := group.originalTokenRange
        originalWhitespaceRange :=
          ⟨group.originalWhitespaceRange.start, c.originalWhitespaceRange.stop⟩
        originalWhitespaceKind := group.originalWhitespaceKind
        content := #[]
        -- This is strictly speaking not a proper `raw` representation for the entire group,
        -- since it does not contain the whitespace in-between `group` and `c`,
        -- but this is not a problem since `PendingComment.finalize` can handle this disparity.
        raw := group.raw ++ c.raw
        startColumnOffset := group.startColumnOffset
        startPos := group.startPos
        endPos := c.endPos
      }
    grouped := grouped.push group
    return grouped

  isGroupable (newlinePositions : Array String.Pos.Raw) (group c : PendingComment)
      : Bool := Id.run do
    let isGroupableKind := group.kind matches .lineComment && c.kind matches .lineComment
    if !isGroupableKind then
      return false
    let isGroupablePlacement :=
      match group.placement, c.placement with
      | .onLineBeforeToken, .onLineBeforeToken
      | .afterToken, .afterToken =>
        true
      | .afterToken, .onLineBeforeToken =>
        group.startColumnOffset == c.startColumnOffset
      | .onLineBeforeToken, .afterToken =>
        false
    if !isGroupablePlacement then
      return false
    let newlineBeforeC? := binSearchRightmost newlinePositions c.startPos id (· < ·)
    let isGroupableAdjacency :=
      if let some (_, newlineBeforeC) := newlineBeforeC? then
        -- There is an empty line between `group` and `c`, which splits the group.
        newlineBeforeC < group.endPos
      else
        true
    if !isGroupableAdjacency then
      return false
    return true

/-- The comments in the leading whitespace of the first token of `stx`. -/
public def CommentCollector.Context.leadingComments (ctx : Context) (stx : Syntax)
    : Array Comment := Id.run do
  let info := stx.getHeadInfo
  let (some range, some leading) := (info.getRange?, info.getLeading?.bind (·.toSlice?))
    | return #[]
  return parseComments ctx.lineInfos range .leading leading

/-- The comments in the trailing whitespace of the last token of `stx`. -/
public def CommentCollector.Context.trailingComments (ctx : Context) (stx : Syntax)
    : Array Comment := Id.run do
  let info := stx.getTailInfo
  let (some range, some trailing) := (info.getRange?, info.getTrailing?.bind (·.toSlice?))
    | return #[]
  return parseComments ctx.lineInfos range .trailing trailing

/-- A comment claimed by a `CommentCollector`, together with the priority of that collector. -/
structure collectComments.Claim where
  priority : Nat
  /-- The range that the collector associated the comment with. -/
  associatedRange : Syntax.Range
  comment : Comment

structure collectComments.State where
  /-- The ranges of the comments that a `CommentCollector` claimed. -/
  claimedComments : Std.HashSet Syntax.Range := {}
  pendingComments : Array Comment := #[]
  comments : Std.HashMap Syntax.Range (Array Comment) := {}

abbrev collectComments.M α := StateT collectComments.State (Except Fmt.Error) α

/--
Collects all comments in `stx`, associating them either with the token immediately before a comment
on the same line or if the comment is on its own line with the next token following the comment.

The `collectors`, ordered by decreasing priority, override this association for the comments they
claim; when two collectors claim the same comment, the one with the greater priority wins.
-/
public partial def collectComments
    (env : Environment) (opts : Options) (collectors : Array CommentCollectorEntry)
    (lineInfos : Array SyntaxLineInfo) (stx : Syntax)
    : Except Fmt.Error (Std.HashMap Syntax.Range (Array Comment)) := do
  let claims := collectClaims
  let (_, s) ← StateT.run (s := mkInitialState claims) <| go stx
  -- Comments on lines after the last token (i.e. `s.pendingComments`) are ignored.
  -- When formatting entire files, there is always an `eoi` token at the end
  -- (so `s.pendingComments` is empty) and when formatting parts of files,
  -- we always want to ignore those comments anyways.
  return s.comments.map fun _ comments =>
    -- Claimed comments are collected before `go` runs, so they may be out of source order.
    comments.qsort (·.originalWhitespaceRange.start < ·.originalWhitespaceRange.start)
where
  /--
  Consults every collector for every node of `stx`, keyed by the range of the claimed comment.
  -/
  collectClaims : Std.HashMap Syntax.Range collectComments.Claim := Id.run do
    if collectors.isEmpty then
      return {}
    let (_, claims) := StateT.run (s := {}) <| goClaims { env, opts, lineInfos } stx
    return claims

  goClaims (ctx : CommentCollector.Context) (stx : Syntax)
      : StateM (Std.HashMap Syntax.Range collectComments.Claim) Unit := do
    let .node _ kind args := stx
      | return
    if kind == choiceKind then
      if let some firstAlternative := args[0]? then
        return ← goClaims ctx firstAlternative
    for entry in collectors do
      for (comment, associatedRange) in entry.collector ctx stx do
        modify (·.alter comment.originalWhitespaceRange fun
          | none =>
            some { priority := entry.priority, associatedRange, comment }
          | some claim =>
            if claim.priority < entry.priority then
              some { priority := entry.priority, associatedRange, comment }
            else
              some claim)
    for arg in args do
      goClaims ctx arg

  mkInitialState (claims : Std.HashMap Syntax.Range collectComments.Claim)
      : collectComments.State := {
    claimedComments := .ofArray claims.keysArray
    comments :=
      claims.fold (init := {}) fun comments _ claim =>
        comments.alter claim.associatedRange fun
          | none => some #[claim.comment]
          | some comments => some <| comments.push claim.comment
  }

  go (stx : Syntax) : collectComments.M Unit := do
    match stx with
    | .missing =>
      return
    | .atom info .. =>
      collectTokenComments info
    | .ident info .. =>
      collectTokenComments info
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      for arg in args do
        go arg
  collectTokenComments (info : SourceInfo) : collectComments.M Unit := do
    let some range := info.getRange?
      | throw <| .elaboration <| .malformedInputSyntax stx "missing token range"
        return
    if let some leading ← info.getLeading? |>.mapM toSlice then
      let comments ← dropClaimedComments <| parseComments lineInfos range .leading leading
      modify fun s => { s with pendingComments := s.pendingComments ++ comments }
    let pendingComments ← modifyGet fun s => (s.pendingComments, { s with pendingComments := #[] })
    addComments range pendingComments
    if let some trailing ← info.getTrailing? |>.mapM toSlice then
      let comments ← dropClaimedComments <| parseComments lineInfos range .trailing trailing
      let (commentsAfterToken, commentsOnLineBeforeToken) :=
        comments.partition (·.placement matches .afterToken)
      addComments range commentsAfterToken
      modify fun s => { s with pendingComments := s.pendingComments ++ commentsOnLineBeforeToken }
  /-- Drops the comments that a `CommentCollector` already associated with a range. -/
  dropClaimedComments (comments : Array Comment) : collectComments.M (Array Comment) := do
    let claimedComments := (← get).claimedComments
    if claimedComments.isEmpty then
      return comments
    return comments.filter (! claimedComments.contains ·.originalWhitespaceRange)
  addComments (range : Syntax.Range) (newComments : Array Comment) : collectComments.M Unit := do
    if newComments.isEmpty then
      return
    for newComment in newComments do
      let range :=
        match newComment.kind, newComment.placement with
        | .blockComment, .afterToken =>
          if newComment.content.size > 1 then
            let (_, commentStartLineInfo) :=
              binSearchRightmost lineInfos newComment.originalWhitespaceRange.start (·.startPos)
                  (· < ·)
                |>.get!
            commentStartLineInfo.tokenRanges[0]!
          else
            range
        | _, _ =>
          range
      modify fun s => {
        s with
        comments :=
          s.comments.alter range fun
            | none => some #[newComment]
            | some comments => some <| comments.push newComment
      }
  toSlice (s : Substring.Raw) : collectComments.M String.Slice := do
    let some s := s.toSlice?
      | throw <| .elaboration <|
          .malformedInputSyntax stx "substring is invalid and cannot be converted to a slice"
    return s

end Extraction

section Placement

public structure tryInsertingComments.Result where
  doc : Doc FmtCost
  pendingComments : Array Comment

private def placement (c : Comment) : Comment.RenderedPlacementKind :=
  match c.kind, c.placement with
  | .lineComment, .onLineBeforeToken
  | .blockComment, .onLineBeforeToken =>
    .afterClosestPreviousNewline
  | .lineComment, .afterToken =>
    .beforeClosestNextNewline
  | .blockComment, .afterToken =>
    if c.content.size > 1 then
      .afterClosestPreviousNewline
    else
      .afterToken

public structure tryInsertingComments.State where
  comments : Std.HashMap TagId (Syntax.Range × Array Comment)
  cache : Std.HashMap (PtrKey (Doc FmtCost)) tryInsertingComments.Result
  freshTagId : TagId
  syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind)

public def tryInsertingComments
    (doc : Doc FmtCost) (comments : Std.HashMap Syntax.Range (Array Comment)) (freshTagId : TagId)
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind))
    : Doc FmtCost × Std.HashMap Syntax.Range (Array TagId × RangeKind) := Id.run do
  -- It would be nice to have a range index structure for this.
  let handledWhitespaceSyntaxRanges :=
    syntaxToTags.filter (fun _ (_, kind) => kind matches .whitespace) |>.keysArray
  let comments :=
    comments.map fun _ cs =>
      cs.filter fun c => ! handledWhitespaceSyntaxRanges.any (·.includes c.originalWhitespaceRange)
  let comments := comments.filter fun _ cs => !cs.isEmpty
  let mut comments' := ∅
  for ⟨range, comments⟩ in comments do
    let tags := findBestTags range comments
    for (tag, rangeForTag, commentsForTag) in tags do
      comments' := comments'.insert tag (rangeForTag, commentsForTag)
  let init := { comments := comments', cache := ∅, freshTagId, syntaxToTags }
  let mut (doc, s) :=
    StateT.run (s := init) do
      let ⟨d, p⟩ ← go doc
      let d ← insertComments d p
      return d
  return (doc, s.syntaxToTags)
where
  findBestTags (range : Syntax.Range) (comments : Array Comment)
      : Array (TagId × Syntax.Range × Array Comment) := Id.run do
    if let some (tags, _) := syntaxToTags.get? range then
      return #[(tags[0]!, range, comments)]
    let syntaxToTagsByStart :=
      syntaxToTags.toArray.qsort fun (a, _) (b, _) =>
        let ord := (Ord.compare a.start b.start) |>.then (Ord.compare a.bsize b.bsize)
        ord.isLT
    let syntaxToTagsByStop :=
      syntaxToTags.toArray.qsort fun (a, _) (b, _) =>
        let ord := (Ord.compare a.stop b.stop) |>.then (Ord.compare b.bsize a.bsize)
        ord.isLT
    let (commentsWithPreviousRangeFallback, commentsWithNextRangeFallback) :=
      comments.partition fun c =>
        c.placement matches .afterToken && !(c.kind matches .blockComment && c.content.size > 1)
    let mut r := #[]
    if !commentsWithPreviousRangeFallback.isEmpty then
      if let some (_, rangeForPreviousRangeFallback, tagsForPreviousRangeFallback, _) :=
        binSearchRightmost syntaxToTagsByStop range.stop (·.1.stop) (· < ·)
      then
        r :=
          r.push (
            tagsForPreviousRangeFallback[0]!,
            rangeForPreviousRangeFallback,
            commentsWithPreviousRangeFallback
          )
    if !commentsWithNextRangeFallback.isEmpty then
      if let some (_, rangeForNextRangeFallback, tagsForNextRangeFallback, _) :=
        binSearchLeftmost syntaxToTagsByStart range.start (·.1.start) (· < ·)
      then
        r :=
          r.push
            (tagsForNextRangeFallback[0]!, rangeForNextRangeFallback, commentsWithNextRangeFallback)
    return r
  tag (doc : Doc FmtCost) (c : Comment) : StateM tryInsertingComments.State (Doc FmtCost) :=
    modifyGet fun s =>
      let (freshTagId, syntaxToTags, doc) :=
        TaggedDoc.taggedWithRange s.freshTagId s.syntaxToTags doc c.originalWhitespaceRange
          .whitespace
      (doc.doc, { s with freshTagId, syntaxToTags })
  renderingToDoc (r : Comment.Rendering) : Doc FmtCost :=
    let lines := r.rendered.split '\n' |>.map (Doc.text ·.toString) |>.toArray
    .aligned <| .joinUsing .hardNl lines
  insertComments (anchor : Doc FmtCost) (cs : Array Comment)
      : StateM tryInsertingComments.State (Doc FmtCost) := do
    let penalty := 999999 -- All failure fallbacks in the document should take priority.
    let mut result := anchor
    for c in cs.reverse do
      match placement c with
      | .afterClosestPreviousNewline =>
        let renderings := c.render
        let docs := renderings.map (Doc.initial <| renderingToDoc ·)
        let docs ← docs.mapM (tag · c)
        let doc := .oneOf docs
        let doc := .aligned <| Doc.free (doc ++ .hardNl) ++ result
        result :=
          .oneOf #[
            doc,
            Doc.costing (DefaultCost.ofFailureFallbackPenalty penalty) result
          ]
      | .beforeClosestNextNewline =>
        let renderings := c.render
        let docs := renderings.map (Doc.final <| renderingToDoc ·)
        let docs ← docs.mapM (tag · c)
        let doc := .oneOf docs
        let doc := result ++ Doc.free (.text " " ++ doc)
        result :=
          .oneOf #[
            doc,
            Doc.costing (DefaultCost.ofFailureFallbackPenalty penalty) result
          ]
      | .afterToken =>
        let renderings := c.render.filter (!·.isMultiLine)
        let afterLineDocs := renderings.map (Doc.final <| renderingToDoc ·)
        let afterLineDocs ← afterLineDocs.mapM (tag · c)
        let afterLineDoc := Doc.free <| .oneOf afterLineDocs
        let afterLineDoc := result ++ .text " " ++ afterLineDoc
        let afterTokenDocs := renderings.map (renderingToDoc ·)
        let afterTokenDocs ← afterTokenDocs.mapM (tag · c)
        let afterTokenDoc := .oneOf afterTokenDocs
        let afterTokenDoc := result ++ .text " " ++ afterTokenDoc
        result :=
          .oneOf #[
            afterTokenDoc,
            afterLineDoc,
            Doc.costing (DefaultCost.ofOverflowFallbackPenalty penalty) result
          ]
    return result
  goMemoized (v : Doc FmtCost) : StateM tryInsertingComments.State tryInsertingComments.Result := do
    let cacheKey := unsafe PtrKey.ofKey v
    if let some r := (← get).cache.get? cacheKey then
      return r
    let r ← go v
    modify fun s => { s with cache := s.cache.insert cacheKey r }
    return r
  go (d : Doc FmtCost) : StateM tryInsertingComments.State tryInsertingComments.Result := do
    match d with
    | .tagged id d =>
      let ⟨d, p⟩ ← goMemoized d
      let tagged := .tagged id d
      let some (_, commentsForId) := (← get).comments.get? id
        | return ⟨tagged, p⟩
      return ⟨tagged, p ++ commentsForId⟩
    | .failure | .text _ | .newline _ =>
      return ⟨d, #[]⟩
    | .unflattenable d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.unflattenable d, p⟩
    | .flattened d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.flattened d, p⟩
    | .indented n c d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.indented n c d, p⟩
    | .aligned d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.aligned d, p⟩
    | .unindented onlyNonCumulative d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.unindented onlyNonCumulative d, p⟩
    | .final d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.final d, p⟩
    | .initial d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.initial d, p⟩
    | .free d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.free d, p⟩
    | .guarded a d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.guarded a d, p⟩
    | .costing c d =>
      let ⟨d, p⟩ ← goMemoized d
      return ⟨.costing c d, p⟩
    | .either d1 d2 =>
      let ⟨d1, p1⟩ ← goMemoized d1
      let ⟨d2, p2⟩ ← goMemoized d2
      let pShared := p1.filter (p2.contains ·)
      let p1Unshared := p1.filter (! pShared.contains ·)
      let d1 ← insertComments d1 p1Unshared
      let p2Unshared := p2.filter (! pShared.contains ·)
      let d2 ← insertComments d2 p2Unshared
      return ⟨.either d1 d2, pShared⟩
    | .append d1 d2 =>
      let mut ⟨d1, p1⟩ ← goMemoized d1
      let (commentsBefore1, commentsAfter1) :=
        p1.partition (placement · matches .afterClosestPreviousNewline)
      if !d2.isAlwaysEmpty then
        d1 ← insertComments d1 commentsAfter1
      let mut ⟨d2, p2⟩ ← goMemoized d2
      let (commentsBefore2, commentsAfter2) :=
        p2.partition (placement · matches .afterClosestPreviousNewline)
      if !d1.isAlwaysEmpty then
        d2 ← insertComments d2 commentsBefore2
      p1 :=
        if !d2.isAlwaysEmpty then
          commentsBefore1
        else
          p1
      p2 :=
        if !d1.isAlwaysEmpty then
          commentsAfter2
        else
          p2
      return ⟨.append d1 d2, p1 ++ p2⟩

/-- Ranges of the tokens in `stx` that span several lines. -/
public partial def collectMultiLineTokenRanges (stx : Syntax) : Array Syntax.Range := go stx #[]
where
  go (stx : Syntax) (ranges : Array Syntax.Range) : Array Syntax.Range :=
    match stx with
    | .missing =>
      ranges
    | .atom info val =>
      pushMultiLineToken info val ranges
    | .ident info rawVal .. =>
      pushMultiLineToken info rawVal.toString ranges
    | .node _ kind args =>
      if kind == choiceKind then
        match args[0]? with
        | some firstAlternative => go firstAlternative ranges
        | none => ranges
      else
        args.foldl (fun ranges arg => go arg ranges) ranges
  pushMultiLineToken (info : SourceInfo) (val : String) (ranges : Array Syntax.Range)
      : Array Syntax.Range :=
    if ! val.contains '\n' then
      ranges
    else if let some range := info.getRange? then
      ranges.push range
    else
      ranges

/--
Determines the ranges in the rendered output that the multi-line tokens at `multiLineTokenRanges`
were rendered to, sorted ascendingly by start position.
Multi-line tokens that cannot be transferred to the rendered output because none of the formatters
tagged them are dropped; comments may then still end up within such a token.
-/
def determineRenderedMultiLineTokenRanges
    {rendering : String.Slice}
    (syntaxToRendered : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (multiLineTokenRanges : Array Syntax.Range)
    : Array rendering.Subslice := Id.run do
  let mut r := #[]
  for tokenRange in multiLineTokenRanges do
    let some renderedRanges := syntaxToRendered.get? tokenRange
      | continue
    for renderedRange in renderedRanges do
      -- A multi-line token may have been rendered on a single line, in which case no comment can
      -- end up within it.
      if renderedRange.toSlice.contains '\n' then
        r := r.push renderedRange
  return r.qsort (·.startInclusive < ·.startInclusive)

private def trimmedSubslice (s : String.Slice) : s.Subslice :=
  let start := s.skipPrefixWhile Char.isWhitespace
  let stop := s.skipSuffixWhile Char.isWhitespace
  if h : start ≤ stop then
    s.subslice start stop h
  else
    -- `s` is all whitespace: `start` is `s.endPos` and `stop` is `s.startPos`.
    s.subsliceFrom start

/--
Associates every comment with a specific range in the rendered output.
If the token that a comment is attached to is rendered in the output,
the comment will be associated with the rendered token.
If the token that a comment is attached to is not rendered,
the comments are associated with the next range before or after the token, depending on the
placement of the comment in the syntax.
If a specific range is rendered several times, we choose the smallest rendered range to attach
the comment to, so as to not duplicate the comment.
-/
def reassociateComments
    {rendering : String.Slice}
    (syntaxToRendered : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (comments : Std.HashMap Syntax.Range (Array Comment))
    : Std.HashMap rendering.Subslice (Array Comment) := Id.run do
  let syntaxToRenderedByStart :=
    syntaxToRendered.toArray.qsort fun (a, _) (b, _) =>
      let ord := (Ord.compare a.start b.start) |>.then (Ord.compare a.bsize b.bsize)
      ord.isLT
  let syntaxToRenderedByStop :=
    syntaxToRendered.toArray.qsort fun (a, _) (b, _) =>
      let ord := (Ord.compare a.stop b.stop) |>.then (Ord.compare b.bsize a.bsize)
      ord.isLT
  let comments := comments.toArray.qsort (fun (a, _) (b, _) => Lean.Fmt.compareRanges a b == .lt)
  let mut r : Std.HashMap rendering.Subslice (Array Comment) := ∅
  for (range, comments) in comments do
    let renderedCommentRanges :=
      determineRenderedCommentRanges syntaxToRenderedByStart syntaxToRenderedByStop range comments
    for (renderedRange, comments) in renderedCommentRanges do
      r :=
        r.alter renderedRange fun
          | none => some comments
          | some previousComments => some <| previousComments ++ comments
  return r
where
  determineRenderedCommentRanges
      (syntaxToRenderedByStart : Array (Syntax.Range × Std.HashSet rendering.Subslice))
      (syntaxToRenderedByStop : Array (Syntax.Range × Std.HashSet rendering.Subslice))
      (range : Syntax.Range) (comments : Array Comment)
      : Array (rendering.Subslice × Array Comment) := Id.run do
    if let some exactCommentRanges := syntaxToRendered.get? range then
      return #[(findBestCommentRange exactCommentRanges, comments)]
    -- If one of the formatters removed the token
    -- (or did not accurately track the `ref` for every `Doc.text` node)
    -- then we may not find an exact syntax match.
    -- In this case, we re-associate comments before a token and line comments after a token
    -- with the closest range after the token and block comments after a token with the closest
    -- range before the token.
    let (commentsWithPreviousRangeFallback, commentsWithNextRangeFallback) :=
      comments.partition fun c =>
        c.placement matches .afterToken && !(c.kind matches .blockComment && c.content.size > 1)

    let rangesForPreviousRangeFallback :=
      binSearchRightmost syntaxToRenderedByStop range.stop (·.1.stop) (· < ·)
        |>.map (·.2.2)
        |>.getD {trimmedSubslice rendering}
    let rangesForNextRangeFallback :=
      binSearchLeftmost syntaxToRenderedByStart range.start (·.1.start) (· < ·)
        |>.map (·.2.2)
        |>.getD {trimmedSubslice rendering}
    let mut r := #[]
    if !commentsWithPreviousRangeFallback.isEmpty then
      r :=
        r.push
          (findBestCommentRange rangesForPreviousRangeFallback, commentsWithPreviousRangeFallback)
    if !commentsWithNextRangeFallback.isEmpty then
      r := r.push (findBestCommentRange rangesForNextRangeFallback, commentsWithNextRangeFallback)
    return r

  findBestCommentRange (ranges : Std.HashSet rendering.Subslice) : rendering.Subslice := Id.run do
    let ranges := ranges.toArray
    let mut bestRange := ranges[0]!
    let mut bestLength := bestRange.toSlice.chars.length
    for range in ranges[1:] do
      let length := range.toSlice.chars.length
      if length < bestLength
        || length == bestLength && range.startInclusive < bestRange.startInclusive
      then
        bestRange := range
        bestLength := length
    return bestRange

def compareSubslicesLargest {s : String.Slice} (a b : s.Subslice) : Ordering :=
  Ord.compare a.startInclusive b.startInclusive |>.then (Ord.compare b.endExclusive a.endExclusive)

def determineCommentInsertions
    {rendering : String.Slice}
    (maxColumnWidth : Nat) (comments : Std.HashMap rendering.Subslice (Array Comment))
    (renderedMultiLineTokenRanges : Array rendering.Subslice)
    : Array (rendering.Pos × String) := Id.run do
  let lineInfos := collectLineInfos rendering
  -- We process comments from the back to the front
  -- (in the case of nested subslices, we process smaller subslices before larger ones).
  -- This ensures that we attempt to insert later comments on the same line first
  -- (after a token or at the end of the line) and when the line is full, earlier comments
  -- get moved before the line.
  let comments := comments.toArray.map fun (range, comments) => (range, comments.reverse)
  let comments := Std.TreeMap.ofArray comments (fun a b => compareSubslicesLargest b a)

  let mut containsEndOfLineComments := lineInfos.map (·.range.toSlice.contains "--")
  let mut r : Std.HashMap rendering.Pos String := ∅
  for (range, comments) in comments do
    for c in comments do
      for (rp, i) in c.renderedPlacements.zipIdx do
        let isFinalAlternative := i == c.renderedPlacements.size - 1
        match rp.kind with
        | .afterClosestPreviousNewline =>
          let (_, lineInfo) := findLineInfoContaining lineInfos range.startInclusive
          let lineInfo := escapeMultiLineTokens lineInfos renderedMultiLineTokenRanges lineInfo
          let insertionPos := lineInfo.range.startInclusive
          let insertedComment := rp.rendering.rendered.indent lineInfo.indentation ++ "\n"
          let newLineLength := insertedComment.chars.length - 1
          if !isFinalAlternative && newLineLength > maxColumnWidth then
            continue
          r :=
            r.alter insertionPos fun
              | none => some insertedComment
              | some existingInsertedComment => some <| insertedComment ++ existingInsertedComment
        | .beforeClosestNextNewline =>
          let (lineNum, lineInfo) := findLineInfoContaining lineInfos range.endExclusive
          if containsEndOfLineComments[lineNum]! then
            assert! !isFinalAlternative
            continue
          -- The end of the line lies within a token spanning several lines, so appending the
          -- comment there would insert it into the token.
          if multiLineTokenRangeContaining? renderedMultiLineTokenRanges lineInfo.range.endExclusive
            |>.isSome
          then
            assert! !isFinalAlternative
            continue
          let insertionPos := lineInfo.range.endExclusive
          if r.contains insertionPos then
            assert! !isFinalAlternative
            continue
          let insertedComment :=
            " " ++ rp.rendering.rendered.indent (lineInfo.length + 1) (skipFirstLine := true)
          r := r.insert insertionPos insertedComment
          if c.kind matches .lineComment then
            containsEndOfLineComments := containsEndOfLineComments.set! lineNum true
        | .afterToken =>
          unreachable!
        break
  return r.toArray.qsort (·.1 < ·.1)
where
  findLineInfoContaining (lineInfos : Array (LineInfo rendering)) (pos : rendering.Pos)
      : Nat × LineInfo rendering :=
    binSearchRightmost lineInfos pos (·.range.startInclusive) (· < ·) |>.get!

  /-- The token spanning several lines that strictly contains `pos`, if there is one. -/
  multiLineTokenRangeContaining?
      (renderedMultiLineTokenRanges : Array rendering.Subslice) (pos : rendering.Pos)
      : Option rendering.Subslice := do
    let (_, tokenRange) ←
      binSearchRightmost renderedMultiLineTokenRanges pos (·.startInclusive) (· < ·)
    guard <| tokenRange.startInclusive < pos && pos < tokenRange.endExclusive
    return tokenRange

  /--
  Moves a line whose start lies within a token spanning several lines to the line that the token
  starts on, so that inserting a comment before the line does not insert it into the token.
  -/
  escapeMultiLineTokens
      (lineInfos : Array (LineInfo rendering))
      (renderedMultiLineTokenRanges : Array rendering.Subslice) (lineInfo : LineInfo rendering)
      : LineInfo rendering := Id.run do
    let mut lineInfo := lineInfo
    repeat
      let some tokenRange :=
          multiLineTokenRangeContaining? renderedMultiLineTokenRanges lineInfo.range.startInclusive
        | break
      -- Strictly decreasing, since `tokenRange` starts before the current line.
      lineInfo := findLineInfoContaining lineInfos tokenRange.startInclusive |>.2
    return lineInfo

public def insertComments
    (maxColumnWidth : Nat)
    (rendering : String.Slice)
    (syntaxToRendered : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (multiLineTokenRanges : Array Syntax.Range)
    : String := Id.run do
  let comments := reassociateComments syntaxToRendered comments
  let renderedMultiLineTokenRanges :=
    determineRenderedMultiLineTokenRanges syntaxToRendered multiLineTokenRanges
  let insertions := determineCommentInsertions maxColumnWidth comments renderedMultiLineTokenRanges
  let mut r : String := ""
  let mut startPos : rendering.Pos := rendering.startPos
  for (insertionPos, comments) in insertions do
    r := r ++ rendering.slice! startPos insertionPos
    r := r ++ comments
    if let some charAfterComment := insertionPos.get? then
      let endCommentChar := comments.revChars.first?.get!
      if !endCommentChar.isWhitespace && !charAfterComment.isWhitespace then
        -- Padding after `comments`
        r := r ++ " "
    startPos := insertionPos
  r := r ++ rendering.slice! startPos rendering.endPos
  return r

end Placement
