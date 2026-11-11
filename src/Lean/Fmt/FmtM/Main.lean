/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Environment
public import Lean.Fmt.FmtM.Error
import Lean.Fmt.FmtM.Basic
import Std.Data.HashMap.AdditionalOperations
import Lean.Fmt.FmtM.Comments
import Lean.Fmt.Core.Formatter
public import Lean.Data.Position
import Init.Data.String.Iter.Intercalate
public import Lean.Language.Lean.Types
public import Lean.Language.Lean.Util
public import Lean.Fmt.FmtM.LineInfo
public import Lean.Fmt.FmtM.Comments
public import Lean.Fmt.FmtM.Attribute
import Lean.Language.Lean
import Lean.Fmt.Util.Module
import Lean.Fmt.Util.RangeTree
import Init.System.Platform
import Std.Sync.Channel

namespace Lean.Fmt

def filterAlreadyFormattedComments
    {rendering : String.Slice}
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (syntaxToRenderedWhitespace : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    : Std.HashMap Syntax.Range (Array Comment) :=
  -- It would be nice to have a range index structure for this.
  let renderedWhitespaceSyntaxRanges := syntaxToRenderedWhitespace.keysArray
  let comments :=
    comments.map fun _ cs =>
      cs.filter fun c => ! renderedWhitespaceSyntaxRanges.any (·.includes c.originalWhitespaceRange)
  comments.filter fun _ cs => !cs.isEmpty

/--
Associates all syntax ranges that have been tagged by `Fmt.fmt` with the portions of the rendered
string that a specific tagged sub-document has been rendered to.
Tagged syntax ranges that do not appear in the rendered string at all are removed.
-/
def connectTags
    {rendering : String.Slice}
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind))
    (tagsToRendered : Std.TreeMap TagId (Std.HashSet rendering.Subslice))
    : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice × RangeKind) :=
  -- 1. All `TagId`s in `tagsToRendered` are contained in `syntaxToTags`.
  -- 2. Only `Syntax.Range`s that have been assigned by the document construction will appear in
  --   `syntaxToTags`. This includes `Syntax` subtrees for which `Fmt.fmt` has been called,
  --   as well as all tokens that appear in the constructed document for which `Fmt.text` has been
  --   called.
  -- 3. `TagId`s in `syntaxToTags` that are not used in the specific alternative chosen by the
  --   formatter do not appear in `tagsToRendered`.
  -- 4. Multiple `TagId`s are associated with the same `Syntax.Range` in `syntaxToTags` when
  --    `Fmt.fmt` is called for a `Syntax` subtree that contains another `Syntax` subtree of the
  --    same range for which `Fmt.fmt` has also been called.
  -- 5. Multiple `rendering.Subslice`s are associated with the same `TagId` in `tagsToRendered` when
  --    a sub-document is shared in multiple places in the same alternative,
  --    e.g. when a formatter yields the same document twice for the same token in the
  --    input `Syntax`.
  syntaxToTags.filterMap fun _ (tags, kind) => do
    let mut ranges := {}
    for tag in tags do
      if let some rendered := tagsToRendered.get? tag then
        ranges := ranges.insertMany rendered
    ranges := ranges.filter (!·.toSlice.isEmpty)
    guard <| !ranges.isEmpty
    return (ranges, kind)

def normalize (rendering : String) : String := Id.run do
  let lines := rendering.split '\n'
  let lines := lines.map (·.dropEndWhile ' ')
  let lines := lines.toArray.popWhile (String.Slice.isEmpty ·)
  let lines := lines.push ""
  return lines.iter.intercalateString "\n"

/--
A part of the rendering of a command that the formatter produced from the input syntax node or
token `input`, as a range of byte positions in the rendering.
-/
public structure RenderedUnit where
  input : Syntax
  start : String.Pos.Raw
  stop : String.Pos.Raw
deriving Inhabited

/--
Inserts the comments that the formatter has not rendered yet into `rendering`. Also returns the
insertions, as `insertComments` does.
-/
public def insertRemainingComments
    (rendering : String)
    (syntaxToRenderedNodes : Std.HashMap Syntax.Range (Std.HashSet rendering.toSlice.Subslice))
    (syntaxToRenderedWhitespace :
      Std.HashMap Syntax.Range (Std.HashSet rendering.toSlice.Subslice))
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (multiLineTokenRanges : Array Syntax.Range)
    : String × Array CommentInsertion :=
  let renderedLineComments := comments.fold (init := #[]) fun acc _ cs =>
    cs.foldl (init := acc) fun acc c =>
      if c.kind matches .lineComment then
        match syntaxToRenderedWhitespace.get? c.originalWhitespaceRange with
        | some subslices => acc ++ subslices.toArray.map (·.startInclusive.offset)
        | none => acc
      else
        acc
  let comments := filterAlreadyFormattedComments comments syntaxToRenderedWhitespace
  insertComments 100 rendering syntaxToRenderedNodes comments multiLineTokenRanges
    renderedLineComments

structure CommandOutput where
  rendering : String
  syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind)
  tagsToRendered : Std.TreeMap TagId (Std.HashSet rendering.toSlice.Subslice) compare

def render (ctx : Fmt.Context) (stx : Syntax) (act : FmtM TaggedDoc)
    : Except Error CommandOutput := do
  let r ← FmtM.run ctx act
  let doc := r.value.doc
  let output ←
    format? 100 200 doc (taintedResolution := false) |>.mapError (Error.ofFormattingError stx)
  return ⟨output.rendering, r.tags, output.tags⟩

def commandRaw (ctx : Fmt.Context) (stx : Syntax) : Except Error String := do
  let some fullSyntaxRange := stx.getRange?
    | throw <| .elaboration <| .malformedInputSyntax stx "missing range"
  let some start := ctx.text.source.pos? fullSyntaxRange.start
    | throw <| .elaboration <| .malformedInputSyntax stx "invalid range"
  let some stop := ctx.text.source.pos? fullSyntaxRange.stop
    | throw <| .elaboration <| .malformedInputSyntax stx "invalid range"
  let leading := (← render ctx stx <| fmtLeadingWithRetainedNewlinesAndComments stx).rendering
  let mut rawText := ctx.text.source.extract start stop
  -- `fmtTrailingWithRetainedNewlinesAndComments` leaves the comments on the line of the last token
  -- to the comment insertion, which a raw command does not use, so they stay as in the input.
  if let some commentsStopPos := afterTokenCommentsStop? then
    let some commentsStop := ctx.text.source.pos? commentsStopPos
      | throw <| .elaboration <| .malformedInputSyntax stx "invalid range"
    -- Without the newline of a line comment, which the trailing whitespace renders.
    let comments := ctx.text.source.extract stop commentsStop
    rawText := rawText ++ (comments.toSlice.dropEndWhile Char.isWhitespace).toString
  let trailing := (← render ctx stx <| fmtTrailingWithRetainedNewlinesAndComments stx).rendering
  return leading ++ rawText ++ trailing
where
  /--
  The end of the comments in the trailing whitespace of the last token of `stx` that start on the
  line of the token.
  -/
  afterTokenCommentsStop? : Option String.Pos.Raw := do
    let .original _ pos trailing endPos := stx.getTailInfo
      | none
    let comments := parseComments ctx.lineInfos ⟨pos, endPos⟩ .trailing (← trailing.toSlice?)
    let c ← comments.filter (·.placement matches .afterToken) |>.back?
    return c.originalWhitespaceRange.stop

/-- The ranges of the tokens and nodes of a syntax tree. -/
structure SyntaxRanges where
  /--
  The ranges of all tokens with text, in ascending order. All alternatives of a choice node span the
  same text, so only the tokens of the first alternative are included.
  -/
  tokens : Array Syntax.Range := #[]
  /-- For each range of a token or node of any alternative, a token or node with this range. -/
  nodes : Std.HashMap Syntax.Range Syntax := {}
deriving Inhabited

/-- The ranges of the tokens and nodes of `stx`. -/
partial def collectRanges (stx : Syntax) : SyntaxRanges :=
  go stx (collectTokens := true) |>.run {} |>.2
where
  /--
  Adds the ranges of the nodes of `stx` to the state, and also those of its tokens if
  `collectTokens`. Returns the range of `stx`.
  -/
  go (stx : Syntax) (collectTokens : Bool) : StateM SyntaxRanges (Option Syntax.Range) := do
    match stx with
    | .missing =>
      return none
    | .atom info _ | .ident info .. =>
      let .original (pos := pos) (endPos := endPos) .. := info
        | return none
      let range := ⟨pos, endPos⟩
      modify fun s => { s with nodes := s.nodes.insert range stx }
      -- A token without text can lie at the boundary of a unit without being part of it.
      if collectTokens && pos < endPos then
        modify fun s => { s with tokens := s.tokens.push range }
      return some range
    | .node _ kind args =>
      let mut start? := none
      let mut stop? := none
      for (arg, i) in args.zipIdx do
        let isLaterChoiceAlternative := kind == choiceKind && i > 0
        if let some argRange ← go arg (collectTokens && !isLaterChoiceAlternative) then
          if start?.isNone then
            start? := some argRange.start
          stop? := some argRange.stop
      let (some start, some stop) := (start?, stop?)
        | return none
      let range := ⟨start, stop⟩
      modify fun s => { s with nodes := s.nodes.insert range stx }
      return some range

/--
The units of the rendering of `stx`, as positions in the rendering with the comments of
`insertions` inserted (see `insertRemainingComments`).
-/
def renderedUnits
    {rendering : String.Slice} (stx : Syntax)
    (syntaxToRenderedNodes : Std.HashMap Syntax.Range (Std.HashSet rendering.Subslice))
    (insertions : Array CommentInsertion)
    : Array RenderedUnit := Id.run do
  let inputNodes := (collectRanges stx).nodes
  let sizeBefore := insertions.foldl (init := #[0]) fun sizes i => sizes.push (sizes.back! + i.size)
  let mut units := #[]
  for (inputRange, subslices) in syntaxToRenderedNodes do
    -- Formatters also tag parts of a token, e.g. the parts of a dotted identifier that they split
    -- at line-break points. Such parts are not units.
    let some input := inputNodes.get? inputRange
      | continue
    for subslice in subslices do
      units := units.push {
        input
        start := shift insertions sizeBefore subslice.startInclusive.offset (isStart := true)
        stop := shift insertions sizeBefore subslice.endExclusive.offset (isStart := false)
      }
  return units
where
  /--
  Maps `pos` to its position after the comments of `insertions` are inserted, where `sizeBefore[i]`
  is the total size of `insertions[0:i]`. A comment inserted at the start of a unit precedes the
  unit, and one inserted at its stop follows it.
  -/
  shift (insertions : Array CommentInsertion) (sizeBefore : Array Nat) (pos : String.Pos.Raw)
      (isStart : Bool) : String.Pos.Raw :=
    let numInsertionsBefore :=
      if isStart then
        binSearchRightmost insertions pos (·.pos) (· < ·) |>.map (·.1 + 1) |>.getD 0
      else
        binSearchLeftmost insertions pos (·.pos) (· < ·) |>.map (·.1) |>.getD insertions.size
    ⟨pos.byteIdx + sizeBefore[numInsertionsBefore]!⟩

/-- The rendering of a command. The units of a raw rendering are not recorded. -/
public structure CommandRendering where
  rendering : String
  units : Array RenderedUnit := #[]

public def commandMain (ctx : Fmt.Context) (stx : Syntax) (fatal : Bool := false)
    : Except Error CommandRendering := do
  try
    let comments ← collectComments ctx.env ctx.opts (getCommentCollectors ctx.env) ctx.lineInfos stx
    let multiLineTokenRanges := collectMultiLineTokenRanges stx
    let r ←
      FmtM.run ctx do
        let leading ← fmtLeadingWithRetainedNewlinesAndComments stx
        let doc ← fmt stx
        let trailing ← fmtTrailingWithRetainedNewlinesAndComments stx
        return leading ++ doc ++ trailing
    let doc := r.value.doc
    let syntaxToTags := r.tags
    let (doc, syntaxToTags) := tryInsertingComments doc comments r.freshTagId syntaxToTags
    let output ←
      format? 100 200 doc (taintedResolution := false) |>.mapError (Error.ofFormattingError stx)
    let syntaxToRendered := connectTags syntaxToTags output.tags
    let (syntaxToRenderedNodes, syntaxToRenderedWhitespace) :=
      syntaxToRendered.partition fun _ (_, kind) => !(kind matches .whitespace)
    let syntaxToRenderedNodes := syntaxToRenderedNodes.map fun _ (ranges, _) => ranges
    let syntaxToRenderedWhitespace := syntaxToRenderedWhitespace.map fun _ (ranges, _) => ranges
    let (rendering, insertions) :=
      insertRemainingComments output.rendering syntaxToRenderedNodes syntaxToRenderedWhitespace
        comments multiLineTokenRanges
    let units := renderedUnits stx syntaxToRenderedNodes insertions
    return { rendering, units }
  catch e =>
    if fatal then
      throw e
    else
      return { rendering := ← commandRaw ctx stx }

/-- How a unit of a rendering fails to parse back as one node or token at its range. -/
public inductive UnitMismatch where
  /-- A token of the reparsed syntax starts before the unit and ends after its start. -/
  | tokenCrossesStart
  /-- A token of the reparsed syntax starts in the unit and ends after its stop. -/
  | tokenCrossesStop
  /-- No node or token of the reparsed syntax has the range of the unit. -/
  | noNodeOrToken
deriving Inhabited, BEq, Repr

/--
Checks that each unit of the rendering of a command parses back as a unit: without the whitespace
and comments at its ends, its range is exactly the range of a node or token of `reparsed`, which
was parsed from an input that starts with the rendering. Returns the first unit that fails the
check.
-/
public def checkUnitRanges (reparsed : Syntax) (units : Array RenderedUnit)
    : Option (RenderedUnit × UnitMismatch) := Id.run do
  let { tokens, nodes } := collectRanges reparsed
  for unit in units do
    let first := firstTokenFrom tokens unit.start
    let afterLast := firstTokenFrom tokens unit.stop
    if first > 0 && tokens[first - 1]!.stop > unit.start then
      return some (unit, .tokenCrossesStart)
    if afterLast > 0 && tokens[afterLast - 1]!.stop > unit.stop then
      return some (unit, .tokenCrossesStop)
    if first < afterLast && !nodes.contains ⟨tokens[first]!.start, tokens[afterLast - 1]!.stop⟩ then
      return some (unit, .noNodeOrToken)
  return none
where
  /-- The index of the first of the sorted `tokens` that starts at or after `pos`. -/
  firstTokenFrom (tokens : Array Syntax.Range) (pos : String.Pos.Raw) : Nat :=
    binSearchLeftmost tokens pos (·.start) (· < ·) |>.map (·.1) |>.getD tokens.size

/--
The `FileMap` of `pre` followed by the text of `text` from `pos` on. It takes the line starts after
`pos` from `text`, so it only scans `pre`.
-/
public def fileMapWithPrefix (text : FileMap) (pre : String) (pos : text.source.Pos) : FileMap :=
  let source := pre ++ text.source.extract pos text.source.endPos
  let preLineStarts := (FileMap.ofString pre).positions
  let firstLineStartAfterPos :=
    binSearchLeftmost text.positions ⟨pos.offset.byteIdx + 1⟩ id (· < ·) |>.map (·.1)
      |>.getD text.positions.size
  if firstLineStartAfterPos == text.positions.size then
    -- `pos` is the end of `text.source`, so `source` is `pre`.
    { source, positions := preLineStarts }
  else
    let restLineStarts :=
      text.positions.extract firstLineStartAfterPos |>.map (shift pre pos.offset)
    -- The last entry of `preLineStarts` is the end of `pre`, which is not the end of `source`.
    { source, positions := preLineStarts.pop ++ restLineStarts }
where
  /-- Maps a line start after `pos` to its position when `pre` replaces the text before `pos`. -/
  shift (pre : String) (pos lineStart : String.Pos.Raw) : String.Pos.Raw :=
    ⟨lineStart.byteIdx - pos.byteIdx + pre.utf8ByteSize⟩

/-- The rendering of a command, parsed in place of the command. -/
public structure ReparsedCommand where
  /-- The rendering, followed by the input after the command. -/
  input : String
  stx : Syntax
  /-- The position after the reparsed command and its trailing whitespace. -/
  stopPos : String.Pos.Raw
  messages : MessageLog

/--
Parses `rendering` in place of the command `cmdData` of the file `ictx`. Returns `none` if the
command has no position.
-/
public def reparseRendering
    (ictx : Parser.InputContext) (cmdData prevCmdData : Language.Lean.CommandData)
    (rendering : String) : Option ReparsedCommand := do
  let text := ictx.fileMap
  let endPos ← cmdData.stx.getTrailingTailPos? >>= text.source.pos?
  -- The rendering of a command always starts at the beginning of a line, so it must be validated
  -- there as well: commands like `variable` require their continuation lines to be indented
  -- relative to the command's own column. The parser does not read the text before the command,
  -- so the input of the reparse starts with the rendering.
  let fileMap := fileMapWithPrefix text rendering endPos
  let pmctx := {
    env := prevCmdData.cmdState.env
    options := prevCmdData.cmdState.scopes[0]!.opts
    currNamespace := prevCmdData.cmdState.scopes[0]!.currNamespace
    openDecls := prevCmdData.cmdState.scopes[0]!.openDecls
  }
  let parserState := { prevCmdData.parserState with pos := 0 }
  let (stx, parserState, messages) :=
    Parser.parseCommand (.mk fileMap.source ictx.fileName (fileMap := fileMap)) pmctx parserState
      MessageLog.empty
  return { input := fileMap.source, stx, stopPos := parserState.pos, messages }

/-- Why the parser does not read a rendering with the structure that the formatter produced. -/
public inductive RenderingCheckFailure where
  /-- The rendering does not parse. -/
  | parseError
  /-- The parser reads the rendering as a command that stops before or after the rendering. -/
  | stopMismatch
  /-- The parser does not read `unit` as one node or token at its range. -/
  | unitMismatch (unit : RenderedUnit) (mismatch : UnitMismatch)
deriving Inhabited

/-- The error for a check failure of the rendering of the command `cmd`. -/
public def RenderingCheckFailure.toError (cmd : Syntax) : RenderingCheckFailure → Error
  | .parseError => .fmt <| .reparseFailure cmd
  | .stopMismatch => .fmt <| .reparseStopMismatch cmd
  | .unitMismatch unit _ => .fmt <| .reparseStructureMismatch unit.input

/-- Checks that `reparsed` reads `rendering` with the structure that the formatter produced. -/
public def checkReparse (reparsed : ReparsedCommand) (rendering : CommandRendering)
    : Option RenderingCheckFailure :=
  if reparsed.messages.hasErrors || reparsed.stx.hasMissing then
    some .parseError
  -- `checkUnitRanges` only sees the tokens of the reparsed command, so it does not notice a
  -- command that stops before or after its rendering.
  else if reparsed.stopPos != rendering.rendering.rawEndPos then
    some .stopMismatch
  else
    checkUnitRanges reparsed.stx rendering.units |>.map fun (unit, mismatch) =>
      .unitMismatch unit mismatch

/-- The state is the position in the file up to which the syntax has been validated. -/
abbrev validateSyntax.M α := StateT String.Pos.Raw (Except Error) α

/--
Validates that `stx` is the syntax of the entire file `text`:
* `stx` does not contain `Syntax.missing`.
* No source info in `stx` is synthetic, and all atoms and identifiers have original source info.
* For all alternatives of choice nodes, the concatenation of the leading whitespace, the text and
  the trailing whitespace of all atoms and identifiers is `text.source`.
* All source positions in `stx` are valid positions in `text.source`, and each position is the
  position of its part in this concatenation. The source info of a node, if any, matches the source
  info of its first and last token.
-/
public partial def validateSyntax (text : FileMap) (stx : Syntax) : Except Error Unit := do
  let ((), stopPos) ← go stx stx |>.run 0
  if stopPos != text.source.rawEndPos then
    throw <| malformed stx
      s!"the syntax ends at byte {stopPos.byteIdx}, but the file ends at \
        byte {text.source.rawEndPos.byteIdx}"
where
  malformed (stx : Syntax) (reason : String) : Error :=
    .elaboration <| .malformedInputSyntax stx reason
  go (parent stx : Syntax) : validateSyntax.M Unit := do
    match stx with
    | .missing =>
      throw <| malformed parent "the syntax contains `Syntax.missing`"
    | .atom info val =>
      goToken stx info val.toSlice
    | .ident info rawVal .. =>
      let some rawValSlice := rawVal.toSlice?
        | throw <| malformed stx "the raw text of an identifier is not a valid substring"
      if let .original (pos := pos) (endPos := endPos) .. := info then
        if rawVal.startPos != pos || rawVal.stopPos != endPos then
          throw <|
            malformed stx "the raw text of an identifier does not have the range of the identifier"
      goToken stx info rawValSlice
    | .node info kind args =>
      if info matches .synthetic .. then
        throw <| malformed stx "the syntax contains synthetic source info"
      if kind == choiceKind then
        goChoice stx args
      else
        for arg in args do
          go stx arg
      if let .original leading pos trailing endPos := info then
        let tokens := Syntax.node .none kind args
        let some (.original firstLeading firstPos ..) := tokens.getHeadInfo?
          | throw <| malformed stx "a node without tokens has source info"
        let some (.original _ _ lastTrailing lastEndPos) := tokens.getTailInfo?
          | throw <| malformed stx "a node without tokens has source info"
        let isSameSubstring (s1 s2 : Substring.Raw) :=
          s1.startPos == s2.startPos && s1.stopPos == s2.stopPos && s1.toSlice? == s2.toSlice?
        unless isSameSubstring leading firstLeading && pos == firstPos && endPos == lastEndPos
            && isSameSubstring trailing lastTrailing do
          throw <| malformed stx "the source info of a node does not match its first and last token"
  goChoice (stx : Syntax) (alternatives : Array Syntax) : validateSyntax.M Unit := do
    let some firstAlternative := alternatives[0]?
      | return
    let startPos ← get
    go stx firstAlternative
    let stopPos ← get
    for alternative in alternatives[1...*] do
      set startPos
      go stx alternative
      let alternativeStopPos ← get
      if alternativeStopPos != stopPos then
        throw <| malformed stx
          s!"the alternatives of a choice node end at different positions \
            (byte {stopPos.byteIdx} and byte {alternativeStopPos.byteIdx})"
  goToken (stx : Syntax) (info : SourceInfo) (val : String.Slice) : validateSyntax.M Unit := do
    let .original leading pos trailing endPos := info
      | if info matches .synthetic .. then
          throw <| malformed stx "the syntax contains synthetic source info"
        else
          throw <| malformed stx "a token has no source info"
    goWhitespace stx "leading whitespace" leading
    goPart stx "text" val pos endPos
    goWhitespace stx "trailing whitespace" trailing
  goWhitespace (stx : Syntax) (partName : String) (whitespace : Substring.Raw)
      : validateSyntax.M Unit := do
    let some slice := whitespace.toSlice?
      | throw <| malformed stx s!"the {partName} of a token is not a valid substring"
    goPart stx partName slice whitespace.startPos whitespace.stopPos
  /--
  Validates that `part` of the token `stx` starts at the current position and is the text of the
  file from `startPos` to `stopPos`. Moves the current position to `stopPos`.
  -/
  goPart
      (stx : Syntax) (partName : String) (part : String.Slice) (startPos stopPos : String.Pos.Raw)
      : validateSyntax.M Unit := do
    let pos ← get
    if startPos != pos then
      throw <| malformed stx
        s!"the {partName} of a token starts at byte {startPos.byteIdx}, but \
          the text before it ends at byte {pos.byteIdx}"
    let some filePart := do
        text.source.slice? (← text.source.pos? startPos) (← text.source.pos? stopPos)
      | throw <| malformed stx
          s!"the {partName} of a token has the range from byte \
            {startPos.byteIdx} to byte {stopPos.byteIdx}, which is not a valid range of the file"
    if part != filePart then
      throw <| malformed stx
        s!"the {partName} of a token does not match the file from byte \
          {startPos.byteIdx} to byte {stopPos.byteIdx}"
    set stopPos

def getNumThreads : BaseIO Nat := do
  if !System.Platform.isEmscripten then
    if let some s ← IO.getEnv "LEAN_NUM_THREADS" then
      return s.trimAscii.toNat?.getD 0
  return (System.Platform.Internal.getHardwareConcurrency ()).toNat

def getParallelism : BaseIO Nat := return max 1 (← getNumThreads)

public def fileMain
    (initialSnap : Language.Lean.InitialSnapshot)
    (cancelTks : Array IO.CancelToken := #[]) (fatal : Bool := false)
    : BaseIO (Except Error String) := do
  run
where
  run : ExceptT Error BaseIO String := do
    let text := initialSnap.ictx.fileMap
    let some finalCmdState := Language.Lean.waitForFinalCmdState? initialSnap
      | throw <| .input <| .importError initialSnap.stx
    let moduleData := Language.Lean.moduleData initialSnap |>.get
    if ← cancelTks.anyM (·.isSet) then
      throw <| .internal .cancelled
    if moduleData.hasParseErrors then
      throw <| .input .parseError
    let headerStx := moduleData.headerData.stx
    let cmdStxs := moduleData.cmdData.map (·.stx)
    let modStx ← mkModuleSyntax headerStx cmdStxs
    validateSyntax text modStx
    let (some headerCmdState, some headerParserState) :=
        (moduleData.headerData.cmdState?, moduleData.headerData.parserState?)
      | throw <| .input <| .importError headerStx
    let allCmdData : Array Language.Lean.CommandData :=
      #[⟨headerStx, headerParserState, headerCmdState⟩] ++ moduleData.cmdData
    let lineInfos := collectSyntaxLineInfos modStx
    let ctx : Fmt.Context := {
      lineInfos
      env := finalCmdState.env
      text
      resolveChoiceNode := fun range => do
        let infoTree ←
          Language.Lean.findInfoTreeAtPos initialSnap text range.start (includeStop := false) |>.get
        findChoiceResolution? infoTree range
      opts := finalCmdState.scopes[0]!.opts
    }
    let renderedHeader := (← commandMain ctx headerStx fatal).rendering
    let parallelism ← getParallelism
    let renderedCommandsMutex : Std.Mutex (Std.TreeMap Nat (Except Error String)) ← Std.Mutex.new ∅
    let jobs : Std.Channel Nat ← Std.Channel.new
    for cmdIdx in (1...allCmdData.size) do
      IO.wait (α := Unit) <| ← jobs.send cmdIdx
    let mut tasks := #[]
    for _ in (0...Nat.min parallelism (allCmdData.size - 1)) do
      let t ←
        BaseIO.asTask (prio := .dedicated) do
          while true do
            let some cmdIdx ← jobs.tryRecv
              | return
            if ← cancelTks.anyM (·.isSet) then
              renderedCommandsMutex.atomically do
                modify (·.insert cmdIdx <| .error <| .internal .cancelled)
              return
            let some cmdData := allCmdData[cmdIdx]?
              | unreachable!
            let some prevCmdData := allCmdData[cmdIdx - 1]?
              | unreachable!
            let rendered? := renderCommand ctx cmdData prevCmdData
            renderedCommandsMutex.atomically do modify (·.insert cmdIdx rendered?)
      tasks := tasks.push t
    for task in tasks do
      IO.wait (α := PUnit) task
    let renderedCommands : Array String ←
      (← renderedCommandsMutex.atomically get).valuesArray.mapM
        fun (renderedCommand? : Except Error String) => renderedCommand?
    let renderedFile := renderedHeader ++ renderedCommands.iter.joinString
    return normalize renderedFile
  renderCommand (ctx : Context) (cmdData prevCmdData : Language.Lean.CommandData)
      : Except Error String := do
    if cmdData.stx.isOfKind ``Parser.Command.eoi then
      return ← commandRaw ctx cmdData.stx
    let rendering ← commandMain ctx cmdData.stx fatal
    let some reparsed := reparseRendering initialSnap.ictx cmdData prevCmdData rendering.rendering
      | return rendering.rendering
    if let some failure := checkReparse reparsed rendering then
      if fatal then
        throw <| failure.toError cmdData.stx
      return ← commandRaw ctx cmdData.stx
    return rendering.rendering
