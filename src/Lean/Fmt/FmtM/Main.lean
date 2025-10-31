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
public import Lean.Fmt.FmtM.LineInfo
public import Lean.Fmt.FmtM.Comments
public import Lean.Fmt.FmtM.Attribute
import Lean.Language.Lean
import Lean.Fmt.Util.Module
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

public def insertRemainingComments
    (rendering : String)
    (syntaxToTags : Std.HashMap Syntax.Range (Array TagId × RangeKind))
    (tagsToRendered : Std.TreeMap TagId (Std.HashSet rendering.toSlice.Subslice) compare)
    (comments : Std.HashMap Syntax.Range (Array Comment))
    (multiLineTokenRanges : Array Syntax.Range)
    : String :=
  let syntaxToRendered := connectTags syntaxToTags tagsToRendered
  let (syntaxToRenderedNodes, syntaxToRenderedWhitespace) :=
    syntaxToRendered.partition fun _ (_, kind) => !(kind matches .whitespace)
  let syntaxToRenderedNodes := syntaxToRenderedNodes.map fun _ (ranges, _) => ranges
  let syntaxToRenderedWhitespace := syntaxToRenderedWhitespace.map fun _ (ranges, _) => ranges
  let comments := filterAlreadyFormattedComments comments syntaxToRenderedWhitespace
  insertComments 100 rendering syntaxToRenderedNodes comments multiLineTokenRanges

private structure CommandOutput where
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
  let rawText := ctx.text.source.extract start stop
  let trailing := (← render ctx stx <| fmtTrailingWithRetainedNewlinesAndComments stx).rendering
  return leading ++ rawText ++ trailing

public def commandMain (ctx : Fmt.Context) (stx : Syntax) (fatal : Bool := false)
    : Except Error String := do
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
    let tagsToRendered := output.tags
    let rendering :=
      insertRemainingComments output.rendering syntaxToTags tagsToRendered comments
        multiLineTokenRanges
    return rendering
  catch e =>
    if fatal then
      throw e
    else
      commandRaw ctx stx

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
          && isSameSubstring trailing lastTrailing
        do
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
    let renderedHeader ← commandMain ctx headerStx fatal
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
    let input := initialSnap.ictx.inputString
    if cmdData.stx.isOfKind ``Parser.Command.eoi then
      return ← commandRaw ctx cmdData.stx
    let mut renderedCommand ← commandMain ctx cmdData.stx fatal
    -- The rendering of a command always starts at the beginning of a line, so it must be validated
    -- there as well: commands like `variable` require their continuation lines to be indented
    -- relative to the command's own column, which fails when the rendering is spliced in at the
    -- indentation the command had in the input.
    let rawStartPos := ctx.text.lineStart (ctx.text.toPosition prevCmdData.parserState.pos).line
    let (some startPos, some endPos) :=
        (input.pos? rawStartPos, cmdData.stx.getTrailingTailPos? >>= String.pos? input)
      | return renderedCommand
    let inputWithRenderedCommand :=
      input.extract input.startPos startPos ++ renderedCommand ++ input.extract endPos input.endPos
    let ictx := Parser.InputContext.mk inputWithRenderedCommand initialSnap.ictx.fileName
    let pmctx := {
      env := prevCmdData.cmdState.env
      options := prevCmdData.cmdState.scopes[0]!.opts
      currNamespace := prevCmdData.cmdState.scopes[0]!.currNamespace
      openDecls := prevCmdData.cmdState.scopes[0]!.openDecls
    }
    let parserState := { prevCmdData.parserState with pos := rawStartPos }
    let (stx, _, msgLog) := Parser.parseCommand ictx pmctx parserState MessageLog.empty
    if msgLog.hasErrors || stx.hasMissing then
      if fatal then
        throw <| .fmt <| .reparseFailure cmdData.stx
      renderedCommand ← commandRaw ctx cmdData.stx
    return renderedCommand
