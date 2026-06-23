/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Server.InfoUtils
public import Lean.Server.Completion.CompletionUtils

public section

namespace Lean.Server.Completion
open Elab

private def findBest?
    (infoTree : InfoTree)
    (gt : α → α → Bool)
    (f : ContextInfo → Info → PersistentArray InfoTree → Option α)
    : Option α :=
  (Id.run <| infoTree.visitM (postNode := choose)).join
where
  choose
      (ctx : ContextInfo)
      (info : Info)
      (cs : PersistentArray InfoTree)
      (childValues : List (Option (Option α)))
      : Option α :=
    let bestChildValue := childValues.map (·.join) |>.foldl (init := none) fun v best =>
      if isBetter v best then
        v
      else
        best
    if let some v := f ctx info cs then
      if isBetter v bestChildValue then
        v
      else
        bestChildValue
    else
      bestChildValue
  isBetter (a b : Option α) : Bool :=
    match a, b with
    | none,   none   => false
    | some _, none   => true
    | none,   some _ => false
    | some a, some b => gt a b

/--
If there are `Info`s that contain `hoverPos` and have a nonempty `LocalContext`,
yields the closest one of those `Info`s.
Otherwise, yields the closest `Info` that contains `hoverPos` and has an empty `LocalContext`.
-/
private def findClosestInfoWithLocalContextAt?
    (hoverPos : String.Pos.Raw)
    (infoTree : InfoTree)
    : Option (ContextInfo × Info) :=
  findBest? infoTree isBetter fun ctx info _ =>
    if info.occursInOrOnBoundary hoverPos then
      (ctx, info)
    else
      none
where
  isBetter (a b : ContextInfo × Info) : Bool :=
    let (_, ia) := a
    let (_, ib) := b
    if !ia.lctx.isEmpty && ib.lctx.isEmpty then
      true
    else if ia.lctx.isEmpty && !ib.lctx.isEmpty then
      false
    else if ia.isSmaller ib then
      true
    else if ib.isSmaller ia then
      false
    else
      false

private def findSyntheticIdentifierCompletion?
    (hoverPos : String.Pos.Raw)
    (infoTree : InfoTree)
    : Option ContextualizedCompletionInfo := do
  let some (ctx, info) := findClosestInfoWithLocalContextAt? hoverPos infoTree
    | none
  let some stack := info.stx.findStack? (·.getRange?.any (·.contains hoverPos (includeStop := true)))
    | none
  let stack := stack.dropWhile fun (stx, _) => !(stx matches `($_:ident) || stx matches `($_:ident.))
  let some (stx, _) := stack.head?
    | none
  let isDotIdCompletion := stack.any fun (stx, _) => stx matches `(.$_:ident)
  if isDotIdCompletion then
    -- An identifier completion is never useful in a dotId completion context.
    none
  let some (id, danglingDot) :=
      match stx with
      | `($id:ident) => some (id.getId, false)
      | `($id:ident.) => some (id.getId, true)
      | _ => none
    | none
  let tailPos := stx.getTailPos?.get!
  let hoverInfo :=
    if hoverPos < tailPos then
      HoverInfo.inside (hoverPos.byteDistance tailPos)
    else
      HoverInfo.after
  some { hoverInfo, ctx, info := .id stx id danglingDot info.lctx none }

private partial def isCursorOnWhitespace (fileMap : FileMap) (hoverPos : String.Pos.Raw) : Bool :=
  hoverPos.atEnd fileMap.source || (hoverPos.get fileMap.source).isWhitespace

private partial def isCursorInProperWhitespace (fileMap : FileMap) (hoverPos : String.Pos.Raw) : Bool :=
  (hoverPos.atEnd fileMap.source || (hoverPos.get fileMap.source).isWhitespace)
    && ((hoverPos.unoffsetBy ⟨1⟩).get fileMap.source).isWhitespace

private partial def isSyntheticTacticCompletion
    (fileMap  : FileMap)
    (hoverPos : String.Pos.Raw)
    (cmdStx   : Syntax)
    : Bool := Id.run do
  let hoverFilePos := fileMap.toPosition hoverPos
  go hoverFilePos cmdStx 0 none
where
  go
      (hoverFilePos         : Position)
      (stx                  : Syntax)
      (leadingWs            : Nat)
      (leadingTokenTailPos? : Option String.Pos.Raw)
      : Bool := Id.run do
    match stx.getPos?, stx.getTailPos? with
    | some startPos, some endPos =>
      let isCursorInCompletionRange :=
        startPos.byteIdx - leadingWs <= hoverPos.byteIdx
          && hoverPos.byteIdx <= endPos.byteIdx + stx.getTrailingSize
      if ! isCursorInCompletionRange then
        return false
      let mut wsBeforeArg := leadingWs
      let mut lastArgTailPos? := leadingTokenTailPos?
      for arg in stx.getArgs do
        if go hoverFilePos arg wsBeforeArg lastArgTailPos? then
          return true
        -- We must account for the whitespace before an argument because the syntax nodes we use
        -- to identify tactic blocks only start *after* the whitespace following a `by`, and we
        -- want to provide tactic completions in that whitespace as well.
        -- This method of computing whitespace assumes that there are no syntax nodes without tokens
        -- after `by` and before the first proper tactic syntax.
        wsBeforeArg := arg.getTrailingSize
        -- Track the tail position of the most recent preceding sibling that has a position so
        -- that empty tactic blocks (which lack positions) can locate their opening token (e.g.
        -- the `by` keyword) for indentation checking. The tail position lets us distinguish
        -- cursors before and after the opener on the opener's line.
        lastArgTailPos? := arg.getTailPos? <|> lastArgTailPos?
      return isCompletionInEmptyTacticBlock stx lastArgTailPos?
        || isCompletionAfterSemicolon stx
        || isCompletionOnTacticBlockIndentation hoverFilePos stx
    | _, _ =>
      -- Empty tactic blocks typically lack ranges since they do not contain any tokens.
      -- We do not perform more precise range checking in this case because we assume that empty
      -- tactic blocks always occur within other syntax with ranges that let us narrow down the
      -- search to the degree that we can be sure that the cursor is indeed in this empty tactic
      -- block.
      return isCompletionInEmptyTacticBlock stx leadingTokenTailPos?

  isCompletionOnTacticBlockIndentation
      (hoverFilePos : Position)
      (stx : Syntax)
      : Bool := Id.run do
    let some tacticsNode := getTacticsNode? stx
      | return false
    let some firstTacticPos := tacticsNode.getPos?
      | return false
    let firstTacticColumn := fileMap.toPosition firstTacticPos |>.column
    -- This ensures that we do not accidentally provide tactic completions in a term mode proof -
    -- tactic completions are only provided at the same indentation level as the other tactics in
    -- that tactic block.
    let isCursorInTacticBlock := hoverFilePos.column == firstTacticColumn
    return isCursorInProperWhitespace fileMap hoverPos && isCursorInTacticBlock

  isCompletionAfterSemicolon (stx : Syntax) : Bool := Id.run do
    let some tacticsNode := getTacticsNode? stx
      | return false
    let tactics := tacticsNode.getArgs
    -- We want to provide completions in the case of `skip;<CURSOR>`, so the cursor must only be on
    -- whitespace, not in proper whitespace.
    return isCursorOnWhitespace fileMap hoverPos && tactics.any fun tactic => Id.run do
      let some tailPos := tactic.getTailPos?
        | return false
      let isCursorAfterSemicolon :=
        tactic.isToken ";"
          && tailPos.byteIdx <= hoverPos.byteIdx
          && hoverPos.byteIdx <= tailPos.byteIdx + tactic.getTrailingSize
      return isCursorAfterSemicolon

  getTacticsNode? (stx : Syntax) : Option Syntax :=
    if stx.getKind == ``Parser.Tactic.tacticSeq1Indented then
      some stx[0]
    else if stx.getKind == ``Parser.Tactic.tacticSeqBracketed then
      some stx[1]
    else
      none

  isCompletionInEmptyTacticBlock (stx : Syntax) (leadingTokenTailPos? : Option String.Pos.Raw) : Bool := Id.run do
    if ! isCursorInProperWhitespace fileMap hoverPos then
      return false
    if ! isEmptyTacticBlock stx then
      return false
    -- Bracketed tactic blocks `{ ... }` are delimited by the braces themselves, so tactics
    -- inserted in an empty bracketed block can appear at any column between the braces
    -- (`withoutPosition` disables indentation constraints inside `tacticSeqBracketed`).
    if stx.getKind == ``Parser.Tactic.tacticSeqBracketed then
      let some openEndPos := stx[0].getTailPos?
        | return false
      let some closeStartPos := stx[2].getPos?
        | return false
      return openEndPos.byteIdx <= hoverPos.byteIdx && hoverPos.byteIdx <= closeStartPos.byteIdx
    return isAtExpectedTacticIndentation leadingTokenTailPos?

  -- After an empty tactic opener like `by`, tactics on a subsequent line must be inserted at an
  -- increased indentation level (two spaces past the indentation of the line containing the
  -- opener token). We mirror that here so that tactic completions are not offered in positions
  -- where a tactic could not actually be inserted. On the same line as the opener, completions
  -- are allowed only in the trailing whitespace past the opener — cursors earlier on the line
  -- belong to the surrounding term, not to the tactic block.
  isAtExpectedTacticIndentation (leadingTokenTailPos? : Option String.Pos.Raw) : Bool := Id.run do
    let some tokenTailPos := leadingTokenTailPos?
      | return true
    let hoverFilePos := fileMap.toPosition hoverPos
    let tokenTailFilePos := fileMap.toPosition tokenTailPos
    if hoverFilePos.line == tokenTailFilePos.line then
      return hoverPos.byteIdx >= tokenTailPos.byteIdx
    let expectedColumn := countLeadingSpaces (fileMap.lineStart tokenTailFilePos.line) + 2
    return hoverFilePos.column == expectedColumn

  countLeadingSpaces (pos : String.Pos.Raw) : Nat := Id.run do
    let mut p := pos
    let mut n : Nat := 0
    while ! p.atEnd fileMap.source do
      if p.get fileMap.source != ' ' then
        break
      p := p.next fileMap.source
      n := n + 1
    return n

  isEmptyTacticBlock (stx : Syntax) : Bool :=
    stx.getKind == ``Parser.Tactic.tacticSeq && isEmpty stx
      || stx.getKind == ``Parser.Tactic.tacticSeq1Indented && isEmpty stx
      || stx.getKind == ``Parser.Tactic.tacticSeqBracketed && isEmpty stx[1]

  isEmpty : Syntax → Bool
    | .missing       => true
    | .ident ..      => false
    | .atom ..       => false
    | .node _ _ args => args.all isEmpty

private partial def findOutermostContextInfo? (i : InfoTree) : Option ContextInfo :=
  go i
where
  go (i : InfoTree) : Option ContextInfo := do
    match i with
  | .context ctx i =>
    match ctx with
    | .commandCtx ctxInfo =>
      some { ctxInfo with }
    | _ =>
      -- This shouldn't happen (see the `PartialContextInfo` docstring),
      -- but let's continue searching regardless
      go i
  | .node _ cs =>
    cs.findSome? go
  | .hole .. =>
    none

private def findSyntheticTacticCompletion?
    (fileMap  : FileMap)
    (hoverPos : String.Pos.Raw)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Option ContextualizedCompletionInfo := do
  let ctx ← findOutermostContextInfo? infoTree
  if ! isSyntheticTacticCompletion fileMap hoverPos cmdStx then
    none
  -- Neither `HoverInfo` nor the syntax in `.tactic` are important for tactic completion.
  return { hoverInfo := HoverInfo.after, ctx, info := .tactic .missing }

private def findExpectedTypeAt (infoTree : InfoTree) (hoverPos : String.Pos.Raw) : Option (ContextInfo × Expr) := do
  let (ctx, .ofTermInfo i) ← infoTree.smallestInfo? fun i => Id.run do
      let some pos := i.pos?
        | return false
      let some tailPos := i.tailPos?
        | return false
      let .ofTermInfo ti := i
        | return false
      return ti.expectedType?.isSome && pos <= hoverPos && hoverPos <= tailPos
    | none
  (ctx, i.expectedType?.get!)

private partial def foldWithLeadingToken [Inhabited α]
    (f    : α → Option Syntax → Syntax → α)
    (init : α)
    (stx  : Syntax)
    : α :=
  let (_, r) := go none init stx
  r
where
  go [Inhabited α] (leadingToken? : Option Syntax) (acc : α) (stx : Syntax) : Option Syntax × α :=
    let acc := f acc leadingToken? stx
    match stx with
    | .missing  => (none, acc)
    | .atom ..  => (stx, acc)
    | .ident .. => (stx, acc)
    | .node _ _ args => Id.run do
      let mut acc := acc
      let mut lastToken? := none
      for arg in args do
        let (lastToken'?, acc') := go (lastToken? <|> leadingToken?) acc arg
        lastToken? := lastToken'? <|> lastToken?
        acc := acc'
      return (lastToken?, acc)

private def findWithLeadingToken?
    (p : Option Syntax → Syntax → Bool)
    (stx : Syntax)
    : Option Syntax :=
  foldWithLeadingToken (stx := stx) (init := none) fun foundStx? leadingToken? stx =>
    match foundStx? with
    | some foundStx => foundStx
    | none =>
      if p leadingToken? stx then
        some stx
      else
        none

private def isSyntheticStructFieldCompletion
    (fileMap  : FileMap)
    (hoverPos : String.Pos.Raw)
    (cmdStx   : Syntax)
    : Bool := Id.run do
  let isCursorOnWhitespace := isCursorOnWhitespace fileMap hoverPos
  let isCursorInProperWhitespace := isCursorInProperWhitespace fileMap hoverPos
  if ! isCursorOnWhitespace then
    return false

  let hoverFilePos := fileMap.toPosition hoverPos

  return Option.isSome <| findWithLeadingToken? (stx := cmdStx) fun leadingToken? stx => Id.run do
    let some leadingToken := leadingToken?
      | return false

    if stx.getKind != ``Parser.Term.structInstFields then
      return false

    let fieldsAndSeps := stx[0].getArgs
    let some outerBoundsStart := leadingToken.getTailPos? (canonicalOnly := true)
      | return false
    let some outerBoundsStop :=
        stx.getTrailingTailPos? (canonicalOnly := true)
          <|> leadingToken.getTrailingTailPos? (canonicalOnly := true)
      | return false
    let outerBounds : Lean.Syntax.Range := ⟨outerBoundsStart, outerBoundsStop⟩

    let isCompletionInEmptyBlock :=
      fieldsAndSeps.isEmpty && outerBounds.contains hoverPos (includeStop := true)
    if isCompletionInEmptyBlock then
      return true

    let isCompletionAfterSep := fieldsAndSeps.zipIdx.any fun (fieldOrSep, i) => Id.run do
      if i % 2 == 0 || !fieldOrSep.isAtom then
        return false
      let sep := fieldOrSep
      let some sepTailPos := sep.getTailPos?
        | return false
      return sepTailPos <= hoverPos
        && hoverPos.byteIdx <= sepTailPos.byteIdx + sep.getTrailingSize
    if isCompletionAfterSep then
      return true

    let isCompletionOnIndentation := Id.run do
      if ! isCursorInProperWhitespace then
        return false
      let some firstFieldPos := stx.getPos?
        | return false
      let firstFieldColumn := fileMap.toPosition firstFieldPos |>.column
      let isCursorInBlock := hoverFilePos.column == firstFieldColumn
      return isCursorInBlock
    return isCompletionOnIndentation

private def findSyntheticFieldCompletion?
  (fileMap  : FileMap)
  (hoverPos : String.Pos.Raw)
  (cmdStx   : Syntax)
  (infoTree : InfoTree)
  : Option ContextualizedCompletionInfo := do
  if ! isSyntheticStructFieldCompletion fileMap hoverPos cmdStx then
    none
  let (ctx, expectedType) ← findExpectedTypeAt infoTree hoverPos
  let .const typeName _ := expectedType.getAppFn
    | none
  if ! isStructure ctx.env typeName then
    none
  return { hoverInfo := HoverInfo.after, ctx, info := .fieldId .missing none .empty typeName }

def findSyntheticCompletions
    (fileMap  : FileMap)
    (hoverPos : String.Pos.Raw)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Array ContextualizedCompletionInfo :=
  let syntheticCompletionData? : Option ContextualizedCompletionInfo :=
    findSyntheticTacticCompletion? fileMap hoverPos cmdStx infoTree <|>
      findSyntheticFieldCompletion? fileMap hoverPos cmdStx infoTree <|>
        findSyntheticIdentifierCompletion? hoverPos infoTree
  syntheticCompletionData?.map (#[·]) |>.getD #[]

end Lean.Server.Completion
