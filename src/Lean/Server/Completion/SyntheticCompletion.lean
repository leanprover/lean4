/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Server.InfoUtils
import Lean.Server.Completion.CompletionUtils

namespace Lean.Server.Completion
open Elab

private def findBest?
    (infoTree : InfoTree)
    (gt : α → α → Bool)
    (f : ContextInfo → Info → PersistentArray InfoTree → Option α)
    : Option α :=
  infoTree.visitM (m := Id) (postNode := choose) |>.join
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
    (hoverPos : String.Pos)
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
    (hoverPos : String.Pos)
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
      HoverInfo.inside (tailPos - hoverPos).byteIdx
    else
      HoverInfo.after
  some { hoverInfo, ctx, info := .id stx id danglingDot info.lctx none }

private partial def getIndentationAmount (fileMap : FileMap) (line : Nat) : Nat := Id.run do
  let lineStartPos := fileMap.lineStart line
  let lineEndPos := fileMap.lineStart (line + 1)
  let mut it : String.Iterator := ⟨fileMap.source, lineStartPos⟩
  let mut indentationAmount := 0
  while it.pos < lineEndPos do
    let c := it.curr
    if c = ' ' || c = '\t' then
      indentationAmount := indentationAmount + 1
    else
      break
    it := it.next
  return indentationAmount

private partial def isCursorOnWhitespace (fileMap : FileMap) (hoverPos : String.Pos) : Bool :=
  fileMap.source.atEnd hoverPos || (fileMap.source.get hoverPos).isWhitespace

private partial def isCursorInProperWhitespace (fileMap : FileMap) (hoverPos : String.Pos) : Bool :=
  (fileMap.source.atEnd hoverPos || (fileMap.source.get hoverPos).isWhitespace)
    && (fileMap.source.get (hoverPos - ⟨1⟩)).isWhitespace

private partial def isSyntheticTacticCompletion
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    : Bool := Id.run do
  let hoverFilePos := fileMap.toPosition hoverPos
  let mut hoverLineIndentation := getIndentationAmount fileMap hoverFilePos.line
  if hoverFilePos.column < hoverLineIndentation then
    -- Ignore trailing whitespace after the cursor
    hoverLineIndentation := hoverFilePos.column
  go hoverFilePos hoverLineIndentation cmdStx 0
where
  go
      (hoverFilePos : Position)
      (hoverLineIndentation : Nat)
      (stx : Syntax)
      (leadingWs : Nat)
      : Bool := Id.run do
    match stx.getPos?, stx.getTailPos? with
    | some startPos, some endPos =>
      let isCursorInCompletionRange :=
        startPos.byteIdx - leadingWs <= hoverPos.byteIdx
          && hoverPos.byteIdx <= endPos.byteIdx + stx.getTrailingSize
      if ! isCursorInCompletionRange then
        return false
      let mut wsBeforeArg := leadingWs
      for arg in stx.getArgs do
        if go hoverFilePos hoverLineIndentation arg wsBeforeArg then
          return true
        -- We must account for the whitespace before an argument because the syntax nodes we use
        -- to identify tactic blocks only start *after* the whitespace following a `by`, and we
        -- want to provide tactic completions in that whitespace as well.
        -- This method of computing whitespace assumes that there are no syntax nodes without tokens
        -- after `by` and before the first proper tactic syntax.
        wsBeforeArg := arg.getTrailingSize
      return isCompletionInEmptyTacticBlock stx
        || isCompletionAfterSemicolon stx
        || isCompletionOnTacticBlockIndentation hoverFilePos hoverLineIndentation stx
    | _, _ =>
      -- Empty tactic blocks typically lack ranges since they do not contain any tokens.
      -- We do not perform more precise range checking in this case because we assume that empty
      -- tactic blocks always occur within other syntax with ranges that let us narrow down the
      -- search to the degree that we can be sure that the cursor is indeed in this empty tactic
      -- block.
      return isCompletionInEmptyTacticBlock stx

  isCompletionOnTacticBlockIndentation
      (hoverFilePos : Position)
      (hoverLineIndentation : Nat)
      (stx : Syntax)
      : Bool := Id.run do
    let isCursorInIndentation := hoverFilePos.column <= hoverLineIndentation
    if ! isCursorInIndentation then
      -- Do not trigger tactic completion at the end of a properly indented tactic block line since
      -- that line might already have entered term mode by that point.
      return false
    let some tacticsNode := getTacticsNode? stx
      | return false
    let some firstTacticPos := tacticsNode.getPos?
      | return false
    let firstTacticLine := fileMap.toPosition firstTacticPos |>.line
    let firstTacticIndentation := getIndentationAmount fileMap firstTacticLine
    -- This ensures that we do not accidentally provide tactic completions in a term mode proof -
    -- tactic completions are only provided at the same indentation level as the other tactics in
    -- that tactic block.
    let isCursorInTacticBlock := hoverLineIndentation == firstTacticIndentation
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
    if stx.getKind == `Lean.Parser.Tactic.tacticSeq1Indented then
      some stx[0]
    else if stx.getKind == `Lean.Parser.Tactic.tacticSeqBracketed then
      some stx[1]
    else
      none

  isCompletionInEmptyTacticBlock (stx : Syntax) : Bool :=
    isCursorInProperWhitespace fileMap hoverPos && isEmptyTacticBlock stx

  isEmptyTacticBlock (stx : Syntax) : Bool :=
    stx.getKind == `Lean.Parser.Tactic.tacticSeq && isEmpty stx
      || stx.getKind == `Lean.Parser.Tactic.tacticSeq1Indented && isEmpty stx
      || stx.getKind == `Lean.Parser.Tactic.tacticSeqBracketed && isEmpty stx[1]

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
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Option ContextualizedCompletionInfo := do
  let ctx ← findOutermostContextInfo? infoTree
  if ! isSyntheticTacticCompletion fileMap hoverPos cmdStx then
    none
  -- Neither `HoverInfo` nor the syntax in `.tactic` are important for tactic completion.
  return { hoverInfo := HoverInfo.after, ctx, info := .tactic .missing }

private def findExpectedTypeAt (infoTree : InfoTree) (hoverPos : String.Pos) : Option (ContextInfo × Expr) := do
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

private structure HoverData where
  fileMap                    : FileMap
  hoverPos                   : String.Pos
  hoverFilePos               : Position
  hoverLineIndentation       : Nat
  isCursorOnWhitespace       : Bool
  isCursorInProperWhitespace : Bool

private def HoverData.ofPosInFile
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    : HoverData := Id.run do
  let hoverFilePos := fileMap.toPosition hoverPos
  let mut hoverLineIndentation := getIndentationAmount fileMap hoverFilePos.line
  if hoverFilePos.column < hoverLineIndentation then
    -- Ignore trailing whitespace after the cursor
    hoverLineIndentation := hoverFilePos.column
  let isCursorOnWhitespace := Completion.isCursorOnWhitespace fileMap hoverPos
  let isCursorInProperWhitespace := Completion.isCursorInProperWhitespace fileMap hoverPos
  return {
    fileMap,
    hoverPos,
    hoverFilePos,
    hoverLineIndentation
    isCursorOnWhitespace,
    isCursorInProperWhitespace
  }

private structure SepBy1Data (ks : SyntaxNodeKinds) (sep : String) where
  sepBy1Stx   : Syntax.TSepArray ks sep
  outerBounds : String.Range

private def isCompletionInSepBy1
    {ks  : SyntaxNodeKinds}
    {sep : String}
    (hd  : HoverData)
    (sd  : SepBy1Data ks sep)
    : Bool := Id.run do
  if ! hd.isCursorOnWhitespace then
    return false

  let isCompletionInEmptyBlock :=
    sd.sepBy1Stx.elemsAndSeps.isEmpty && sd.outerBounds.contains hd.hoverPos (includeStop := true)
  if isCompletionInEmptyBlock then
    return true

  let isCompletionAfterSep := sd.sepBy1Stx.elemsAndSeps.any fun fieldOrSep => Id.run do
    if ! fieldOrSep.isToken sep then
      return false
    let some sepTailPos := fieldOrSep.getTailPos?
      | return false
    return sepTailPos <= hd.hoverPos
      && hd.hoverPos.byteIdx <= sepTailPos.byteIdx + fieldOrSep.getTrailingSize
  if isCompletionAfterSep then
    return true

  let isCompletionOnIndentation := Id.run do
    if ! hd.isCursorInProperWhitespace then
      return false
    let isCursorInIndentation := hd.hoverFilePos.column <= hd.hoverLineIndentation
    if ! isCursorInIndentation then
      return false
    let some firstFieldPos := sd.sepBy1Stx.elemsAndSeps[0]?.getD Syntax.missing |>.getPos?
      | return false
    let firstFieldLine := hd.fileMap.toPosition firstFieldPos |>.line
    let firstFieldIndentation := getIndentationAmount hd.fileMap firstFieldLine
    let isCursorInBlock := hd.hoverLineIndentation == firstFieldIndentation
    return isCursorInBlock
  return isCompletionOnIndentation

private def isSyntheticWhereBlockFieldCompletion
  (fileMap  : FileMap)
  (hoverPos : String.Pos)
  (cmdStx   : Syntax)
  : Bool :=
  let hd := HoverData.ofPosInFile fileMap hoverPos
  Option.isSome <| cmdStx.find? fun stx => Id.run do
    let `(Parser.Command.whereStructInst|where $structFields:whereStructField;* $[$_:whereDecls]?) :=
        stx
      | return false
    let some outerBoundStart := stx[0].getTailPos? (canonicalOnly := true)
      | return false
    let some outerBoundStop :=
        stx[2].getPos? (canonicalOnly := true)
        <|> stx[1].getTrailingTailPos? (canonicalOnly := true)
        <|> stx[0].getTrailingTailPos? (canonicalOnly := true)
      | return false
    let sd : SepBy1Data _ _ := {
      sepBy1Stx   := structFields
      outerBounds := {
        start := outerBoundStart
        stop  := outerBoundStop
      }
    }
    return isCompletionInSepBy1 hd sd

private def isSyntheticStructInstFieldCompletion
  (fileMap  : FileMap)
  (hoverPos : String.Pos)
  (cmdStx   : Syntax)
  : Bool :=
  let hd := HoverData.ofPosInFile fileMap hoverPos
  Option.isSome <| cmdStx.find? fun stx => Id.run do
    let `(Lean.Parser.Term.structInst| { $[$srcs,* with]? $fields,* $[..%$ell]? $[: $ty]? }) :=
        stx
      | return false
    let some outerBoundStart :=
        stx[1].getTailPos? (canonicalOnly := true)
        <|> stx[0].getTailPos? (canonicalOnly := true)
      | return false
    let some outerBoundStop :=
        stx[3].getPos? (canonicalOnly := true)
        <|> stx[4].getPos? (canonicalOnly := true)
        <|> stx[5].getPos? (canonicalOnly := true)
      | return false
    let sd : SepBy1Data _ _ := {
      sepBy1Stx   := fields
      outerBounds := {
        start := outerBoundStart
        stop  := outerBoundStop
      }
    }
    return isCompletionInSepBy1 hd sd

private def findSyntheticFieldCompletion?
  (fileMap  : FileMap)
  (hoverPos : String.Pos)
  (cmdStx   : Syntax)
  (infoTree : InfoTree)
  : Option ContextualizedCompletionInfo := do
  if ! isSyntheticWhereBlockFieldCompletion fileMap hoverPos cmdStx
      && ! isSyntheticStructInstFieldCompletion fileMap hoverPos cmdStx then
    none
  let (ctx, expectedType) ← findExpectedTypeAt infoTree hoverPos
  let .const typeName _ := expectedType.getAppFn
    | none
  if ! isStructure ctx.env typeName then
    none
  return { hoverInfo := HoverInfo.after, ctx, info := .fieldId .missing none .empty typeName }

def findSyntheticCompletions
    (fileMap  : FileMap)
    (hoverPos : String.Pos)
    (cmdStx   : Syntax)
    (infoTree : InfoTree)
    : Array ContextualizedCompletionInfo :=
  let syntheticCompletionData? : Option ContextualizedCompletionInfo :=
    findSyntheticTacticCompletion? fileMap hoverPos cmdStx infoTree <|>
      findSyntheticFieldCompletion? fileMap hoverPos cmdStx infoTree <|>
        findSyntheticIdentifierCompletion? hoverPos infoTree
  syntheticCompletionData?.map (#[·]) |>.getD #[]

end Lean.Server.Completion
