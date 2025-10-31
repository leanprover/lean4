/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Layouts
import Lean.Fmt.Util.RangeTree
import Lean.Fmt.Util.Basic
import Lean.Fmt.FmtM.Comments
meta import Lean.Parser.Term.Basic
import Init.Data

partial def Lean.Syntax.getTailToken? (stx : Syntax) : Option Syntax :=
  match stx with
  | .missing => none
  | .atom .. | .ident .. => some stx
  | .node _ _ args => args.findSomeRev? getTailToken?

partial def Lean.Syntax.getHeadToken? (stx : Syntax) : Option Syntax :=
  match stx with
  | .missing => none
  | .atom .. | .ident .. => some stx
  | .node _ _ args => args.findSome? getHeadToken?

def String.deindent (s : String) (numSpaces : Nat) : String :=
  s.split "\n" |>.map (dropSpaces · numSpaces |>.toString) |>.toList |> "\n".intercalate
where
  dropSpaces (line : Slice) (numSpaces : Nat) : Slice := Id.run do
    let mut line := line
    let mut numSpaces := numSpaces
    while numSpaces > 0 do
      if line.front != ' ' then
        break
      line := line.drop 1
      numSpaces := numSpaces - 1
    return line

public structure Lean.FmtM.Result (α : Type) extends Fmt.State where
  value : α

public def Lean.FmtM.Result.ofFinalState (value : α) (s : Fmt.State) : Lean.FmtM.Result α where
  value
  toState := s

public def Lean.FmtM.run (ctx : Fmt.Context) (act : FmtM α) : Except Fmt.Error (Result α) := do
  let r :=
    ReaderT.run act ctx
      |>.run {
        shareCommonState := default
        freshTagId := Nat.zero
        tags := ∅
        missingFormatters := ∅
        partialFormatters := ∅
      }
  match r with
  | .ok v s => return .ofFinalState v s
  | .error err _ => throw err

instance : MonadShareCommon Lean.FmtM where
  withShareCommon v _ :=
    modifyGet fun s =>
      let (v, shareCommonState) := s.shareCommonState.shareCommon v
      (v, { s with shareCommonState })

namespace Lean.Fmt

def FormattedWhitespace.merge (t1 t2 : FormattedWhitespace) : FormattedWhitespace where
  formattedLeadingRanges := t1.formattedLeadingRanges ++ t2.formattedLeadingRanges
  formattedTrailingRanges := t1.formattedTrailingRanges ++ t2.formattedTrailingRanges

public def getStxArg! (stx : Syntax) (i : Nat) : FmtM Syntax := do
  let arg := stx.getArg i
  if arg.isMissing then
    throw <| .partialFormatter
  return arg

public def getLineInfo! (pos : String.Pos.Raw) : FmtM SyntaxLineInfo := do
  let ctx ← read
  let (_, lineInfo) := binSearchRightmost ctx.lineInfos pos (·.startPos) (· < ·) |>.get!
  assert! lineInfo.startPos <= pos && pos <= lineInfo.endPos
  return lineInfo

public def getLineInfos (pos tailPos : String.Pos.Raw) : FmtM (Array SyntaxLineInfo) := do
  let ctx ← read
  let (startIdx, _) := binSearchRightmost ctx.lineInfos pos (·.startPos) (· < ·) |>.get!
  let (endIdx, _) := binSearchRightmost ctx.lineInfos tailPos (·.startPos) (· < ·) |>.get!
  let lineInfos := ctx.lineInfos[startIdx...=endIdx].toArray
  assert! !lineInfos.isEmpty
  return lineInfos

public def getNextLineInfo? (pos : String.Pos.Raw) : FmtM (Option SyntaxLineInfo) := do
  let ctx ← read
  let (i, _) := binSearchRightmost ctx.lineInfos pos (·.startPos) (· < ·) |>.get!
  return ctx.lineInfos[i + 1]?

public def fmtLeadingWhitespace
    (stx : Syntax)
    (fmtLeading : Syntax → Substring.Raw → FmtM (Array (TaggedDoc × Option Syntax.Range)))
    : FmtM TaggedDoc := do
  let some leadingTk := stx.getHeadToken?
    | return empty
  let some leading := leadingTk.getLeading?
    | return empty
  let leadingResult ← fmtLeading leadingTk leading
  let leadingFmt ←
    leadingResult.mapM fun (d, range?) => do
      match range? with
      | none => return d
      | some range => return { ← taggedWhitespace d.doc range with metaData := d.metaData }
  return join leadingFmt

public def fmtTrailingWhitespace
    (stx : Syntax)
    (fmtTrailing : Syntax → Substring.Raw → FmtM (Array (TaggedDoc × Option Syntax.Range)))
    : FmtM TaggedDoc := do
  let some trailingTk := stx.getTailToken?
    | return empty
  let some trailing := trailingTk.getTrailing?
    | return empty
  let trailingResult ← fmtTrailing trailingTk trailing
  let trailingFmt ←
    trailingResult.mapM fun (d, range?) => do
      match range? with
      | none => return d
      | some range => return { ← taggedWhitespace d.doc range with metaData := d.metaData }
  return join trailingFmt

def getInfixOperationOfParserDescr? (env : Environment) (opts : Options) (kind : SyntaxNodeKind)
    : Option InfixOperation := do
  let info ← env.find? kind
  guard <| info.type.isConstOf ``ParserDescr || info.type.isConstOf ``TrailingParserDescr
  let descr ← unsafe env.evalConst ParserDescr opts kind |>.toOption
  let ParserDescr.trailingNode _ prec lhsPrec
        (ParserDescr.binary `andthen (ParserDescr.symbol _) (ParserDescr.cat `term rhsPrec)) :=
      descr
    | none
  let isInfixl := prec == lhsPrec && lhsPrec + 1 == rhsPrec
  let precs? : Option InfixOperationPrecs := some { prec, lhsPrec, rhsPrec }
  if isInfixl then
    return { sparse := false, precs? }
  let isInfixr := prec == rhsPrec && lhsPrec == rhsPrec + 1
  if isInfixr then
    return { sparse := false, precs? }
  let isInfix := prec + 1 == lhsPrec && lhsPrec == rhsPrec
  if isInfix then
    return { sparse := true, precs? }
  none

def getInfixOperation? (env : Environment) (opts : Options) (kind : SyntaxNodeKind)
    : Option InfixOperation := do
  match infixFmtAttribute.getValues env kind |>.head? with
  | none => getInfixOperationOfParserDescr? env opts kind
  | some op => return op

def hasPrefixFormatter (env : Environment) (opts : Options) (kind : SyntaxNodeKind) : Bool :=
  Option.isSome <| do
    let info ← env.find? kind
    guard <| info.type.isConstOf ``ParserDescr
    let descr ← unsafe env.evalConst ParserDescr opts kind |>.toOption
    let ParserDescr.node _ prec
          (ParserDescr.binary `andthen (ParserDescr.symbol _) (ParserDescr.cat `term argPrec)) :=
        descr
      | none
    guard <| prec == argPrec

def hasPostfixFormatter (env : Environment) (opts : Options) (kind : SyntaxNodeKind) : Bool :=
  Option.isSome <| do
    let info ← env.find? kind
    guard <| info.type.isConstOf ``TrailingParserDescr
    let descr ← unsafe env.evalConst ParserDescr opts kind |>.toOption
    let ParserDescr.trailingNode _ prec lhsPrec (ParserDescr.symbol _) := descr
      | none
    guard <| prec == lhsPrec

/-- Parser aliases that do not produce any syntax, i.e. pretty printing hints and input checks. -/
private def emptyParserAliases : Array Name := #[
  `ws, `noWs, `linebreak, `colGt, `colGe, `colEq, `lineEq, `ppSpace, `ppLine, `ppHardSpace,
  `ppAllowUngrouped, `ppHardLineUnlessUngrouped
]

/-- Parser aliases that do not produce any syntax beyond that of their argument. -/
private def transparentParserAliases : Array Name := #[
  `atomic, `group, `patternIgnore, `withPosition, `withoutPosition, `withoutForbidden, `ppGroup,
  `ppRealGroup, `ppRealFill, `ppIndent, `ppDedent, `ppDedentIfGrouped
]

/--
Checks whether `descr` exclusively parses atoms, so that the syntax it produces is fully
determined by its syntax node kind.
-/
private def isAtomicParserDescr : ParserDescr → Bool
  | .symbol .. | .nonReservedSymbol .. | .unicodeSymbol .. =>
    true
  | .const alias =>
    emptyParserAliases.contains alias
  | .unary alias p =>
    transparentParserAliases.contains alias && isAtomicParserDescr p
  | .binary alias p₁ p₂ =>
    (alias == `andthen || alias == `orelse) && isAtomicParserDescr p₁ && isAtomicParserDescr p₂
  | .node _ _ p | .nodeWithAntiquot _ _ p =>
    isAtomicParserDescr p
  | _ =>
    false

def hasAtomicFormatter (env : Environment) (opts : Options) (kind : SyntaxNodeKind) : Bool :=
  Option.isSome <| do
    let info ← env.find? kind
    guard <| info.type.isConstOf ``ParserDescr
    let descr ← unsafe env.evalConst ParserDescr opts kind |>.toOption
    -- Trailing nodes are excluded because their syntax contains the operand preceding the operator.
    guard <| ! descr matches .trailingNode ..
    guard <| isAtomicParserDescr descr

public def getConditionalFormatter? (env : Environment) (kind : SyntaxNodeKind)
    : Option ConditionalFmt :=
  conditionalFmtAttribute.getValues env kind |>.head?

public def getQuantifierFormatter? (env : Environment) (kind : SyntaxNodeKind)
    : Option QuantifierFmt :=
  quantifierFmtAttribute.getValues env kind |>.head?

structure QuantifierChain where
  quantifiers : Array QuantifierHeadComponents
  body : Syntax
deriving Inhabited

/--
Collects the maximal chain of nested quantifiers starting at `stx`, which is deconstructed using
`deconstructQuantifier?`. Every subsequent quantifier of the chain is deconstructed using the
formatter registered for its kind, so that chains may span several quantifier kinds
(e.g. `∀ ε > 0, ∃ δ > 0, ∀ x, p x`).
-/
def quantifierChain (env : Environment) (deconstructQuantifier? : QuantifierFmt) (stx : Syntax)
    : QuantifierChain := Id.run do
  let mut deconstructQuantifier? := some deconstructQuantifier?
  let mut stx := stx
  let mut quantifiers : Array QuantifierHeadComponents := #[]
  while true do
    let some deconstruct := deconstructQuantifier?
      | return { quantifiers, body := stx }
    let some components := deconstruct stx
      | return { quantifiers, body := stx }
    quantifiers := quantifiers.push components.toQuantifierHeadComponents
    stx := components.body
    deconstructQuantifier? := getQuantifierFormatter? env stx.getKind
  unreachable!

variable (env : Environment) (opts : Options) (op : InfixOperation) in
partial def collectInfixOperatorChain (stx : Syntax) : Array Syntax := Id.run do
  if stx.getNumArgs != 3 then
    return #[stx]
  let op'? := getInfixOperation? env opts stx.getKind
  if !(op.precs?.isSome && op'?.any (·.precs? == op.precs?)
    || op.extendedChainKinds.contains stx.getKind)
  then
    return #[stx]
  let left := stx[0]
  let op := stx[1]
  let right := stx[2]
  if !op.isAtom then
    return #[stx]
  let leftChain := collectInfixOperatorChain left
  let rightChain := collectInfixOperatorChain right
  return leftChain ++ #[op] ++ rightChain

public def fmtRawAsInSource (isFallback : Bool := false) : Fmt := fun stx => do
  -- We assume that this function is not being called for syntax that may contain tokens with
  -- comments.
  -- TODO: Remove once we have formatting for Verso docstrings.
  let some pos := stx.getPos?
    | return ← text "" stx
  let some tailPos := stx.getTailPos?
    | return ← text "" stx
  let ctx ← read
  let some pos := ctx.text.source.pos? pos
    | throw <| .elaboration <| .malformedInputSyntax stx "invalid syntax position"
  let some tailPos := ctx.text.source.pos? tailPos
    | throw <| .elaboration <| .malformedInputSyntax stx "invalid syntax position"
  let source := ctx.text.source.extract pos tailPos
  let lines := source.split "\n" |>.map (Doc.text ·.toString) |>.toArray
  let rawDoc := Doc.unindented (onlyNonCumulative := false) <| .joinUsing .hardNl lines
  let mut rawDoc ← taggedNode rawDoc stx
  if isFallback then
    rawDoc := mkRawFallback rawDoc
  return rawDoc

structure fmtRaw.Context where
  anchorColumnPos : Nat
  firstTokenPos : String.Pos.Raw
  lastTokenTailPos : String.Pos.Raw

mutual

partial def fmtChoiceNode : Fmt := fun choiceStx => do
  if choiceStx.getNumArgs == 0 then
    return ← text "" choiceStx
  let saved ← get
  let mut first? : Option (TaggedDoc × State) := none
  let mut reference? : Option (TaggedDoc × State) := none
  for stx in choiceStx.getArgs do
    set saved
    let doc ← fmt stx
    if first?.isNone then
      first? := some (doc, ← get)
    if isRawFallback doc then
      continue
    let some (referenceDoc, _) := reference?
      | reference? := some (doc, ← get)
        continue
    if doc.doc != referenceDoc.doc then
      set saved
      return ← disambiguateChoiceNode choiceStx
  let some (referenceDoc, referenceState) := reference?
    | let (firstDoc, firstState) := first?.get!
      set firstState
      return firstDoc
  set referenceState
  return referenceDoc
where
  disambiguateChoiceNode : Fmt := fun stx => do
    let ctx ← read
    let some range := stx.getRange?
      | throw <| .elaboration <| .ambiguousChoiceNode stx
    let some i := ctx.resolveChoiceNode range
      | throw <| .elaboration <| .ambiguousChoiceNode stx
    if i.stx.getNumArgs != stx.getNumArgs then
      throw <| .elaboration <| .ambiguousChoiceNode stx
    let some chosenAltStx := stx.getArgs[i.chosenAltIdx]?
      | throw <| .elaboration <| .ambiguousChoiceNode stx
    fmt chosenAltStx

public partial def fmtInfixOperator (op : InfixOperation) : Fmt := fun stx => do
  let ctx ← read
  let op := { op with extendedChainKinds := op.extendedChainKinds.insert stx.getKind }
  let chain := collectInfixOperatorChain ctx.env ctx.opts op stx
  let chain ← chain.mapM fmt
  let format :=
    if op.sparse then
      .sparse (separateFinalOperand := op.separateFinalOperand)
    else
      .dense
  return Layouts.infixOperator (format := format) chain

public partial def fmtPrefixOperator : Fmt := fun stx => do
  if stx.getNumArgs != 2 then
    throw .partialFormatter
  let op ← getStxArg! stx 0
  let opIsIdentComponent := Lean.Name.escapePart op.getAtomVal == op.getAtomVal
  let op ← fmt op
  let operand ← fmt (← getStxArg! stx 1)
  let format :=
    if opIsIdentComponent then
      .withSpacing
    else
      .withoutSpacingIfAtomic
  return Layouts.prefixOperator op operand format

public partial def fmtPostfixOperator : Fmt := fun stx => do
  if stx.getNumArgs != 2 then
    throw .partialFormatter
  let operand ← fmt (← getStxArg! stx 0)
  let op ← getStxArg! stx 1
  let opIsIdentComponent := Lean.Name.escapePart op.getAtomVal == op.getAtomVal
  let op ← fmt op
  let format :=
    if opIsIdentComponent then
      .withSpacing
    else
      .withoutSpacing
  return Layouts.postfixOperator operand op format

public partial def fmtConditional (initialFmt : ConditionalFmt) : Fmt := fun stx => do
  let env := (← read).env
  let mut some c ← initialFmt stx
    | throw .partialFormatter
  let allowFlattening := !(← hasNewline stx)
  while true do
    let mut (some elseTk, some elseBody) := (c.elseTk?, c.elseBody?)
      | break
    if let `(Parser.Tactic.tacticSeq| $tactic:tactic) := elseBody then
      -- We allow the `if-then-else-if-else` chaining to look through single-element
      -- `tacticSeq`s, because `if-then-else-if-else` chains in tactic sequences always contain
      -- an intermediate `tacticSeq` node.
      -- `do` conditionals do not have this problem.
      elseBody := tactic
    let some f := getConditionalFormatter? env elseBody.getKind
      | break
    let some e ← f elseBody
      | break
    c := {
      c with
      elseIfs :=
        c.elseIfs.push {
          elseTk := elseTk
          ifTk := e.ifTk
          cond := e.cond
          thenTk := e.thenTk
          body := e.thenBody
        }
      elseTk? := e.elseTk?
      elseBody? := e.elseBody?
    }
  let ifTk ← fmt c.ifTk
  let cond := c.cond
  let thenTk ← fmt c.thenTk
  let thenBody ← fmt c.thenBody
  let elseIfs : Array (Layouts.Types.ElseIf) ←
    c.elseIfs.mapM fun ei =>
      return {
        elseTk := ← fmt ei.elseTk
        ifTk := ← fmt ei.ifTk
        cond := ei.cond
        thenTk := ← fmt ei.thenTk
        thenBlock := ← fmt ei.body
      }
  let elseTk? := (← c.elseTk?.mapM fmt).getD empty
  let elseBody? := (← c.elseBody?.mapM fmt).getD empty
  return Layouts.conditional ifTk cond thenTk thenBody elseIfs elseTk? elseBody? allowFlattening
where
  hasNewline (stx : Syntax) : FmtM Bool := do
    let some pos := stx.getPos?
      | return false
    let some tailPos := stx.getTailPos?
      | return false
    let lineInfos ← getLineInfos pos tailPos
    return lineInfos.size > 1

public partial def fmtBinderGroups (bgs : BinderGroups)
    : FmtM (Array (Array (Array TaggedDoc))) := do
  bgs.mapM fun bg => bg.mapM fun sbg => sbg.mapM fmt

public partial def fmtWithBinderPred (lhs : Syntax) (rhs : TSyntax `binderPred)
    : FmtM TaggedDoc := do
  let lhs ← fmt lhs
  let rhs ← fmt rhs
  return nested <| Layouts.horizontalOrVertical #[lhs, rhs]

public partial def fmtQuantifierHead (head : QuantifierHeadComponents)
    : FmtM Layouts.Types.QuantifierHead := do
  let quantifier ← fmt head.quantifier
  let binderGroups ←
    match head.binders with
    | .binders groups => fmtBinderGroups groups
    | .pred lhs rhs => pure #[#[#[← fmtWithBinderPred lhs rhs]]]
  let typeAscriptionTk? := (← head.typeAscriptionTk?.mapM fmt).getD empty
  let type? := (← head.type?.mapM fmt).getD empty
  let commaTk ← fmt head.commaTk
  return { quantifier, binderGroups, typeAscriptionTk?, type?, separationTk := commaTk }

public partial def fmtQuantifier (deconstructQuantifier? : QuantifierFmt) : Fmt := fun stx => do
  let chain := quantifierChain (← read).env deconstructQuantifier? stx
  if chain.quantifiers.isEmpty then
    throw .partialFormatter
  let quantifierHeads ← chain.quantifiers.mapM fmtQuantifierHead
  let body ← fmt chain.body
  return Layouts.quantified quantifierHeads body

public partial def getFormatterForKind? (kind : SyntaxNodeKind) : FmtM (Option (Name × Fmt)) := do
  let ctx ← read
  return getFmtProviders ctx.env |>.findSome? (·.provider ctx.env ctx.opts kind)

public partial def fmtRaw (isFallback : Bool := false) : Fmt := fun stx => do
  let some pos := stx.getPos?
    | return ← text "" stx
  let some tailPos := stx.getTailPos?
    | return ← text "" stx
  let lineInfos ← getLineInfos pos tailPos
  let startColumnPos := pos.unoffsetBy lineInfos[0]!.startPos |>.offsetOfPos lineInfos[0]!.line
  let anchorLineInfos :=
    lineInfos[1...*].toArray.filter fun li =>
      li.tokenRanges.all (·.start >= li.startPos) && li.length > li.indentation
  let anchorColumnPositions := #[startColumnPos] ++ anchorLineInfos.map (·.indentation)
  let anchorColumnPos := anchorColumnPositions.min?.get!
  let mut rawDoc ←
    go stx |>.run { anchorColumnPos, firstTokenPos := pos, lastTokenTailPos := tailPos }
  let isRawBlockSeparated := startColumnPos <= lineInfos[0]!.indentation
  let rawColumnPositions := anchorLineInfos.map (·.indentation)
  let areLinesAligned := isRawBlockSeparated || rawColumnPositions.all (· >= startColumnPos)
  if areLinesAligned then
    rawDoc := TaggedDoc.untagged <| .aligned rawDoc.doc
  else
    rawDoc := TaggedDoc.nested rawDoc
  rawDoc ← rawDoc.tag stx
  if isFallback then
    rawDoc := mkRawFallback rawDoc
  return rawDoc
where
  go (stx : Syntax) : ReaderT fmtRaw.Context FmtM TaggedDoc := do
    match stx with
    | .missing =>
      return failure
    | .atom _ val =>
      fmtToken stx val
    | .ident _ rawVal _ _ =>
      fmtToken stx rawVal.toString
    | .node _ kind args =>
      if kind == choiceKind then
        if let some firstAlternative := args[0]? then
          return ← go firstAlternative
      let docs ← args.mapM go
      return join docs
  fmtToken (stx : Syntax) (token : String) : ReaderT fmtRaw.Context FmtM TaggedDoc := do
    let ctx ← read
    let leadingDoc ← fmtLeadingWhitespace stx (fmtLeading ctx)
    let trailingDoc ← fmtTrailingWhitespace stx (fmtTrailing ctx)
    let valDocs := token.split "\n" |>.map (.text ·.toString) |>.toArray
    let valDoc :=
      if valDocs.size = 1 then
        valDocs[0]!
      else
        -- If the token contains a newline, we enforce that it renders exactly as-is
        -- in the source code.
        .unindented (onlyNonCumulative := false) <| .joinUsing .hardNl valDocs
    let doc ← TaggedDoc.taggedNode valDoc stx
    return leadingDoc ++ doc ++ trailingDoc
  fmtTrailing (ctx : fmtRaw.Context) (_trailingTk : Syntax) (trailing : Substring.Raw)
      : FmtM (Array (TaggedDoc × Option Syntax.Range)) := do
    let isFinalTrailing := trailing.startPos >= ctx.lastTokenTailPos
    if isFinalTrailing then
      return #[]
    let lines := trailing.splitOn "\n" |>.toArray
    let newLines :=
      #[lines[0]!.toString] ++ lines[1...*].toArray.map (·.toString.deindent ctx.anchorColumnPos)
    let formatted := newLines.map (Doc.text ·)
    return #[(TaggedDoc.untagged <| Doc.joinUsing .hardNl formatted, some <| .ofSubstring trailing)]
  fmtLeading (ctx : fmtRaw.Context) (_leadingTk : Syntax) (leading : Substring.Raw)
      : FmtM (Array (TaggedDoc × Option Syntax.Range)) := do
    let isInitialLeading := leading.stopPos <= ctx.firstTokenPos
    if isInitialLeading then
      return #[]
    let lines := leading.splitOn "\n" |>.toArray
    let newLines := lines.map (·.toString.deindent ctx.anchorColumnPos)
    let formatted := newLines.map (Doc.text ·)
    return #[(TaggedDoc.untagged <| Doc.joinUsing .hardNl formatted, some <| .ofSubstring leading)]

public partial def fmtWith (f : Fmt) (formatterName : Name) : Fmt := fun stx => do
  try
    let r ← f stx
    let r ← r.tag stx
    withShareCommon r
  catch e =>
    if let .internal .partialFormatter := e then
      let r ← fmtRaw (isFallback := true) stx
      if let some range := stx.getRange? then
        modify fun s => {
          s with
          partialFormatters := s.partialFormatters.insert range { stx, formatterName }
        }
      return r
    throw e

public partial def fmt : Fmt := fun stx =>
  match stx with
  | .missing =>
    pure <| failure
  | .atom _ val =>
    let valDocs := val.split "\n" |>.map (Doc.text ·.toString) |>.toArray
    let valDoc := .joinUsing .hardNl valDocs
    TaggedDoc.taggedText valDoc stx
  | .ident _ rawVal _ _ =>
    let valDocs := rawVal.toString.split "\n" |>.map (Doc.text ·.toString) |>.toArray
    let valDoc := .joinUsing .hardNl valDocs
    TaggedDoc.taggedText valDoc stx
  | .node .. => do
    let kind := stx.getKind
    let some (fName, f) ← getFormatterForKind? kind
      | let doc ← fmtRaw (isFallback := true) stx
        if let some range := stx.getRange? then
          modify fun s => { s with missingFormatters := s.missingFormatters.insert range { kind } }
        return doc
    fmtWith f fName stx

end

public def fmtAtomic : Fmt := fmtRaw (isFallback := false)

/-- Formats the alternatives of a choice node, which have no syntax node kind of their own. -/
def choiceNodeFmtProvider : FmtProvider := fun _ _ kind => do
  guard <| kind == choiceKind
  return (`Lean.Fmt.fmtChoiceNode, fmtChoiceNode)

/--
The syntax node kinds of antiquotations and antiquotation splices, as constructed by
`Lean.Parser.mkAntiquot`, `Lean.Parser.mkAntiquotSplice` and `Lean.Parser.tokenWithAntiquot`.
See also `Lean.Syntax.antiquotKind?`, `Lean.Syntax.antiquotSpliceKind?`,
`Lean.Syntax.antiquotSuffixSplice?` and `Lean.Syntax.isTokenAntiquot`.
-/
def isAntiquotKind : SyntaxNodeKind → Bool
  | .str _ "antiquot"
  | .str _ "antiquot_scope"
  | .str _ "antiquot_splice"
  | .str _ "antiquot_suffix_splice"
  | .str .anonymous "token_antiquot" =>
    true
  | _ =>
    false

/--
Formats antiquotations verbatim. Antiquotations occur outside of quotations in syntax that admits
them in its own grammar, such as `json% { key : $value }`.
-/
def antiquotFmtProvider : FmtProvider := fun _ _ kind => do
  guard <| isAntiquotKind kind
  return (`Lean.Fmt.fmtAtomic, fmtAtomic)

/--
Formats the operator notations whose associativity and fixity follow from their `ParserDescr`.
-/
def derivedOperatorFmtProvider : FmtProvider := fun env opts kind =>
  if let some op := getInfixOperationOfParserDescr? env opts kind then
    some (`Lean.Fmt.fmtInfixOperator, fmtInfixOperator op)
  else if hasPrefixFormatter env opts kind then
    some (`Lean.Fmt.fmtPrefixOperator, fmtPrefixOperator)
  else if hasPostfixFormatter env opts kind then
    some (`Lean.Fmt.fmtPostfixOperator, fmtPostfixOperator)
  else
    none

/-- Formats the syntax that consists exclusively of atoms according to its `ParserDescr`. -/
def derivedAtomicFmtProvider : FmtProvider := fun env opts kind => do
  guard <| hasAtomicFormatter env opts kind
  return (`Lean.Fmt.fmtAtomic, fmtAtomic)

/-- Whether `a` and `b` lie on the same line of `lineInfos`. -/
private def sameLine (lineInfos : Array SyntaxLineInfo) (a b : String.Pos.Raw) : Bool :=
  let lineIdx? (pos : String.Pos.Raw) :=
    binSearchRightmost lineInfos pos (·.startPos) (· < ·) |>.map (·.1)
  lineIdx? a == lineIdx? b

/--
Reassociates the comments that follow the operator of an infix operation.
`collectComments` attaches such a comment to the operator or to the token after it, which moves it
around with the operator when the operation is laid out differently. It is attached to the operand
that it shares its line with instead; a comment that shares its line with neither operand is placed
above the operator, where it ends up on a line of its own either way.
-/
def infixOperatorCommentCollector : CommentCollector := fun ctx stx => Id.run do
  if stx.getNumArgs != 3 then
    return #[]
  let (lhs, op, rhs) := (stx[0], stx[1], stx[2])
  if !op.isAtom then
    return #[]
  if (getInfixOperation? ctx.env ctx.opts stx.getKind).isNone then
    return #[]
  let comments := ctx.trailingComments op
  if comments.isEmpty then
    return #[]
  -- The operands are anchored at their last token, which is always tagged by the formatters,
  -- whereas an operand of an operator chain is not formatted as a node of its own.
  let (some lhsRange, some opRange, some rhsPos, some rhsRange) :=
      (lhs.getTailInfo.getRange?, op.getRange?, rhs.getPos?, rhs.getTailInfo.getRange?)
    | return #[]
  let opOnLhsLine := sameLine ctx.lineInfos lhsRange.stop opRange.start
  let opOnRhsLine := sameLine ctx.lineInfos opRange.stop rhsPos
  let mut r := #[]
  for c in comments do
    -- Only a comment before the first newline of the whitespace is on the operator's line.
    let commentOnOpLine := c.placement matches .afterToken
    if commentOnOpLine && opOnLhsLine && opOnRhsLine then
      -- `a + b`: the whole operation is on one line, so there is no other line to move to.
      continue
    if commentOnOpLine && opOnLhsLine then
      -- `a +` / `b`: the comment ends the line of the left operand.
      r := r.push (c, lhsRange)
    else if commentOnOpLine && opOnRhsLine then
      -- `a` / `+ b`: the comment lies within the line of the right operand.
      r := r.push (c, rhsRange)
    else
      -- The comment shares its line with neither operand, so it belongs above the operator rather
      -- than after it.
      r := r.push ({ c with placement := .onLineBeforeToken }, opRange)
  return r

builtin_initialize
  addBuiltinFmtProvider 1100 choiceNodeFmtProvider
  addBuiltinFmtProvider 1000 <| keyedFmtProvider fmtAttribute id
  addBuiltinFmtProvider 900 antiquotFmtProvider
  addBuiltinFmtProvider 800 <| keyedFmtProvider infixFmtAttribute fun op => fmtInfixOperator op
  addBuiltinFmtProvider 800 <| keyedFmtProvider conditionalFmtAttribute fmtConditional
  addBuiltinFmtProvider 800 <| keyedFmtProvider quantifierFmtAttribute fmtQuantifier
  addBuiltinFmtProvider 600 derivedOperatorFmtProvider
  addBuiltinFmtProvider 400 derivedAtomicFmtProvider

builtin_initialize addBuiltinCommentCollector 500 infixOperatorCommentCollector

public def fmt? (stx? : Option Syntax) : FmtM TaggedDoc := do
  let some stx := stx?
    | return empty
  fmt stx

public def fmtWith? (f : Fmt) (formatterName : Name) (stx? : Option Syntax) : FmtM TaggedDoc := do
  let some stx := stx?
    | return empty
  fmtWith f formatterName stx

public def fmtArray {ks : SyntaxNodeKinds} (array : TSyntaxArray ks) : FmtM (Array TaggedDoc) :=
  array.mapM fmt

public def fmtArrayWith
    {ks : SyntaxNodeKinds} (f : Fmt) (formatterName : Name) (array : TSyntaxArray ks)
    : FmtM (Array TaggedDoc) :=
  array.mapM (fmtWith f formatterName)

public def fmtSepArray (sepArray : Syntax.SepArray sep) : FmtM (TaggedDoc.SepArray sep) := do
  return ⟨← sepArray.elemsAndSeps.mapM fmt⟩

public def fmtSepArrayWith (f : Fmt) (formatterName : Name) (sepArray : Syntax.SepArray sep)
    : FmtM (TaggedDoc.SepArray sep) := do
  return ⟨← sepArray.elemsAndSeps.mapIdxM fun i d =>
    if i % 2 = 0 then
      fmtWith f formatterName d
    else
      fmt d⟩

public def fmtTSepArray (sepArray : Syntax.TSepArray ks sep) : FmtM (TaggedDoc.SepArray sep) := do
  return ⟨← sepArray.elemsAndSeps.mapM fmt⟩

public def fmtTSepArrayWith (f : Fmt) (formatterName : Name) (sepArray : Syntax.TSepArray ks sep)
    : FmtM (TaggedDoc.SepArray sep) := do
  return ⟨← sepArray.elemsAndSeps.mapIdxM fun i d =>
    if i % 2 = 0 then
      fmtWith f formatterName d
    else
      fmt d⟩

public def fmtLeadingWithRetainedNewlines (stx : Syntax) (minNewlines := 1) (maxNewlines := 2)
    : FmtM TaggedDoc := do
  fmtLeadingWhitespace stx fun leadingTk leading => do
    let some leading := leading.toSlice?
      | throw <| .elaboration <|
          .malformedInputSyntax leadingTk "substring is invalid and cannot be converted to a slice"
    let searcher := String.Slice.Pattern.ToForwardSearcher.toSearcher '\n' leading
    let numNewlines := searcher.filter (· matches .matched ..) |>.length
    let numNewlines := Nat.min (Nat.max numNewlines minNewlines) maxNewlines
    let nls := Array.replicate numNewlines hardNl
    return #[(join nls, none)]

public def fmtTrailingWithRetainedNewlines (stx : Syntax) (minNewlines := 1) (maxNewlines := 2)
    : FmtM TaggedDoc := do
  fmtTrailingWhitespace stx fun trailingTk trailing => do
    let some trailing := trailing.toSlice?
      | throw <| .elaboration <|
          .malformedInputSyntax trailingTk "substring is invalid and cannot be converted to a slice"
    let searcher := String.Slice.Pattern.ToForwardSearcher.toSearcher '\n' trailing
    let numNewlines := searcher.filter (· matches .matched ..) |>.length
    let numNewlines := Nat.min (Nat.max numNewlines minNewlines) maxNewlines
    let nls := Array.replicate numNewlines hardNl
    return #[(join nls, none)]

public def fmtArrayWithRetainedIntermediateNewlines (stxs : Array Syntax) : FmtM TaggedDoc := do
  if stxs.size = 1 then
    return ← fmt stxs[0]!
  let mut acc : Array TaggedDoc := #[]
  for h : i in (0...stxs.size) do
    let stx := stxs[i]
    let mut d ← fmt stx
    let trailingDoc ←
      if i < stxs.size - 1 then
        fmtTrailingWithRetainedNewlines stx
      else
        pure empty
    d := d ++ trailingDoc
    acc := acc.push d
  return join acc

def fmtCommentsWithRetainedNewlines
    (comments : Array Comment) (whitespace : String.Slice) (isLeading : Bool)
    : Array (TaggedDoc × Option Syntax.Range) × Bool := Id.run do
  let topLevelComments := comments.filter (! ·.placement matches .afterToken)
  let numNewlinesBeforeComments := countNewlinesBeforeComments topLevelComments whitespace
  let mut r := #[]
  let mut insertedAnyNewlines := false
  for h : i in (0...comments.size) do
    -- A block comment placed on its own line (unlike a line comment) does not include a trailing
    -- newline, so we must separate it from whatever follows it with at least one newline, even if
    -- the following comment or token was on the same line in the source (e.g. `/- c -/ def`).
    let prevIsBlockComment := i != 0 && comments[i - 1].kind matches .blockComment
    let numNewlines := numNewlinesBeforeComments.get? i |>.getD 0
    let numNewlines := if prevIsBlockComment then Nat.max numNewlines 1 else numNewlines
    let maxNumNewlines := if i == 0 || prevIsBlockComment then 2 else 1
    for _ in (0...Nat.min numNewlines maxNumNewlines) do
      r := r.push (hardNl, none)
      insertedAnyNewlines := true
    let c := comments[i]
    let alternatives :=
      c.render.map (·.rendered)
        |>.mapIdx fun i r =>
          let lines := r.split '\n' |>.map (.text ·.toString) |>.toArray
          TaggedDoc.untagged <| .joinUsing .hardNl lines
    let mut d := free <| oneOf alternatives
    if c.kind matches .lineComment then
      d := d ++ hardNl
      insertedAnyNewlines := true
    r := r.push (d, c.originalWhitespaceRange)
  let lastIsBlockComment :=
    comments.size != 0 && comments[comments.size - 1]!.kind matches .blockComment
  let finalNumNewlines := numNewlinesBeforeComments.get? comments.size |>.getD 0
  let finalNumNewlines :=
    if lastIsBlockComment then Nat.max finalNumNewlines 1 else finalNumNewlines
  let maxNumNewlines :=
    if isLeading then
      if comments.size > 0 then
        2
      else
        0
    else if comments.size == 0 || lastIsBlockComment then
      2
    else
      1
  for _ in (0...Nat.min finalNumNewlines maxNumNewlines) do
    r := r.push (hardNl, none)
    insertedAnyNewlines := true
  return (r, insertedAnyNewlines)
where
  countNewlinesBeforeComments (comments : Array Comment) (whitespace : String.Slice)
      : Std.HashMap Nat Nat := Id.run do
    let searcher := String.Slice.Pattern.ToForwardSearcher.toSearcher '\n' whitespace
    let newlinePositions :=
      searcher.filterMap (fun
        | .matched startPos _ => some startPos.str.offset
        | .rejected .. => none)
    let mut newlinesBeforeComment := {}
    let mut i := 0
    for newlinePosition in newlinePositions do
      -- Skip all comments that are strictly before `newlinePosition`.
      while true do
        let some c := comments[i]?
          | break
        if newlinePosition < c.originalWhitespaceRange.stop then
          break
        -- c.originalWhitespaceRange.stop <= newlinePosition
        i := i + 1
      -- The comment at `i` now either contains `newlinePosition` or `newlinePosition` is before it.
      if let some c := comments[i]? then
        if c.originalWhitespaceRange.contains newlinePosition then
          continue
      newlinesBeforeComment :=
        newlinesBeforeComment.alter i fun
          | none => some 1
          | some num => some <| num + 1
    return newlinesBeforeComment

public def fmtLeadingWithRetainedNewlinesAndComments (stx : Syntax) : FmtM TaggedDoc :=
  fmtLeadingWhitespace stx fun leadingTk leading => do
    let some leadingTkRange := leadingTk.getRange?
      | throw <| .elaboration <| .malformedInputSyntax leadingTk "missing token range"
    let some leading := leading.toSlice?
      | throw <| .elaboration <|
          .malformedInputSyntax leadingTk "substring is invalid and cannot be converted to a slice"
    let comments := parseComments (← read).lineInfos leadingTkRange .leading leading
    let (leadingDocs, _) := fmtCommentsWithRetainedNewlines comments leading (isLeading := true)
    return leadingDocs

public def fmtTrailingWithRetainedNewlinesAndComments
    (stx : Syntax) (atleastOneNewline : Bool := true)
    : FmtM TaggedDoc := do
  fmtTrailingWhitespace stx fun trailingTk trailing => do
    let some trailingTkRange := trailingTk.getRange?
      | throw <| .elaboration <| .malformedInputSyntax trailingTk "missing token range"
    let some trailing := trailing.toSlice?
      | throw <| .elaboration <|
          .malformedInputSyntax trailingTk "substring is invalid and cannot be converted to a slice"
    let comments := parseComments (← read).lineInfos trailingTkRange .trailing trailing
    let topLevelComments := comments.filter (! ·.placement matches .afterToken)
    let mut (trailingDocs, insertedAnyNewlines) :=
      fmtCommentsWithRetainedNewlines topLevelComments trailing (isLeading := false)
    if !insertedAnyNewlines && atleastOneNewline then
      trailingDocs := trailingDocs.push (hardNl, none)
    return trailingDocs

public def fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith (f : Fmt) (stxs : Array Syntax)
    : FmtM TaggedDoc := do
  if stxs.size = 1 then
    return ← f stxs[0]!
  let mut acc : Array TaggedDoc := #[]
  for h : i in (0...stxs.size) do
    let stx := stxs[i]
    let mut d ← f stx
    let trailingDoc ←
      if i < stxs.size - 1 then
        fmtTrailingWithRetainedNewlinesAndComments stx
      else
        pure empty
    d := d ++ trailingDoc
    acc := acc.push d
  return join acc

public def fmtArrayWithRetainedIntermediateNewlinesAndComments (stxs : Array Syntax)
    : FmtM TaggedDoc :=
  fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith fmt stxs

public inductive TrailingGroup (sep : String) where
  | group (g : SepArray sep)
  | trailing (t : TaggedDoc)
deriving Inhabited

public def fmtTSepArrayTrailingGroups (stxs : Syntax.TSepArray ks sep)
    : FmtM (Array (TrailingGroup sep)) := do
  let elemsAndSeps := stxs.elemsAndSeps
  let mut acc : Array (TrailingGroup sep) := #[]
  let mut pendingGroup : SepArray sep := ⟨#[]⟩
  for h : i in (0...elemsAndSeps.size) do
    let stx := elemsAndSeps[i]
    pendingGroup := ⟨pendingGroup.elemsAndSeps.push (← fmt stx)⟩
    let isSep := i % 2 != 0
    if i < elemsAndSeps.size - 1 && isSep then
      let trailingAnchorStx :=
        if stx.matchesNull 0 then
          elemsAndSeps[i - 1]!
        else
          stx
      let trailingDoc ←
        fmtTrailingWithRetainedNewlinesAndComments trailingAnchorStx (atleastOneNewline := false)
      if !trailingDoc.isAlwaysEmpty then
        acc := acc.push <| .group pendingGroup
        acc := acc.push <| .trailing trailingDoc
        pendingGroup := ⟨#[]⟩
  if !pendingGroup.elemsAndSeps.isEmpty then
    acc := acc.push <| .group pendingGroup
  return acc

public def fmtTSepArrayWithRetainedIntermediateNewlinesAndComments (stxs : Syntax.TSepArray ks sep)
    : FmtM TaggedDoc := do
  let groups ← fmtTSepArrayTrailingGroups stxs
  let groups :=
    groups.map fun
      | .group g => Layouts.sepArray g <| .fillUsingSpacedSep none .retainTrailingSep
      | .trailing t => t
  return join groups
