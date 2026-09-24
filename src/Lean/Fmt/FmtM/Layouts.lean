/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Primitives
import Init.Data
import Init.While
import Std.Data.Iterators.Producers.Range
import Std.Data.Iterators.Combinators.StepSize

namespace Lean.Fmt.Layouts

section General

public inductive Types.ArrayFormat where
  | join
  | joinUsingSpace
  | joinUsingSoftSpace
  | joinUsingNl (allowFlattening : Bool)
  | joinUsingBreak
  | fill

public def array (array : Array TaggedDoc) (format : Types.ArrayFormat) : TaggedDoc := Id.run do
  let array := array.filter (!·.isAlwaysEmpty)
  if array.isEmpty then
    return empty
  if array.size = 1 then
    return array[0]!
  match format with
  | .join =>
    let terms := array.map (.withSepAfter · empty)
    combine terms
  | .joinUsingSpace =>
    let terms := array.map (.withSepAfter · space)
    combine terms
  | .joinUsingSoftSpace =>
    let terms := array.map (.withSepAfter · softSpace)
    combine terms
  | .joinUsingNl allowFlattening =>
    if allowFlattening then
      let terms := array.map (.withSepAfter · nl)
      maybeFlattened <| combine terms
    else
      let terms := array.map (.withSepAfter · hardNl)
      combine terms
  | .joinUsingBreak =>
    let terms := array.map (.withSepAfter · «break»)
    maybeFlattened <| combine terms
  | .fill =>
    fillUsingSpace array

public def lines (lines : Array TaggedDoc) : TaggedDoc :=
  array lines <| .joinUsingNl (allowFlattening := false)

public def spacedLines (lines : Array TaggedDoc) : TaggedDoc :=
  let lines := lines.map (.withSepAfter · (hardNl ++ hardNl))
  combine lines

public def atomic (terms : Array TaggedDoc) : TaggedDoc := array terms .join

public def atomicInfixOperator (terms : Array TaggedDoc) : TaggedDoc := Id.run do
  let terms := terms.filter (!·.isAlwaysEmpty)
  if terms.size = 1 then
    return terms[0]!
  return nested <| atomic terms

public def spacedAtomic (terms : Array TaggedDoc) : TaggedDoc := array terms .joinUsingSpace

public def softSpacedAtomic (terms : Array TaggedDoc) : TaggedDoc := array terms .joinUsingSoftSpace

public def fill (terms : Array TaggedDoc) : TaggedDoc := array terms .fill

public def horizontalOrVertical (terms : Array TaggedDoc) (spacing : Bool := true) : TaggedDoc :=
  if spacing then
    array terms <| .joinUsingNl (allowFlattening := true)
  else
    array terms .joinUsingBreak

public inductive Types.SepArrayFormat.TrailingSep where
  | includeTrailingSep
  | excludeTrailingSep
  | retainTrailingSep

public inductive Types.SepArrayFormat
  | joinUsingSep
    (afterElem? afterSep? : Option TaggedDoc)
    (trailingSep : SepArrayFormat.TrailingSep := .excludeTrailingSep)
  | joinUsingNl
    (allowFlattening : Bool)
    (afterElem? : Option TaggedDoc := none)
    (trailingSep : SepArrayFormat.TrailingSep := .excludeTrailingSep)
  | fillUsingSep
    (afterElem? afterSep? : Option TaggedDoc)
    (trailingSep : SepArrayFormat.TrailingSep := .excludeTrailingSep)
  | fillUsingSpacedSep
    (afterElem? : Option TaggedDoc)
    (trailingSep : SepArrayFormat.TrailingSep := .excludeTrailingSep)

public def Types.SepArrayFormat.trailingSep
    : Types.SepArrayFormat → Types.SepArrayFormat.TrailingSep
  | .joinUsingSep (trailingSep := trailingSep) .. => trailingSep
  | .joinUsingNl (trailingSep := trailingSep) .. => trailingSep
  | .fillUsingSep (trailingSep := trailingSep) .. => trailingSep
  | .fillUsingSpacedSep (trailingSep := trailingSep) .. => trailingSep

public def sepArray (sepArray : SepArray sep) (format : Types.SepArrayFormat)
    : TaggedDoc := Id.run do
  let sepArray := normalize sepArray format.trailingSep
  if sepArray.elemsAndSeps.isEmpty then
    return empty
  if sepArray.elemsAndSeps.size = 1 then
    return sepArray.elemsAndSeps[0]!
  match format with
  | .joinUsingSep afterElem? afterSep? _ =>
    joinUsingSep sepArray afterElem? afterSep?
  | .joinUsingNl allowFlattening afterElem? _ =>
    let joinedUsingNl := joinUsingNl sepArray afterElem?
    if allowFlattening then
      oneOf #[
        flattened <| joinUsingSep sepArray afterElem? (afterSep? := space),
        joinedUsingNl
      ]
    else
      joinedUsingNl
  | .fillUsingSep afterElem? afterSep? _ =>
    fillUsingSep sepArray afterElem? afterSep?
  | .fillUsingSpacedSep afterElem? _ =>
    fillUsingSpacedSep sepArray afterElem?

where

  normalize (sepArray : SepArray sep) (trailingSep : Types.SepArrayFormat.TrailingSep)
      : SepArray sep := Id.run do
    let sepArray := sepArray.elemsAndSeps
    let mut r := #[]
    for i in (0...sepArray.size).iter.stepSize 2 do
      let elem := sepArray[i]!
      if elem.isAlwaysEmpty then
        continue
      r := r.push elem
      if trailingSep matches .retainTrailingSep && i == sepArray.size - 1 then
        break
      let sep' := sepArray[i + 1]?.getD empty
      let sep' :=
        if sep'.isAlwaysEmpty then
          untagged (.text sep)
        else
          sep'
      r := r.push sep'
    if trailingSep matches .excludeTrailingSep && r.size % 2 == 0 then
      r := r.pop
    return ⟨r⟩

  joinUsingSep (sepArray : SepArray sep) (afterElem? afterSep? : Option TaggedDoc) : TaggedDoc :=
    let docs :=
      sepArray.elemsAndSeps.mapIdx fun i doc => Id.run do
        if i == sepArray.elemsAndSeps.size - 1 then
          return doc
        let isElem := i % 2 == 0
        let afterDoc? :=
          if isElem then
            afterElem?
          else
            afterSep?
        let doc :=
          if isElem || !doc.isAlwaysEmpty then
            doc
          else
            untagged (.text sep)
        let some afterDoc := afterDoc?
          | return doc
        return doc ++ afterDoc
    join docs

  joinUsingNl (sepArray : SepArray sep) (afterElem? : Option TaggedDoc) : TaggedDoc := Id.run do
    let mut (elems, _) := split sepArray
    if let some afterElem := afterElem? then
      elems :=
        elems.mapIdx fun i elem =>
          if i == elems.size - 1 then
            elem
          else
            elem ++ afterElem
    return joinUsing hardNl elems

  fillUsingSep (sepArray : SepArray sep) (afterElem? afterSep? : Option TaggedDoc) : TaggedDoc :=
    let afterElem := afterElem?.getD empty
    let afterSep := afterSep?.getD empty
    let (elems, seps) := splitAttachingTrailingSep sepArray afterElem
    fillWith elems fun i =>
      let sep := join #[afterElem, seps[i]!, afterSep]
      { flat := sep, broken := sep }

  fillUsingSpacedSep (sepArray : SepArray sep) (afterElem? : Option TaggedDoc) : TaggedDoc :=
    let afterElem := afterElem?.getD empty
    let (elems, seps) := splitAttachingTrailingSep sepArray afterElem
    fillWith elems fun i =>
      let sep := join #[afterElem, seps[i]!]
      { flat := join #[sep, space], broken := sep }

  /-- Like `split`, but appends a trailing separator to the last element. -/
  splitAttachingTrailingSep (sepArray : SepArray sep) (afterElem : TaggedDoc)
      : Array TaggedDoc × Array TaggedDoc := Id.run do
    let mut (elems, seps) := split sepArray
    if !seps.isEmpty && seps.size == elems.size then
      elems := elems.modify (elems.size - 1) fun lastElem => join #[lastElem, afterElem, seps.back!]
      seps := seps.pop
    return (elems, seps)

  split (sepArray : SepArray sep) : Array TaggedDoc × Array TaggedDoc := Id.run do
    let mut elems := #[]
    let mut seps := #[]
    for h : i in (0...sepArray.elemsAndSeps.size) do
      let doc := sepArray.elemsAndSeps[i]
      if i % 2 == 0 then
        elems := elems.push doc
      else
        let doc :=
          if !doc.isAlwaysEmpty then
            doc
          else
            untagged (.text sep)
        seps := seps.push doc
    return (elems, seps)

public def sepLines (lines : SepArray sep) (includeSeps : Bool) : TaggedDoc :=
  if includeSeps then
    sepArray lines <| .joinUsingSep none hardNl
  else
    sepArray lines <| .joinUsingNl (allowFlattening := false)

public def sepFill (elems : SepArray sep) : TaggedDoc := sepArray elems <| .fillUsingSpacedSep none

public def sepHorizontalOrVertical (elems : SepArray sep) (includeSeps : Bool)
    : TaggedDoc := Id.run do
  let elems := sepArray.normalize elems .excludeTrailingSep
  if elems.elemsAndSeps.size = 1 then
    return elems.elemsAndSeps[0]!
  if includeSeps then
    return maybeFlattened <| sepArray elems <| .joinUsingSep none nl
  else
    return sepArray elems <| .joinUsingNl (allowFlattening := true)

end General

section Lean

public def retainedWhitespace (docsWithIntermediateWhitespace : Array TaggedDoc)
    : TaggedDoc := Id.run do
  if docsWithIntermediateWhitespace.isEmpty then
    return empty
  if docsWithIntermediateWhitespace.size = 1 then
    return docsWithIntermediateWhitespace[0]!
  let mut components := #[]
  let mut i := 0
  while i < docsWithIntermediateWhitespace.size do
    let doc := docsWithIntermediateWhitespace[i]!
    let trailing? := docsWithIntermediateWhitespace[i + 1]? |>.getD empty
    components := components.push (.withSepAfter doc trailing?)
    i := i + 2
  return combine components

partial def isAligned [BEq τ] [Hashable τ] (v : Doc τ) : Bool := goMemoized v |>.run' {}
where
  goMemoized (v : Doc τ) : StateM (Std.HashMap (PtrKey (Doc τ)) Bool) Bool := do
    let cacheKey := unsafe PtrKey.ofKey v
    if let some isAligned := (← get).get? cacheKey then
      return isAligned
    let isAligned ← go v
    modify fun s => s.insert cacheKey isAligned
    return isAligned
  go : Doc τ → StateM (Std.HashMap (PtrKey (Doc τ)) Bool) Bool
    | .aligned _ =>
      return true
    | .tagged _ d
    | .flattened d
    | .unflattenable d
    | .indented _ _ d
    | .unindented _ d
    | .final d
    | .initial d
    | .free d
    | .guarded _ d
    | .costing _ d =>
      goMemoized d
    | .either a b =>
      return (← goMemoized a) && (← goMemoized b)
    | .failure | .text _ | .newline _ | .append _ _ =>
      return false

public inductive Types.PrefixOperatorFormat where
  | withoutSpacing
  | withoutSpacingIfAtomic
  | withSpacing

public def prefixOperator
    (prefixOperatorTk operand : TaggedDoc) (format : Types.PrefixOperatorFormat)
    : TaggedDoc := Id.run do
  if prefixOperatorTk.isAlwaysEmpty then
    return operand
  let mut doc :=
    if format matches .withoutSpacing
      || format matches .withoutSpacingIfAtomic && (operand.isAtomic || operand.isSelfDelimited)
        && !operand.isRawFallback
    then
      nested <| atomic #[prefixOperatorTk, operand]
    else
      nested <| spacedAtomic #[prefixOperatorTk, operand]
  if isAligned operand.doc then
    doc := pseudoAligned doc
  return doc

public inductive Types.PostfixOperatorFormat where
  | withoutSpacing
  | withSpacing

public def postfixOperator
    (operand postfixOperatorTk : TaggedDoc) (format : Types.PostfixOperatorFormat)
    : TaggedDoc := Id.run do
  if postfixOperatorTk.isAlwaysEmpty then
    return operand
  if format matches .withSpacing then
    return nested <| spacedAtomic #[operand, postfixOperatorTk]
  else
    return nested <| atomic #[operand, postfixOperatorTk]

public inductive Types.InfixOperatorFormat
  | dense
    (hardNestedFirstOperand := true) (trailingOperator : Bool := false) (spacing := true)
    (respectPseudoAlignment := true)
  | sparse
    (hardNestedFirstOperand := true) (trailingOperator : Bool := false) (spacing := true)
    (alignedOperators : Bool := false) (separateFinalOperand : Bool := false)

public def Types.InfixOperatorFormat.hardNestedFirstOperand : Types.InfixOperatorFormat → Bool
  | .dense hardNestedFirstOperand _ _ _ => hardNestedFirstOperand
  | .sparse hardNestedFirstOperand _ _ _ _ => hardNestedFirstOperand

public def Types.InfixOperatorFormat.trailingOperator : Types.InfixOperatorFormat → Bool
  | .dense _ trailingOperator _ _ => trailingOperator
  | .sparse _ trailingOperator _ _ _ => trailingOperator

public def Types.InfixOperatorFormat.spacing : Types.InfixOperatorFormat → Bool
  | .dense _ _ spacing _ => spacing
  | .sparse _ _ spacing _ _ => spacing

public def Types.InfixOperatorFormat.alignedOperators : Types.InfixOperatorFormat → Bool
  | .dense _ _ _ _ => false
  | .sparse _ trailingOperator _ alignedOperators _ => !trailingOperator && alignedOperators

public def Types.InfixOperatorFormat.separateFinalOperand : Types.InfixOperatorFormat → Bool
  | .dense _ _ _ _ => false
  | .sparse _ trailingOperator _ _ separateFinalOperand => !trailingOperator && separateFinalOperand

public def Types.InfixOperatorFormat.respectPseudoAlignment : Types.InfixOperatorFormat → Bool
  | .dense _ _ _ respectPseudoAlignment => respectPseudoAlignment
  | .sparse _ _ _ _ _ => true

public def permitDenseLayout (doc : TaggedDoc) (respectPseudoAlignment : Bool) : Bool :=
  if respectPseudoAlignment then
    !doc.isPseudoAligned && ! isAligned doc.doc
  else
    ! isAligned doc.doc

public def infixOperator (chain : Array TaggedDoc) (format : Types.InfixOperatorFormat := .sparse)
    : TaggedDoc := Id.run do
  let (chain, isHeadless, isTailless) := normalize chain
  if chain.isEmpty then
    return empty
  let mut combinedChain := combineChain chain isHeadless
  if combinedChain.size = 1 then
    return combinedChain[0]!
  if !format.trailingOperator && format.hardNestedFirstOperand then
    combinedChain := combinedChain.modify 0 hardNested
  else if format.trailingOperator && format.hardNestedFirstOperand then
    combinedChain :=
      combinedChain.mapIdx fun i link =>
        if i < combinedChain.size - 1 then
          hardNested link
        else
          link
  let mut doc :=
    if !format.trailingOperator then
      fill combinedChain
    else
      fillWrapping combinedChain nested
  if !isHeadless && !format.trailingOperator then
    doc :=
      oneOf #[
        compactFirstOperation combinedChain,
        doc
      ]
  let lastOperand := chain[chain.size - 1]!
  if let some doc' :=
    addStickyAlt? doc lastOperand isTailless combinedChain #[.coequal, .preferSticky]
  then
    doc := doc'
  else if let some doc' := addDenseAlt? doc lastOperand isTailless combinedChain then
    doc := doc'
  else if let some doc' := addStickyAlt? doc lastOperand isTailless combinedChain #[.preferUnsticky]
  then
    doc := doc'
  if !format.trailingOperator then
    doc := pseudoAligned doc
  return nested doc
where
  addStickyAlt?
      (doc : TaggedDoc) (lastOperand : TaggedDoc) (isTailless : Bool)
      (combinedChain : Array TaggedDoc) (eligibleKinds : Array StickynessKind)
      : Option TaggedDoc := do
    guard <| format.trailingOperator
    guard <| !isTailless
    let stickynessKind ← getStickynessKind? lastOperand
    guard <| eligibleKinds.contains stickynessKind
    let lastOperandSticky := getSticky? lastOperand |>.get!
    let stickyCombinedChain :=
      combinedChain.set! (combinedChain.size - 1) lastOperandSticky.stickyVariant
    let stickyDoc :=
      combineFlat #[
        flattened (combineFlat stickyCombinedChain.pop),
        stickyCombinedChain.back!
      ]
    return withStickyAlt doc stickyDoc (.ofSticky lastOperandSticky)
  addDenseAlt?
      (doc : TaggedDoc) (lastOperand : TaggedDoc) (isTailless : Bool)
      (combinedChain : Array TaggedDoc)
      : Option TaggedDoc := do
    guard <| format matches .dense ..
    guard <| !isTailless
    guard <| format.trailingOperator || combinedChain.size = 2
    guard <| permitDenseLayout lastOperand format.respectPseudoAlignment
    return fallbackOnHeight doc <| combineFlat #[
      flattened (combineFlat combinedChain.pop),
      combinedChain.back!
    ]
  normalize (chain : Array TaggedDoc) : Array TaggedDoc × Bool × Bool := Id.run do
    let chainSizeBeforeSuffixTrim := chain.size
    let chain := chain.popWhile (·.isAlwaysEmpty)
    let isTailless := (chainSizeBeforeSuffixTrim - chain.size) % 2 != 0
    let chainSizeBeforePrefixTrim := chain.size
    let chain := chain.reverse.popWhile (·.isAlwaysEmpty) |>.reverse
    let isHeadless := (chainSizeBeforePrefixTrim - chain.size) % 2 != 0
    if chain.isEmpty then
      return (#[], false, false)
    if !format.trailingOperator then
      let mut normalized := if isHeadless then #[] else #[chain[0]!]
      let mut i := if isHeadless then 0 else 1
      while i < chain.size do
        let operator := chain[i]!
        let some operand := chain[i + 1]?
          | normalized := normalized.push operator
            break
        if !operand.isAlwaysEmpty then
          normalized := normalized.push operator
          normalized := normalized.push operand
        i := i + 2
      return (normalized, isHeadless, isTailless)
    else
      let mut normalized := if isHeadless then #[chain[0]!] else #[]
      let mut i := if isHeadless then 1 else 0
      while i < chain.size do
        let operand := chain[i]!
        let some operator := chain[i + 1]?
          | normalized := normalized.push operand
            break
        if !operand.isAlwaysEmpty then
          normalized := normalized.push operand
          normalized := normalized.push operator
        i := i + 2
      return (normalized, isHeadless, isTailless)
  combineChain (chain : Array TaggedDoc) (isHeadless : Bool) : Array TaggedDoc := Id.run do
    if !format.trailingOperator then
      let mut combinedChain := if isHeadless then #[] else #[chain[0]!]
      let mut i := if isHeadless then 0 else 1
      while i < chain.size do
        let operator := chain[i]!
        let operand := chain[i + 1]?.getD empty
        let combined := combineFlat #[operator, nested operand]
        combinedChain := combinedChain.push combined
        i := i + 2
      return combinedChain
    else
      let mut combinedChain := if isHeadless then #[chain[0]!] else #[]
      let mut i := if isHeadless then 1 else 0
      while i < chain.size do
        let operand := chain[i]!
        let operator := chain[i + 1]?.getD empty
        let combined := combineFlat #[nested operand, operator]
        combinedChain := combinedChain.push combined
        i := i + 2
      return combinedChain
  compactFirstOperation (combinedChain : Array TaggedDoc) : TaggedDoc :=
    let firstOperand := combinedChain[0]!
    let secondOperand :=
      if format.hardNestedFirstOperand && combinedChain.size > 2 then
        hardNested combinedChain[1]!
      else
        combinedChain[1]!
    let compactFirstOperation :=
      combineFlat #[
        firstOperand,
        guarded compactFirstOperationAssertion secondOperand
      ]
    let compactedChain := #[compactFirstOperation] ++ combinedChain[2...*]
    fill compactedChain
  compactFirstOperationAssertion : Assertion := {
    id := `Lean.Fmt.Layouts.infixOperator.compactFirstOperationAssertion
    assertion columnPos indentation nonCumulativeIndentation :=
      columnPos <= indentation + nonCumulativeIndentation
  }
  combineFlat (docs : Array TaggedDoc) : TaggedDoc :=
    if format.spacing then
      Layouts.spacedAtomic docs
    else
      Layouts.atomic docs
  fill (docs : Array TaggedDoc) : TaggedDoc :=
    if format.alignedOperators then
      Layouts.lines docs
    else if format.separateFinalOperand then
      if format.spacing then
        Layouts.horizontalOrVertical #[fillUsingSpace docs[0...docs.size - 1], docs[docs.size - 1]!]
      else
        Layouts.horizontalOrVertical (spacing := false)
          #[TaggedDoc.fill docs[0...docs.size - 1], docs[docs.size - 1]!]
    else if format.spacing then
      fillUsingSpace docs
    else
      TaggedDoc.fill docs
  fillWrapping (docs : Array TaggedDoc) (wrap : TaggedDoc → TaggedDoc) : TaggedDoc :=
    if format.spacing then
      fillUsingSpaceWrapping docs wrap
    else
      TaggedDoc.fillWrapping docs wrap

public def typeAscription
    (lhs typeAscriptionTk rhs : TaggedDoc) (format : Types.InfixOperatorFormat := .dense)
    : TaggedDoc :=
  infixOperator (format := format) #[lhs, typeAscriptionTk, rhs]

public inductive Types.BracketFormat where
  | dense (spacing := false)
  | sparse
    (sep : TaggedDoc)
    (unindentedRb : Bool := true) (stickynessKind : StickynessKind := .preferSticky)

public def bracketed
    (lb : TaggedDoc) (body : TaggedDoc) (rb : TaggedDoc) (format : Types.BracketFormat)
    : TaggedDoc := Id.run do
  if body.isAlwaysEmpty then
    return atomic #[lb, rb]
  let isBodyAligned := isAligned body.doc
  let isBodyPseudoAligned := isPseudoAligned body
  match format with
  | .dense spacing =>
    if spacing then
      return spacedAtomic #[lb, nested body, rb]
    let f := fun body => Id.run do
      let mut doc := atomic #[lb, nested body, rb]
      if isBodyAligned then
        doc := aligned doc
      else if isBodyPseudoAligned then
        doc := pseudoAligned doc
      doc := mkSelfDelimited (isBracketed := true) doc
      return doc
    return propagateStickyness body f (kind? := some .preferUnsticky)
  | .sparse sep unindentedRb preferStickyVariant =>
    let body := aligned body
    let mut sparse := lb ++ hardNested (sep ++ body) ++ sep ++ rb
    if unindentedRb then
      sparse := unindented (onlyNonCumulative := true) sparse
    -- The less indented variant dominates, so the closing bracket is rendered at the minimum of the
    -- indentation and the column of the opening bracket, never to the right of the opening bracket.
    let stickyVariant :=
      mkSelfDelimited (isBracketed := true) <| oneOf #[
        sparse,
        aligned sparse
      ]
    let nonStickyVariant := maybeFlattened stickyVariant
    return sticky nonStickyVariant stickyVariant preferStickyVariant

public def parens (lbTk : TaggedDoc) (body : TaggedDoc) (rbTk : TaggedDoc) : TaggedDoc :=
  Layouts.bracketed lbTk body rbTk .dense

public def parenthesizedSeq (lbTk : TaggedDoc) (seq : TaggedDoc) (rbTk : TaggedDoc) : TaggedDoc :=
  Layouts.bracketed lbTk seq rbTk <| .sparse «break»

public structure Types.Alt where
  flat : TaggedDoc
  nonFlat : TaggedDoc

public def alt (subAlts : Array TaggedDoc) (arrowTk rhs : TaggedDoc) (isComplex : Bool := false)
    : Types.Alt := Id.run do
  if arrowTk.isAlwaysEmpty && rhs.isAlwaysEmpty then
    let subAlts := combineSubAlts subAlts
    return ⟨flattened subAlts, subAlts⟩
  let subAlts := subAlts.map nested
  let subAlts := subAlts.modify (subAlts.size - 1) hardNested
  let lhs := Layouts.spacedAtomic #[combineSubAlts subAlts, arrowTk]
  let nonStickyDoc := combine #[.withSepAfter lhs ⟨nl, nested⟩, rhs]
  let flat := flattened nonStickyDoc
  let some stickyRhs := getSticky? rhs
    | return ⟨flat, nonStickyDoc⟩
  let stickyDoc := combine #[.withSepAfter lhs ⟨space, nested⟩, stickyRhs.stickyVariant]
  return ⟨
    flat,
    withStickyAlt nonStickyDoc stickyDoc (.ofSticky stickyRhs (allowFlattening := false))
  ⟩
where
  combineSubAlts (subAlts : Array TaggedDoc) : TaggedDoc :=
    if isComplex then
      Layouts.lines subAlts
    else
      Layouts.horizontalOrVertical subAlts

public def alts (alts : Array Types.Alt) (allowFlattenedAlts : Bool := true) : TaggedDoc :=
  let unflattened := Layouts.lines <| alts.map (·.nonFlat)
  if !allowFlattenedAlts then
    withPosition <| unflattened
  else
    let flattened := Layouts.lines <| alts.map (·.flat)
    withPosition <| oneOf #[flattened, unflattened]

public inductive Types.KeywordPrefixedSeqFormat where
  | sticky
  | nonSticky

public def keywordPrefixedSeq
    (keywordTk : TaggedDoc) (seq : TaggedDoc) (format : Types.KeywordPrefixedSeqFormat)
    : TaggedDoc :=
  let doc := stickyCombine keywordTk ⟨nl, nested⟩ seq
  if format matches .sticky then
    sticky (maybeFlattened doc) doc .preferSticky
  else
    maybeFlattened doc

public inductive Types.KeywordPrefixedTermFormat where
  | sticky
  | nonSticky

public def keywordPrefixedTerm
    (keyword : TaggedDoc) (term : TaggedDoc) (format : Types.KeywordPrefixedTermFormat := .sticky)
    : TaggedDoc := Id.run do
  if term.isAlwaysEmpty then
    if keyword.isAlwaysEmpty then
      return empty
    match format with
    | .sticky => return sticky keyword (flattened keyword) .coequal
    | .nonSticky => return keyword
  let nonStickyDoc :=
    if permitDenseLayout term (respectPseudoAlignment := false) then
      stickyCombine (hardNested keyword) ⟨space, nested⟩ term
    else
      maybeFlattened <| stickyCombine (hardNested keyword) ⟨nl, nested⟩ term
  match format with
  | .sticky =>
    let (stickyDoc, kind) :=
      if let some stickyTerm := getSticky? term then
        if stickyTerm.kind matches .preferSticky then
          (combine #[.withSepAfter (flattened keyword) ⟨nl, nested⟩, term], .preferSticky)
        else
          (stickyCombine (flattened keyword) ⟨nl, nested⟩ term, stickyTerm.kind)
      else
        (stickyCombine (flattened keyword) ⟨nl, nested⟩ term, .coequal)
    return sticky nonStickyDoc stickyDoc kind
  | .nonSticky =>
    return nonStickyDoc

public inductive Types.KeywordPrefixedAltsFormat where
  | sticky
  | nonSticky

public def keywordPrefixedAlts
    (keyword : TaggedDoc) (alts : Array Layouts.Types.Alt)
    (format : Types.KeywordPrefixedTermFormat := .sticky)
    : TaggedDoc :=
  let alts := Layouts.alts alts
  let nonStickyDoc := Layouts.lines #[keyword, alts]
  match format with
  | .sticky =>
    let stickyDoc := Layouts.lines #[flattened keyword, alts]
    sticky nonStickyDoc stickyDoc .coequal
  | .nonSticky =>
    nonStickyDoc

public inductive Types.KeywordPrefixedSepArrayFormat where
  | sticky (sepArrayFormat : Types.SepArrayFormat)
  | nonSticky (sepArrayFormat : Types.SepArrayFormat)

public def Types.KeywordPrefixedSepArrayFormat.isSticky : Types.KeywordPrefixedSepArrayFormat → Bool
  | .sticky .. => true
  | .nonSticky .. => false

public def Types.KeywordPrefixedSepArrayFormat.sepArrayFormat
    : Types.KeywordPrefixedSepArrayFormat → Types.SepArrayFormat
  | .sticky sepArrayFormat => sepArrayFormat
  | .nonSticky sepArrayFormat => sepArrayFormat

public def keywordPrefixedSepArray
    (keyword : TaggedDoc) (sepArray : SepArray sep) (format : Types.KeywordPrefixedSepArrayFormat)
    : TaggedDoc := Id.run do
  let sepArray := Layouts.sepArray.normalize sepArray format.sepArrayFormat.trailingSep
  if sepArray.elemsAndSeps.size = 1 then
    let format := if format.isSticky then .sticky else .nonSticky
    return keywordPrefixedTerm keyword sepArray.elemsAndSeps[0]! format
  let sepArrayFirstElemFlattened : SepArray sep := ⟨sepArray.elemsAndSeps.modify 0 flattened⟩
  let nonStickyDoc :=
    oneOf #[
      combine #[
        .withSepAfter (hardNested keyword) ⟨space, nested⟩,
        (Layouts.sepArray sepArrayFirstElemFlattened format.sepArrayFormat)
      ],
      combine #[
        .withSepAfter (hardNested keyword) ⟨hardNl, nested⟩,
        (Layouts.sepArray sepArray format.sepArrayFormat)
      ]
    ]
  if format.isSticky then
    let stickyDoc :=
      combine #[
        .withSepAfter (flattened keyword) ⟨nl, nested⟩,
        Layouts.sepArray sepArray format.sepArrayFormat
      ]
    return sticky nonStickyDoc stickyDoc .coequal
  return nonStickyDoc

public inductive Types.KeywordPrefixedSepFillFormat where
  | sticky
  | nonSticky

public def keywordPrefixedSepFill
    (keyword : TaggedDoc) (sepArray : SepArray sep) (format : Types.KeywordPrefixedSepFillFormat)
    : TaggedDoc :=
  let sepArrayFormat := .fillUsingSpacedSep none
  let format :=
    match format with
    | .sticky => .sticky sepArrayFormat
    | .nonSticky => .nonSticky sepArrayFormat
  keywordPrefixedSepArray keyword sepArray format

public structure Types.KeywordSeparatedFormat where
  allowFlattening : Bool := true
  nestedRhs : Bool := true

public def keywordSeparated
    (lhs : TaggedDoc) (keywordTk : TaggedDoc) (rhs : TaggedDoc)
    (format : Types.KeywordSeparatedFormat := {})
    : TaggedDoc := Id.run do
  if keywordTk.isAlwaysEmpty then
    return maybeFlattened <| attachRhs lhs
  let trailingKeywordLhs := flattened <| Layouts.spacedAtomic #[lhs, keywordTk]
  let leadingKeywordRhs := maybeFlattened <| attachRhs keywordTk
  return maybeFlattened <| oneOf #[
    attachRhs trailingKeywordLhs,
    combine #[.withSepAfter lhs sep, leadingKeywordRhs]
  ]
where
  attachRhs (lhs : TaggedDoc) : TaggedDoc :=
    if format.allowFlattening then
      stickyCombine lhs ⟨sep, wrap⟩ rhs
    else
      combine #[.withSepAfter lhs ⟨sep, wrap⟩, rhs]
  sep :=
    if format.allowFlattening then
      nl
    else
      hardNl
  wrap :=
    if format.nestedRhs then
      nested
    else
      id

public structure Types.ApplicationFormat where
  hardNestedFirstTerm : Bool := true
  sparse : Bool := false
  parenthesize : Bool
  respectPseudoAlignment : Bool

public def applicationWithSomeFilled
    (terms : Array (Fillable TaggedDoc)) (format : Types.ApplicationFormat)
    : TaggedDoc := Id.run do
  let mut fillableTerms := terms.filter (!·.v.isAlwaysEmpty)
  if fillableTerms.isEmpty then
    return empty
  if fillableTerms.size = 1 then
    return fillableTerms[0]!.v
  if fillableTerms.size > 1 && format.hardNestedFirstTerm then
    fillableTerms := fillableTerms.modify 0 fun f => { f with v := hardNested f.v }
  if format.parenthesize then
    let lbTk := untagged <| .text "("
    let rbTk := untagged <| .text ")"
    for i in (1...fillableTerms.size - 1) do
      let arg := fillableTerms[i]!
      if needsAppBrackets arg.v then
        fillableTerms := fillableTerms.set! i { arg with v := Layouts.parens lbTk arg.v rbTk }
  let mut app := fillSomeUsingSpace fillableTerms
  let terms := fillableTerms.map (·.1)
  if let some app' := addStickyAlt? app fillableTerms terms #[.coequal, .preferSticky] then
    app := app'
  else if let some app' := addDenseAlt? app terms then
    app := app'
  else if let some app' := addStickyAlt? app fillableTerms terms #[.preferUnsticky] then
    app := app'
  return maybeFlattened <| nested app
where
  addStickyAlt?
      (app : TaggedDoc) (fillableTerms : Array (Fillable TaggedDoc)) (terms : Array TaggedDoc)
      (eligibleKinds : Array StickynessKind)
      : Option TaggedDoc := do
    guard <| fillableTerms.back!.allowFill
    let stickynessKind ← terms.back!.getStickynessKind?
    guard <| eligibleKinds.contains stickynessKind
    let lastTermSticky := getSticky? terms.back! |>.get!
    let stickyTerms := terms.set! (terms.size - 1) lastTermSticky.stickyVariant
    return withStickyAlt app (dense stickyTerms) (.ofSticky lastTermSticky)
  addDenseAlt? (app : TaggedDoc) (terms : Array TaggedDoc) : Option TaggedDoc := do
    guard <| !format.sparse && terms.size == 2
    guard <| permitDenseLayout terms.back! format.respectPseudoAlignment
    return oneOf #[dense terms, app]
  dense (terms : Array TaggedDoc) : TaggedDoc :=
    combine #[
      flattened (joinUsing space terms.pop),
      .withSepBefore terms.back! space
    ]

public def application
    (terms : Array TaggedDoc)
    (format : Types.ApplicationFormat := { parenthesize := true, respectPseudoAlignment := true })
    : TaggedDoc :=
  applicationWithSomeFilled (format := format) <|
    terms.map fun term => ({ v := term, allowFill := true })

public structure Types.PseudoApplicationFormat where
  hardNestedFirstTerm : Bool := true
  sparse : Bool := false
  parenthesize : Bool := false
  respectPseudoAlignment : Bool := false

public def Types.PseudoApplicationFormat.toApplicationFormat (f : Types.PseudoApplicationFormat)
    : Types.ApplicationFormat where
  hardNestedFirstTerm : Bool := f.hardNestedFirstTerm
  sparse : Bool := f.sparse
  parenthesize : Bool := f.parenthesize
  respectPseudoAlignment : Bool := f.respectPseudoAlignment

public def pseudoApplication
    (terms : Array TaggedDoc) (format : Types.PseudoApplicationFormat := {})
    : TaggedDoc :=
  application terms format.toApplicationFormat

public inductive metaApplication.Term where
  | sep (doc : TaggedDoc)
  | elems (docs : Array TaggedDoc)

public def metaApplication.Term.ofSepArray {s : String} (elems : SepArray s)
    : Array metaApplication.Term :=
  elems.elemsAndSeps.mapIdx fun i doc => if i % 2 == 0 then .elems #[doc] else .sep doc

public def metaApplication (lb : TaggedDoc) (terms : Array metaApplication.Term) (rb : TaggedDoc)
    : TaggedDoc := Id.run do
  let mut terms := terms
  terms :=
    terms.map fun
      | .sep s => .sep s
      | .elems docs => .elems <| docs.filter (!·.isAlwaysEmpty)
  let firstElemsIdx? :=
    terms.findIdx? fun
      | .sep _ => false
      | .elems es => !es.isEmpty
  if terms.size > 1 then
    if let some firstElemsIdx := firstElemsIdx? then
      terms :=
        terms.modify firstElemsIdx fun
          | .sep s => .sep s
          | .elems es => .elems <| es.modify 0 hardNested
  let terms' : SepArray "," :=
    ⟨terms.map fun
      | .sep s => s
      | .elems elems => Layouts.fill elems⟩
  let terms' := Layouts.sepFill terms'
  Layouts.bracketed lb terms' rb .dense

public def pipeOperator (chain : Array TaggedDoc) : TaggedDoc :=
  Layouts.infixOperator chain (format := .dense (trailingOperator := true))

public structure Types.Block where
  block : TaggedDoc
  hardNestedIfFirst : Bool := true
deriving Inhabited

public instance : Coe TaggedDoc Types.Block where
  coe block := { block }

public structure Types.BlocksFormat where
  nested : Bool := true

public def blocks (blocks : Array Types.Block) (format : Types.BlocksFormat := {})
    : TaggedDoc := Id.run do
  let mut blocks := blocks.filter (!·.block.isAlwaysEmpty)
  if blocks.isEmpty then
    return empty
  let { block := initialBlock, hardNestedIfFirst := initialBlockHardNested } := blocks[0]!
  if blocks.size = 1 then
    return initialBlock
  let mut acc :=
    if initialBlockHardNested then
      hardNested initialBlock
    else
      initialBlock
  for i in (1...blocks.size) do
    let { block, hardNestedIfFirst } := blocks[i]!
    let nonStickyAcc := maybeFlattened <| combine #[.withSepAfter acc nl, block]
    let some sticky := getSticky? block
      | acc := nonStickyAcc
        continue
    let mut stickyAcc := combine #[.withSepAfter (flattened acc) space, sticky.stickyVariant]
    if hardNestedIfFirst && i < blocks.size - 1 then
      stickyAcc := hardNested stickyAcc
    acc := withStickyAlt nonStickyAcc stickyAcc (.ofSticky sticky)
  if format.nested then
    acc := nested acc
  return acc

public def tuple (lb : TaggedDoc) (fields : SepArray sep) (rb : TaggedDoc) : TaggedDoc := Id.run do
  let fields := Layouts.sepArray.normalize fields .excludeTrailingSep
  if fields.elemsAndSeps.size = 1 then
    return Layouts.bracketed lb fields.elemsAndSeps[0]! rb .dense
  let fields := Layouts.sepArray fields <| .joinUsingSep none nl
  return Layouts.bracketed lb fields rb <| .sparse «break» (stickynessKind := .coequal)

public structure Types.ArrayLitFormat where
  spacing : Bool := false
  unindentedRb : Bool := true

public def collection
    (lb : TaggedDoc) (elems : SepArray sep) (rb : TaggedDoc)
    (format : Types.ArrayLitFormat := {}) :=
  let elems := Layouts.sepArray.normalize elems .excludeTrailingSep
  let sep :=
    if format.spacing then
      nl
    else
      «break»
  let fields := Layouts.sepFill elems
  Layouts.bracketed lb fields rb <|
    .sparse sep format.unindentedRb (stickynessKind := .preferSticky)

public def keywordPrefixedCollection
    (keyword : TaggedDoc) (lb : TaggedDoc) (elems : SepArray sep) (rb : TaggedDoc)
    (format : Types.ArrayLitFormat := {})
    : TaggedDoc :=
  let collection := Layouts.collection lb elems rb format
  propagateStickyness collection fun collection =>
    nested <| Layouts.spacedAtomic #[keyword, collection]

public inductive Types.SignatureKind where
  | local (respectPseudoAlignment : Bool := true)
  | global

private def signature
    (lvals : Array TaggedDoc) (binderGroups : Array (Array (Array TaggedDoc)))
    (typeAscriptionTk : TaggedDoc) (type : TaggedDoc) (kind : Types.SignatureKind)
    (lvalsLayout : Array TaggedDoc → TaggedDoc := Layouts.horizontalOrVertical)
    : TaggedDoc :=
  -- For a clear separation of a token preceding the list of binders and the type,
  -- `lval` should be present so that when the list of binders needs to be split across multiple
  -- lines or there are no binders and the type needs to be split across multiple lines,
  -- the list of binders and the type are separated from the token before the binders and the types
  -- by a newline.
  -- For example, if `foobar` precedes the list of binders but there is no `lval`, we could get the
  -- following rendering if `(foo : bar)` needs to be split:
  -- ```
  -- foobar (foo
  --   : bar)
  --   : barfoo
  -- ```
  -- or the following rendering:
  -- ```
  -- foobar : foo
  --   bar
  -- ```
  -- In most cases, this kind of rendering is visually unpleasant
  -- (and so `lval` should be non-empty), though there are rare exceptions.
  -- E.g. if unnamed instance binders `[<type>]` are understood as a signature with an empty `lval`,
  -- empty `binders` and a non-empty `type?`, the following rendering is arguably totally fine:
  -- ```
  -- [foo
  --   bar]
  -- ```
  let lvals := lvals.filter (!·.isAlwaysEmpty)
  let binderGroups :=
    binderGroups.filterMap fun group => do
      let group :=
        group.filterMap fun subGroup => do
          let subGroup := subGroup.filter (!·.isAlwaysEmpty)
          guard <| !subGroup.isEmpty
          return subGroup
      guard <| !group.isEmpty
      return group
  let lvals :=
    if lvals.size <= 1 && type.isAlwaysEmpty && typeAscriptionTk.isAlwaysEmpty
      && binderGroups.isEmpty
    then
      lvals
    else
      lvals.modify 0 hardNested
  let format :=
    match kind with
    | .local respectPseudoAlignment =>
      .dense (hardNestedFirstOperand := false) (respectPseudoAlignment := respectPseudoAlignment)
    | .global =>
      .sparse (hardNestedFirstOperand := false)
  let binderGroups :=
    Layouts.horizontalOrVertical <| binderGroups.map (fillUsingSpaceWithSoftBoundaries ·)
  nested <| Layouts.typeAscription (format := format)
    (Layouts.horizontalOrVertical <| #[(lvalsLayout lvals), binderGroups]) typeAscriptionTk type

public def localSignature
    (lvals : Array TaggedDoc) (binderGroups : Array (Array (Array TaggedDoc)))
    (typeAscriptionTk : TaggedDoc) (type : TaggedDoc)
    : TaggedDoc :=
  signature lvals binderGroups typeAscriptionTk type .local

public def globalSignature
    (lvals : Array TaggedDoc) (binderGroups : Array (Array (Array TaggedDoc)))
    (typeAscriptionTk : TaggedDoc) (type : TaggedDoc)
    : TaggedDoc :=
  signature lvals binderGroups typeAscriptionTk type .global

public def assignmentDeclaration
    (signature : TaggedDoc) (separationTk : TaggedDoc) (body : TaggedDoc) (sticky : Bool := false)
    : TaggedDoc :=
  let doc :=
    maybeFlattened <|
      if separationTk.isAlwaysEmpty && body.isAlwaysEmpty then
        signature
      else
        let lhs :=
          combine #[
            .withSepAfter (hardNested signature) space,
            separationTk
          ]
        stickyCombine lhs ⟨nl, nested⟩ body
  if sticky then
    let (stickyVariant, kind) :=
      let lhs :=
        combine #[
          .withSepAfter (flattened signature) space,
          separationTk
        ]
      if let some stickyBody := getSticky? body then (
        stickyCombine lhs ⟨nl, nested⟩ body
          (allowFlattening := !(stickyBody.kind matches .preferSticky)),
        stickyBody.kind
      )
      else
        (stickyCombine lhs ⟨nl, nested⟩ body, .coequal)
    TaggedDoc.sticky doc stickyVariant kind
  else
    doc

public def matchDeclaration (signature : TaggedDoc) (matchAlts : TaggedDoc) : TaggedDoc :=
  combine #[
    .withSepAfter (hardNested signature) ⟨hardNl, nested⟩,
    matchAlts
  ]

public def whereDeclaration (signature : TaggedDoc) (whereTk : TaggedDoc) (body : TaggedDoc)
    : TaggedDoc := Id.run do
  if body.isAlwaysEmpty then
    return Layouts.spacedAtomic #[signature, whereTk]
  let lhs := Layouts.spacedAtomic #[(hardNested signature), whereTk]
  return maybeFlattened <| stickyCombine lhs ⟨hardNl, nested⟩ body

public def binder
    (lbs : Array TaggedDoc) (lhses : Array TaggedDoc)
    (subBinderGroups : Array (Array (Array TaggedDoc))) (typeAscriptionTk? : TaggedDoc)
    (type? : TaggedDoc) (colonEqTk? : TaggedDoc) (default? : TaggedDoc) (rbs : Array TaggedDoc)
    (kind : Types.SignatureKind := .local (respectPseudoAlignment := false))
    : TaggedDoc :=
  let lbs := atomic lbs
  let binderSignature :=
    Layouts.signature lhses subBinderGroups typeAscriptionTk? type? kind Layouts.fill
  let simpleBinder := assignmentDeclaration binderSignature colonEqTk? default?
  let rbs := atomic rbs
  parens lbs simpleBinder rbs

public structure Types.LetTermFormat where
  separateSignatureAndDecl : Bool := false

public def letDecl
    (keywordTk : TaggedDoc) (config : TaggedDoc) (decl : TaggedDoc)
    (format : Types.LetTermFormat := {})
    : TaggedDoc :=
  let signature := Layouts.pseudoApplication #[keywordTk, config]
  let signatureSep :=
    if format.separateSignatureAndDecl then
      nl
    else
      space
  nested <| maybeFlattened <| combine #[
    .withSepAfter signature signatureSep,
    decl
  ]

public structure Types.QuantifierHead where
  quantifier : TaggedDoc
  binderGroups : Array (Array (Array TaggedDoc))
  typeAscriptionTk? : TaggedDoc
  type? : TaggedDoc
  separationTk : TaggedDoc

public def quantified (quantifierHeads : Array Types.QuantifierHead) (body : TaggedDoc)
    : TaggedDoc := Id.run do
  if quantifierHeads.isEmpty then
    return body
  let quantifierHeads :=
    quantifierHeads.map fun qh =>
      let signature := Layouts.localSignature #[] qh.binderGroups qh.typeAscriptionTk? qh.type?
      Layouts.prefixOperator qh.quantifier (Layouts.atomic #[signature, qh.separationTk])
        .withSpacing
  let quantifierHeads := quantifierHeads.map (⟨hardNested ·, true⟩)
  let components := quantifierHeads.push ⟨body, false⟩
  let quantifiers := fillSomeUsingSpaceWrapping components nested
  return pseudoAligned <| maybeFlattened quantifiers

public def subtype (lbTk lhs sepTk rhs rbTk : TaggedDoc) (format : Types.BracketFormat)
    : TaggedDoc :=
  let body :=
    pseudoAligned <|
      Layouts.infixOperator #[lhs, sepTk, rhs] (format := .dense (respectPseudoAlignment := false))
  Layouts.bracketed lbTk body rbTk format

public structure Types.ElseIf where
  elseTk : TaggedDoc
  ifTk : TaggedDoc
  cond : TaggedDoc
  thenTk : TaggedDoc
  thenBlock : TaggedDoc

public def conditional
    (ifTk cond thenTk thenBlock : TaggedDoc) (elseIfs : Array Types.ElseIf)
    (elseTk elseBlock : TaggedDoc) (allowFlattening : Bool)
    : TaggedDoc :=
  let elseIfs :=
    elseIfs.filter fun elseIf =>
      !(elseIf.elseTk.isAlwaysEmpty && elseIf.ifTk.isAlwaysEmpty && elseIf.cond.isAlwaysEmpty
        && elseIf.thenTk.isAlwaysEmpty && elseIf.thenBlock.isAlwaysEmpty)
  let allowFlattening := allowFlattening && elseIfs.isEmpty
  let elseIfs := #[⟨empty, ifTk, cond, thenTk, thenBlock⟩] ++ elseIfs
  if allowFlattening then
    oneOf #[
      flattened <| mk elseIfs elseTk elseBlock (allowFlattening := true),
      mk elseIfs elseTk elseBlock (allowFlattening := false)
    ]
  else
    unflattenable <| mk elseIfs elseTk elseBlock (allowFlattening := false)
where
  attachBlockToToken (tk block : TaggedDoc) (allowFlattening : Bool) : TaggedDoc :=
    stickyCombine tk ⟨nl, nested⟩ block allowFlattening

  mk (elseIfs : Array Types.ElseIf) (elseTk elseBlock : TaggedDoc) (allowFlattening : Bool)
      : TaggedDoc :=
    let elseIfs :=
      elseIfs.map fun ⟨elseTk, ifTk, cond, thenTk, thenBlock⟩ =>
        let tk := Layouts.spacedAtomic #[elseTk, ifTk]
        let head := Layouts.pseudoApplication #[tk, cond]
        let «then» := attachBlockToToken thenTk thenBlock allowFlattening
        let trailingThen :=
          combine #[
            .withSepAfter (flattened head) space,
            «then»
          ]
        let leadingThen :=
          combine #[
            .withSepAfter head nl,
            «then»
          ]
        oneOf #[trailingThen, leadingThen]
    let «else» := attachBlockToToken elseTk elseBlock allowFlattening
    let blocks := elseIfs.push «else»
    let blocks := blocks.map fun block => .withSepAfter (some block) nl
    let conditional := combine blocks
    aligned conditional

public def strLit («prefix» str : TaggedDoc) : TaggedDoc :=
  mkSelfDelimited <| Layouts.atomic #[«prefix», str]

end Lean
