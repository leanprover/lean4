/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Attribute
import Init.Data.Range.Polymorphic.Iterators

namespace Lean.Fmt
namespace TaggedDoc

public def untagged (doc : Fmt.Doc FmtCost) : TaggedDoc := { doc }

public def taggedWithRange
    (freshTagId : TagId) (tags : Std.HashMap Syntax.Range (Array TagId × RangeKind))
    (doc : Fmt.Doc FmtCost) (range : Syntax.Range) (kind : RangeKind)
    : TagId × Std.HashMap Syntax.Range (Array TagId × RangeKind) × TaggedDoc :=
  let doc := { doc := .tagged freshTagId doc }
  let tags :=
    tags.alter range fun
      | none => some (#[freshTagId], kind)
      | some (tags, kind) => some <| (tags.push freshTagId, kind)
  let freshTagId : TagId := freshTagId + 1
  (freshTagId, tags, doc)

public def taggedText (doc : Fmt.Doc FmtCost) (ref : Syntax) : FmtM TaggedDoc := do
  let some range := ref.getRange?
    | return { doc }
  modifyGet fun s =>
    let (freshTagId, tags, doc) := taggedWithRange s.freshTagId s.tags doc range .text
    (doc, { s with freshTagId, tags })

public def taggedNode (doc : Fmt.Doc FmtCost) (ref : Syntax) : FmtM TaggedDoc := do
  let some range := ref.getRange?
    | return { doc }
  modifyGet fun s =>
    let (freshTagId, tags, doc) := taggedWithRange s.freshTagId s.tags doc range .node
    (doc, { s with freshTagId, tags })

public def taggedWhitespace (doc : Fmt.Doc FmtCost) (range : Syntax.Range) : FmtM TaggedDoc := do
  modifyGet fun s =>
    let (freshTagId, tags, doc) := taggedWithRange s.freshTagId s.tags doc range .whitespace
    (doc, { s with freshTagId, tags })

public def isTagged (d : TaggedDoc) : Bool := d.doc matches .tagged ..

public def tag (d : TaggedDoc) (ref : Syntax) : FmtM TaggedDoc := do
  if d.isTagged then
    return d
  return { ← taggedNode d.doc ref with metaData := d.metaData }

public def getMetaData? (α) [TypeName α] (d : TaggedDoc) : Option α :=
  d.metaData.findSome? (·.v.get? α)

public def addMetaData
    [Inhabited α] [TypeName α]
    (d : TaggedDoc) (metaData : α) (propagate : α → (Doc FmtCost → Doc FmtCost) → α)
    : TaggedDoc := {
  d with
  metaData := { v := Dynamic.mk metaData, propagate := propagateDynamic } :: d.metaData
}
where
  propagateDynamic (v : Dynamic) (f : Doc FmtCost → Doc FmtCost) : Dynamic :=
    let v := v.get? α |>.get!
    let r := propagate v f
    Dynamic.mk r

public def propagateMetaData (d : TaggedDoc) (f : Doc FmtCost → Doc FmtCost) : TaggedDoc where
  doc := f d.doc
  metaData := d.metaData.map fun { v, propagate } => { v := propagate v f, propagate }
public def propagateArrayMetaData (ds : Array TaggedDoc) (f : Array (Doc FmtCost) → Doc FmtCost)
    : TaggedDoc :=
  if ds.size = 1 then
    ds[0]!
  else
    untagged <| f <| ds.map (·.doc)

public def failure : TaggedDoc := untagged .failure
public def newline (flattened : String) : TaggedDoc := untagged (.newline flattened)
public def nl : TaggedDoc := untagged .nl
public def «break» : TaggedDoc := untagged .break
public def hardNl : TaggedDoc := untagged .hardNl
public def text (s : String) (ref : Syntax) : FmtM TaggedDoc := taggedText (.text s) ref
public def empty : TaggedDoc := untagged .empty
public def space : TaggedDoc := untagged (.text " ")
public def nested (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.nested
public def hardNested (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.hardNested
public def doublyNested (d : TaggedDoc) : TaggedDoc := hardNested <| nested d
public def aligned (d : TaggedDoc) : TaggedDoc :=
  -- We deliberately do not propagate meta-data here.
  -- Propagating stickiness through `aligned` can result in unintuitive alignments.
  untagged <| .aligned d.doc
public def unflattenable (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.unflattenable
public def flattened (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.flattened
public def maybeFlattened (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.maybeFlattened
public def unindented (d : TaggedDoc) (onlyNonCumulative : Bool) : TaggedDoc :=
  propagateMetaData d (Doc.unindented onlyNonCumulative)
public def final (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.final
public def initial (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.initial
public def free (d : TaggedDoc) : TaggedDoc := propagateMetaData d Doc.free
public def guarded (p : Assertion) (d : TaggedDoc) : TaggedDoc :=
  propagateMetaData d (Doc.guarded p)
public def withFailureFallbackPenalty (d : TaggedDoc) (amount : Nat := 1) : TaggedDoc :=
  propagateMetaData d (Doc.costing (DefaultCost.ofFailureFallbackPenalty amount))
public def withOverflowFallbackPenalty (d : TaggedDoc) (amount : Nat := 1) : TaggedDoc :=
  propagateMetaData d (Doc.costing (DefaultCost.ofOverflowFallbackPenalty amount))
public def withHeightFallbackPenalty (d : TaggedDoc) (amount : Nat := 1) : TaggedDoc :=
  propagateMetaData d (Doc.costing (DefaultCost.ofHeightFallbackPenalty amount))
public def either (a b : TaggedDoc) : TaggedDoc := untagged <| .either a.doc b.doc
public def oneOf (ds : Array TaggedDoc) : TaggedDoc := propagateArrayMetaData ds (.oneOf ·)
public def fallbackOnFailure (d fallback : TaggedDoc) : TaggedDoc :=
  oneOf #[d, withFailureFallbackPenalty fallback]
public def fallbackOnOverflow (d fallback : TaggedDoc) : TaggedDoc :=
  oneOf #[d, withOverflowFallbackPenalty fallback]
public def fallbackOnHeight (d fallback : TaggedDoc) : TaggedDoc :=
  oneOf #[d, withHeightFallbackPenalty fallback]
public def softSpace : TaggedDoc := fallbackOnFailure space hardNl
public def append (a b : TaggedDoc) : TaggedDoc := untagged <| .append a.doc b.doc
public def join (ds : Array TaggedDoc) : TaggedDoc := propagateArrayMetaData ds (.join ·)
public def joinUsing (sep : TaggedDoc) (ds : Array TaggedDoc) : TaggedDoc :=
  propagateArrayMetaData ds (.joinUsing sep.doc ·)
public def fillWith (ds : Array TaggedDoc) (sep : Nat → FillSep TaggedDoc) : TaggedDoc :=
  propagateArrayMetaData ds
    (.fillWith · fun i =>
      let { flat, broken } := sep i
      { flat := flat.doc, broken := broken.doc })
public def fill (ds : Array TaggedDoc) : TaggedDoc := propagateArrayMetaData ds (.fill ·)
public def fillWrapping (ds : Array TaggedDoc) (wrap : TaggedDoc → TaggedDoc) : TaggedDoc :=
  -- `wrap` is only ever applied to untagged internal documents created by `fillWrapping`,
  -- so it is safe to lift it to `Doc`.
  propagateArrayMetaData ds (.fillWrapping · fun d => wrap (untagged d) |>.doc)
public def fillUsingSpace (ds : Array TaggedDoc) : TaggedDoc :=
  propagateArrayMetaData ds (.fillUsingSpace ·)
public def fillUsingSpaceWrapping (ds : Array TaggedDoc) (wrap : TaggedDoc → TaggedDoc)
    : TaggedDoc :=
  -- `wrap` is only ever applied to untagged internal documents created by `fillUsingSpaceWrapping`,
  -- so it is safe to lift it to `Doc`.
  propagateArrayMetaData ds (.fillUsingSpaceWrapping · fun d => wrap (untagged d) |>.doc)

/--
Fills all documents of all groups like `TaggedDoc.fillUsingSpace` does. In addition, the formatter
can place a newline between two adjacent groups. It only does so if the newline does not increase
the amount of lines.
-/
public def fillUsingSpaceWithSoftBoundaries (dss : Array (Array TaggedDoc)) : TaggedDoc := Id.run do
  let ds := dss.flatten
  if ds.size = 1 then
    return ds[0]!
  return untagged <| .fillUsingSpaceWithSoftBoundaries (DefaultCost.ofHeightFallbackPenalty 1) <|
    dss.map (·.map (·.doc))

public def fillSomeUsingSpace (ds : Array (Fillable TaggedDoc)) : TaggedDoc := Id.run do
  if ds.size == 1 then
    return ds[0]!.v
  return untagged <| .fillSomeUsingSpace <|
    ds.map fun { v, allowFill } => { v := v.doc, allowFill := allowFill }
public def fillSomeUsingSpaceWrapping
    (ds : Array (Fillable TaggedDoc)) (wrap : TaggedDoc → TaggedDoc)
    : TaggedDoc := Id.run do
  if ds.size == 1 then
    return ds[0]!.v
  let ds : Array (Fillable (Fmt.Doc FmtCost)) :=
    ds.map fun { v, allowFill } => { v := v.doc, allowFill := allowFill }
  -- `wrap` is only ever applied to untagged internal documents created by
  -- `fillSomeUsingSpaceWrapping`, so it is safe to lift it to `Doc`.
  return untagged <| .fillSomeUsingSpaceWrapping ds fun d => wrap (untagged d) |>.doc

public def isAlwaysEmpty (d : TaggedDoc) : Bool := d.doc.isAlwaysEmpty
public def isAlwaysNonEmpty (d : TaggedDoc) : Bool := d.doc.isAlwaysNonEmpty
public def isCompoundAtomic (d : TaggedDoc) : Bool := d.doc.isCompoundAtomic
public def isAtomic (d : TaggedDoc) : Bool := d.doc.isAtomic

public instance : Append TaggedDoc where
  append a b :=
    if a.isAlwaysEmpty then
      b
    else if b.isAlwaysEmpty then
      a
    else
      untagged <| a.doc ++ b.doc

public inductive StickynessKind where
  | coequal
  | preferSticky
  | preferUnsticky
deriving Inhabited, BEq

public structure Sticky where
  stickyVariant : TaggedDoc
  kind : StickynessKind
deriving Inhabited, TypeName

public def sticky (nonStickyVariant : TaggedDoc) (stickyVariant : TaggedDoc) (kind : StickynessKind)
    : TaggedDoc :=
  nonStickyVariant.addMetaData (Sticky.mk stickyVariant kind) fun v f => {
    stickyVariant := propagateMetaData v.stickyVariant f
    kind := v.kind
  }

public def getSticky? (doc : TaggedDoc) : Option Sticky := doc.getMetaData? Sticky

public def getStickynessKind? (doc : TaggedDoc) : Option StickynessKind :=
  getSticky? doc |>.map (·.kind)

public def propagateStickyness
    (inner : TaggedDoc) (f : TaggedDoc → TaggedDoc) (kind? : Option StickynessKind := none)
    : TaggedDoc := Id.run do
  let nonStickyOuter := f inner
  let some stickyInner := getSticky? inner
    | return nonStickyOuter
  let stickyOuter := f stickyInner.stickyVariant
  let kind := kind?.getD stickyInner.kind
  return sticky nonStickyOuter stickyOuter kind

public inductive withStickyAlt.Config where
  | coequal
  | preferUnsticky
  | preferSticky (allowFlattening : Bool := true)

public def withStickyAlt.Config.ofSticky (s : Sticky) (allowFlattening : Bool := true)
    : withStickyAlt.Config :=
  match s.kind with
  | .coequal => .coequal
  | .preferSticky => .preferSticky allowFlattening
  | .preferUnsticky => .preferUnsticky

public def withStickyAlt (doc stickyDoc : TaggedDoc) (cfg : withStickyAlt.Config) : TaggedDoc :=
  match cfg with
  | .coequal =>
    oneOf #[
      unflattenable stickyDoc,
      doc
    ]
  | .preferUnsticky =>
    oneOf #[
      doc,
      withHeightFallbackPenalty (unflattenable stickyDoc)
    ]
  | .preferSticky (allowFlattening := true) =>
    oneOf #[
      unflattenable stickyDoc,
      flattened doc,
      withOverflowFallbackPenalty doc
    ]
  | .preferSticky (allowFlattening := false) =>
    oneOf #[
      unflattenable stickyDoc,
      withOverflowFallbackPenalty doc
    ]

public structure Sep where
  s : TaggedDoc
  wrap : TaggedDoc → TaggedDoc := id

public instance : Coe TaggedDoc Sep where
  coe s := { s }

public structure Component where
  sepBefore? : Option Sep := none
  doc? : Option TaggedDoc
  sepAfter? : Option Sep := none

public instance : Coe (Option TaggedDoc) Component where
  coe doc? := { doc? }

public def Component.withSepBefore (doc? : Option TaggedDoc) (sepBefore : Sep) : Component where
  sepBefore? := some sepBefore
  doc?

public def Component.withSepAfter (doc? : Option TaggedDoc) (sepAfter : Sep) : Component where
  doc?
  sepAfter? := some sepAfter

public def combine (cs : Array Component) : TaggedDoc := Id.run do
  let entries := filterEmptyDocs cs
  if entries.isEmpty then
    return empty
  if let #[(_, doc, _)] := entries then
    return doc
  let entries := normalizeSeps entries

  let mut combined := empty
  for (sepBefore?, doc) in entries.reverse do
    let some sepBefore := sepBefore?
      | combined := doc ++ combined
        continue
    let separatedDoc := sepBefore.s ++ doc
    combined := separatedDoc ++ combined
    combined := sepBefore.wrap combined

  return combined
where
  filterEmptyDocs (cs : Array Component) : Array (Option Sep × TaggedDoc × Option Sep) :=
    cs.filterMap fun c => do
      let d ← c.doc?
      guard <| !d.isAlwaysEmpty
      return (c.sepBefore?, d, c.sepAfter?)
  normalizeSeps (entries : Array (Option Sep × TaggedDoc × Option Sep))
      : Array (Option Sep × TaggedDoc) := Id.run do
    let mut entries := entries
    entries := entries.modify 0 fun (_, doc, sepAfter?) => (none, doc, sepAfter?)
    entries := entries.modify (entries.size - 1) fun (sepBefore?, doc, _) => (sepBefore?, doc, none)
    -- Collapse adjacent seps
    for i in (0...entries.size - 1) do
      let (_, _, some _currSepAfter) := entries[i]!
        | continue
      let (some _nextSepBefore, _, _) := entries[i + 1]!
        | continue
      entries :=
        entries.modify i fun (currSepBefore?, currDoc, _) => (currSepBefore?, currDoc, none)
    -- Move seps after a document to before the next document
    for i in (0...entries.size - 1) do
      let (_, _, some currSepAfter) := entries[i]!
        | continue
      entries :=
        entries.modify (i + 1) fun (_, nextDoc, nextSepAfter?) =>
          (currSepAfter, nextDoc, nextSepAfter?)
    return entries.map fun (sepBefore?, doc, _) => (sepBefore?, doc)

public def stickyCombine
    (lhs : TaggedDoc) (sep : Sep) (rhs : TaggedDoc) (allowFlattening : Bool := true)
    : TaggedDoc := Id.run do
  let nonStickyDoc := combine #[.withSepAfter lhs sep, rhs]
  let some stickyRhs := getSticky? rhs
    | return nonStickyDoc
  let stickySep := { sep with s := space }
  let stickyDoc := combine #[.withSepAfter lhs stickySep, stickyRhs.stickyVariant]
  return withStickyAlt nonStickyDoc stickyDoc (.ofSticky stickyRhs allowFlattening)

public def withPosition (body : TaggedDoc) : TaggedDoc := aligned body

public structure SepArray (sep : String) where
  elemsAndSeps : Array TaggedDoc

public def SepArray.mapElems (a : SepArray sep) (f : TaggedDoc → TaggedDoc) : SepArray sep :=
  ⟨a.elemsAndSeps.mapIdx fun i sepOrElem =>
    if i % 2 = 0 then
      f sepOrElem
    else
      sepOrElem⟩

public def SepArray.pushElem (a : SepArray sep) (elem : TaggedDoc) : SepArray sep :=
  if a.elemsAndSeps.size % 2 == 0 then
    ⟨a.elemsAndSeps.push elem⟩
  else
    ⟨a.elemsAndSeps ++ #[untagged <| .text sep, elem]⟩

public def SepArray.numElems (a : SepArray sep) : Nat := a.elemsAndSeps.size / 2

public instance : Coe (Array TaggedDoc) (SepArray sep) where
  coe docs := ⟨docs⟩

public instance : CoeOut (SepArray sep) (Array TaggedDoc) where
  coe docs := docs.elemsAndSeps

public structure SelfDelimited where
  isBracketed : Bool
deriving Inhabited, TypeName

public def mkSelfDelimited (doc : TaggedDoc) (isBracketed : Bool := false) : TaggedDoc :=
  doc.addMetaData (SelfDelimited.mk isBracketed) fun v _ => v

public def isSelfDelimited (doc : TaggedDoc) : Bool := doc.getMetaData? SelfDelimited |>.isSome

public def isBracketed (doc : TaggedDoc) : Bool :=
  doc.getMetaData? SelfDelimited |>.any (·.isBracketed)

public structure RawFallback
deriving Inhabited, TypeName

public def mkRawFallback (doc : TaggedDoc) : TaggedDoc :=
  doc.addMetaData RawFallback.mk fun v _ => v

public def isRawFallback (doc : TaggedDoc) : Bool := doc.getMetaData? RawFallback |>.isSome

public structure PseudoAligned
deriving Inhabited, TypeName

public def pseudoAligned (doc : TaggedDoc) : TaggedDoc :=
  doc.addMetaData PseudoAligned.mk fun v _ => v

public def isPseudoAligned (doc : TaggedDoc) : Bool := doc.getMetaData? PseudoAligned |>.isSome

public def needsAppBrackets (doc : TaggedDoc) : Bool :=
  doc.isRawFallback || !doc.isCompoundAtomic && !doc.isSelfDelimited

public structure PseudoDedented where
  dedentedVariant : TaggedDoc
deriving Inhabited, TypeName

public def pseudoDedented (indentedVariant dedentedVariant : TaggedDoc) : TaggedDoc :=
  indentedVariant.addMetaData (PseudoDedented.mk dedentedVariant) fun v f => {
    dedentedVariant := propagateMetaData v.dedentedVariant f
  }

public def getPseudoDedented? (doc : TaggedDoc) : Option PseudoDedented :=
  doc.getMetaData? PseudoDedented

end TaggedDoc

export TaggedDoc
  (untagged taggedNode taggedText taggedWhitespace isTagged tag addMetaData getMetaData? failure
    newline nl «break» hardNl text empty space nested hardNested doublyNested
    withFailureFallbackPenalty withOverflowFallbackPenalty withHeightFallbackPenalty
    fallbackOnFailure fallbackOnOverflow fallbackOnHeight aligned unflattenable flattened
    maybeFlattened unindented final initial free guarded either oneOf append join joinUsing fillWith
    fill fillWrapping fillUsingSpace fillUsingSpaceWrapping fillUsingSpaceWithSoftBoundaries
    fillSomeUsingSpace fillSomeUsingSpaceWrapping combine stickyCombine Sticky StickynessKind
    propagateStickyness PseudoAligned pseudoAligned isPseudoAligned needsAppBrackets sticky
    SelfDelimited mkSelfDelimited isSelfDelimited isBracketed RawFallback mkRawFallback
    isRawFallback getSticky? getStickynessKind? withStickyAlt withPosition SepArray
    propagateMetaData PseudoDedented pseudoDedented getPseudoDedented? softSpace)
