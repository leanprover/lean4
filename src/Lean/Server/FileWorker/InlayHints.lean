/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
prelude
import Lean.Server.GoTo
import Lean.Server.Requests

namespace Lean.Elab

def InlayHintLinkLocation.toLspLocation (srcSearchPath : SearchPath) (text : FileMap)
    (l : InlayHintLinkLocation) : IO (Option Lsp.Location) := do
  let some uri ← Server.documentUriFromModule srcSearchPath l.module
    | return none
  return some {
    uri
    range := text.utf8RangeToLspRange l.range
  }

def InlayHintLabelPart.toLspInlayHintLabelPart (srcSearchPath : SearchPath) (text : FileMap)
    (p : InlayHintLabelPart) : IO Lsp.InlayHintLabelPart := do
    let location? ← p.location?.bindM fun loc => loc.toLspLocation srcSearchPath text
    let tooltip? := do return .markdown { kind := .markdown, value := ← p.tooltip? }
    return {
      value := p.value
      location?,
      tooltip?
    }

def InlayHintLabel.toLspInlayHintLabel (srcSearchPath : SearchPath) (text : FileMap) : InlayHintLabel → IO Lsp.InlayHintLabel
  | .name n => do return .name n
  | .parts p => do return .parts <| ← p.mapM (·.toLspInlayHintLabelPart srcSearchPath text)

def InlayHintKind.toLspInlayHintKind : InlayHintKind → Lsp.InlayHintKind
  | .type => .type
  | .parameter => .parameter

def InlayHintTextEdit.toLspTextEdit (text : FileMap) (e : InlayHintTextEdit) : Lsp.TextEdit := {
  range := text.utf8RangeToLspRange e.range
  newText := e.newText
}

def InlayHintInfo.toLspInlayHint (srcSearchPath : SearchPath) (text : FileMap) (i : InlayHintInfo) : IO Lsp.InlayHint := do
  return {
    position := text.utf8PosToLspPos i.position
    label := ← i.label.toLspInlayHintLabel srcSearchPath text
    kind? := i.kind?.map (·.toLspInlayHintKind)
    textEdits? := some <| i.textEdits.map (·.toLspTextEdit text)
    tooltip? := do return .markdown { kind := .markdown, value := ← i.tooltip? }
    paddingLeft? := i.paddingLeft
    paddingRight? := i.paddingRight
  }

end Lean.Elab

namespace Lean.Server.FileWorker
open Lsp

def applyEditToHint? (hintMod : Name) (ihi : Elab.InlayHintInfo) (range : String.Range) (newText : String) : Option Elab.InlayHintInfo := do
  let isLabelLocAffectedByEdit :=
    match ihi.label with
    | .name _ => false
    | .parts ps =>
      ps.any fun p =>
        p.location?.any fun loc =>
          loc.module == hintMod && range.overlaps loc.range (includeFirstStop := true)
  -- We always include the stop of the edit range because insertion edit ranges may be empty,
  -- but we must still invalidate the inlay hint in this case.
  let isInlayHintInvalidatedByEdit :=
    range.contains ihi.position (includeStop := true) ||
      ihi.textEdits.any (range.overlaps ·.range (includeFirstStop := true)) ||
      isLabelLocAffectedByEdit
  if isInlayHintInvalidatedByEdit then
    none
  let byteOffset : Int := (newText.toSubstring.bsize : Int) - (range.bsize : Int)
  let shift (p : String.Pos) : String.Pos :=
    if range.stop < p then
      ⟨p.byteIdx + byteOffset |>.toNat⟩
    else if p < range.start then
      p
    else -- `range.start <= p && p <= range.stop`
      panic! s!"Got position {p} that should have been invalidated by edit at range {range.start}-{range.stop}"
  let shiftRange (r : String.Range) : String.Range := ⟨shift r.start, shift r.stop⟩
  return { ihi with
    position := shift ihi.position
    textEdits := ihi.textEdits.map fun edit => { edit with range := shiftRange edit.range }
    label :=
      match ihi.label with
      | .name s => .name s
      | .parts ps => .parts <| ps.map fun p => { p with
        location? := p.location?.map fun loc =>
          if loc.module == hintMod then
            { loc with range := shiftRange loc.range }
          else
            loc
      }
  }

structure InlayHintState where
  oldInlayHints      : Array Elab.InlayHintInfo
  lastEditTimestamp? : Option Nat
  deriving TypeName, Inhabited

def InlayHintState.init : InlayHintState := {
  oldInlayHints := #[]
  lastEditTimestamp? := none
}

def handleInlayHints (_ : InlayHintParams) (s : InlayHintState) :
    RequestM (LspResponse (Array InlayHint) × InlayHintState) := do
  let ctx ← read
  let srcSearchPath := ctx.srcSearchPath
  -- We delay sending inlay hints by 3000ms to avoid inlay hint flickering on the client.
  -- VS Code already has a mechanism for this, but it is not sufficient.
  let inlayHintEditDelayMs := 3000
  let timestamp ← IO.monoMsNow
  let editDelayMs :=
    match s.lastEditTimestamp? with
    | none => 0
    | some lastEditTimestamp =>
      let timeSinceLastEditMs := timestamp - lastEditTimestamp
      inlayHintEditDelayMs - timeSinceLastEditMs
  let (snaps, _, isComplete) ← ctx.doc.cmdSnaps.getFinishedPrefixWithConsistentLatency editDelayMs.toUInt32 (cancelTk? := ctx.cancelTk.truncatedTask)
  let finishedRange? : Option String.Range := do
    return ⟨⟨0⟩, ← List.max? <| snaps.map (fun s => s.endPos)⟩
  let oldInlayHints :=
    if let some finishedRange := finishedRange? then
      s.oldInlayHints.filter fun (ihi : Elab.InlayHintInfo) =>
        ! finishedRange.contains ihi.position
    else
      s.oldInlayHints
  let newInlayHints : Array Elab.InlayHintInfo ← (·.2) <$> StateT.run (s := #[]) do
    for s in snaps do
      s.infoTree.visitM' (postNode := fun ci i _ => do
        let .ofCustomInfo i := i
          | return
        let some ih := Elab.InlayHint.ofCustomInfo? i
          | return
        let ih ← ci.runMetaM ih.lctx ih.resolveDeferred
        modify (·.push ih.toInlayHintInfo))
  let inlayHints := newInlayHints ++ oldInlayHints
  let lspInlayHints ← inlayHints.mapM (·.toLspInlayHint srcSearchPath ctx.doc.meta.text)
  let r := { response := lspInlayHints, isComplete }
  let s := { s with oldInlayHints := inlayHints }
  RequestM.checkCanceled
  return (r, s)

def handleInlayHintsDidChange (p : DidChangeTextDocumentParams)
    : StateT InlayHintState RequestM Unit := do
  let meta := (← read).doc.meta
  let text := meta.text
  let srcSearchPath := (← read).srcSearchPath
  let .ok modName? ← EIO.toBaseIO <| do
      let some path := System.Uri.fileUriToPath? meta.uri
        | return none
      let some mod ← searchModuleNameOfFileName path srcSearchPath
        | return some <| ← moduleNameOfFileName path none
      return some mod
    | return
  let modName := modName?.getD .anonymous -- `.anonymous` occurs in untitled files
  let s ← get
  let mut updatedOldInlayHints := #[]
  for ihi in s.oldInlayHints do
    let mut ihi := ihi
    let mut inlayHintInvalidated := false
    for c in p.contentChanges do
      let .rangeChange changeRange newText := c
        | set <| { s with oldInlayHints := #[] } -- `fullChange` => all old inlay hints invalidated
          return
      let changeRange := text.lspRangeToUtf8Range changeRange
      let some ihi' := applyEditToHint? modName ihi changeRange newText
        | -- Change in some position of inlay hint => inlay hint invalidated
          inlayHintInvalidated := true
          break
      ihi := ihi'
    if ! inlayHintInvalidated then
      updatedOldInlayHints := updatedOldInlayHints.push ihi
  let isInlayHintInsertionEdit := p.contentChanges.all fun c => Id.run do
    let .rangeChange changeRange newText := c
      | return false
    let changeRange := text.lspRangeToUtf8Range changeRange
    let edit := ⟨changeRange, newText⟩
    return s.oldInlayHints.any (·.textEdits.contains edit)
  let timestamp ← IO.monoMsNow
  let lastEditTimestamp? :=
    if isInlayHintInsertionEdit then
      -- For some stupid reason, VS Code doesn't remove the inlay hint when applying it, so we
      -- try to figure out whether the edit was an insertion of an inlay hint and then respond
      -- to the request without latency so that it inserted ASAP.
      none
    else
      some timestamp
  set <| { s with
    oldInlayHints := updatedOldInlayHints
    lastEditTimestamp?
  }

builtin_initialize
  registerPartialStatefulLspRequestHandler
    "textDocument/inlayHint"
    "workspace/inlayHint/refresh"
    500
    InlayHintParams
    (Array InlayHint)
    InlayHintState
    .init
    handleInlayHints
    handleInlayHintsDidChange

end Lean.Server.FileWorker
