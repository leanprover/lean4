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
  oldFinishedSnaps   : Nat
  lastEditTimestamp? : Option Nat
  deriving TypeName, Inhabited

def InlayHintState.init : InlayHintState := {
  oldInlayHints := #[]
  oldFinishedSnaps := 0
  lastEditTimestamp? := none
}

def handleInlayHints (p : InlayHintParams) (s : InlayHintState) :
    RequestM (LspResponse (Array InlayHint) × InlayHintState) := do
  let ctx ← read
  let text := ctx.doc.meta.text
  let range := text.lspRangeToUtf8Range p.range
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
  let (snaps, _, isComplete) ← ctx.doc.cmdSnaps.getFinishedPrefixWithConsistentLatency editDelayMs.toUInt32 (cancelTk? := ctx.cancelTk.cancellationTask)
  let snaps := snaps.toArray
  let finishedSnaps := snaps.size
  let oldFinishedSnaps := s.oldFinishedSnaps
  -- File processing is monotonic modulo `didChange` notifications.
  assert! finishedSnaps >= oldFinishedSnaps
  -- VS Code emits inlay hint requests *every time the user scrolls*. This is reasonably expensive,
  -- so in addition to re-using old inlay hints from parts of the file that haven't been processed
  -- yet, we also re-use old inlay hints from parts of the file that have been processed already
  -- with the current state of the document.
  let invalidOldInlayHintsRange : String.Range := {
    start := snaps[oldFinishedSnaps - 1]?.map (·.endPos) |>.getD ⟨0⟩
    stop := snaps[finishedSnaps - 1]?.map (·.endPos) |>.getD ⟨0⟩
  }
  let oldInlayHints :=
    s.oldInlayHints.filter fun (ihi : Elab.InlayHintInfo) =>
      ! invalidOldInlayHintsRange.contains ihi.position
  let newInlayHints : Array Elab.InlayHintInfo ← (·.2) <$> StateT.run (s := #[]) do
    for s in snaps[oldFinishedSnaps:] do
      s.infoTree.visitM' (postNode := fun ci i _ => do
        let .ofCustomInfo i := i
          | return
        let some ih := Elab.InlayHint.ofCustomInfo? i
          | return
        let ih ← ci.runMetaM ih.lctx ih.resolveDeferred
        modify (·.push ih.toInlayHintInfo))
  let allInlayHints := newInlayHints ++ oldInlayHints
  let inlayHintsInRange := allInlayHints.filter (range.contains (includeStop := true) ·.position)
  let lspInlayHints ← inlayHintsInRange.mapM (·.toLspInlayHint srcSearchPath text)
  let r := { response := lspInlayHints, isComplete }
  let s := { s with
    oldInlayHints := allInlayHints
    oldFinishedSnaps := finishedSnaps
  }
  return (r, s)

def handleInlayHintsDidChange (p : DidChangeTextDocumentParams)
    : StateT InlayHintState RequestM Unit := do
  let s ← get
  let updatedOldInlayHints ← updateOldInlayHints s.oldInlayHints
  let lastEditTimestamp? ← determineLastEditTimestamp? s.oldInlayHints
  set <| { s with
    oldInlayHints := updatedOldInlayHints
    oldFinishedSnaps := 0
    lastEditTimestamp?
  }

where

  updateOldInlayHints (oldInlayHints : Array Elab.InlayHintInfo) : RequestM (Array Elab.InlayHintInfo) := do
    let meta := (← read).doc.meta
    let text := meta.text
    let srcSearchPath := (← read).srcSearchPath
    let modName? ← EIO.toBaseIO <| do
      let some path := System.Uri.fileUriToPath? meta.uri
        | return none
      let some mod ← searchModuleNameOfFileName path srcSearchPath
        | return some <| ← moduleNameOfFileName path none
      return some mod
    let modName ← match modName? with
      | .ok (some modName) => pure modName
      | .ok none => pure .anonymous -- `.anonymous` occurs in untitled files
      | .error err => throw <| .ofIoError err
    let mut updatedOldInlayHints := #[]
    for ihi in oldInlayHints do
      let mut ihi := ihi
      let mut inlayHintInvalidated := false
      for c in p.contentChanges do
        let .rangeChange changeRange newText := c
          | return #[] -- `fullChange` => all old inlay hints invalidated
        let changeRange := text.lspRangeToUtf8Range changeRange
        let some ihi' := applyEditToHint? modName ihi changeRange newText
          | -- Change in some position of inlay hint => inlay hint invalidated
            inlayHintInvalidated := true
            break
        ihi := ihi'
      if ! inlayHintInvalidated then
        updatedOldInlayHints := updatedOldInlayHints.push ihi
    return updatedOldInlayHints

  determineLastEditTimestamp? (oldInlayHints : Array Elab.InlayHintInfo) : RequestM (Option Nat) := do
    let text := (← read).doc.meta.text
    let isInlayHintInsertionEdit := p.contentChanges.all fun c => Id.run do
      let .rangeChange changeRange newText := c
        | return false
      let changeRange := text.lspRangeToUtf8Range changeRange
      let edit := ⟨changeRange, newText⟩
      return oldInlayHints.any (·.textEdits.contains edit)
    let timestamp ← IO.monoMsNow
    if isInlayHintInsertionEdit then
      -- For some stupid reason, VS Code doesn't remove the inlay hint when applying it, so we
      -- try to figure out whether the edit was an insertion of an inlay hint and then respond
      -- to the request without latency so that it inserted ASAP.
      return none
    else
      return some timestamp

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
