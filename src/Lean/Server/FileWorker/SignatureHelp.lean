/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Server.InfoUtils
public import Lean.Data.Lsp
public import Init.Data.Array.Sort.Basic
import Lean.PrettyPrinter.Delaborator

public section

namespace Lean.Server.FileWorker.SignatureHelp

open Lean

def determineSignatureHelp (tree : Elab.InfoTree) (appStx : Syntax)
    : IO (Option Lsp.SignatureHelp) := do
  let some (appCtx, .ofTermInfo appInfo) := tree.smallestInfo? fun
      | .ofTermInfo ti =>
        -- HACK: Use range of syntax to figure out corresponding `TermInfo`.
        -- This is necessary because in order to accurately determine which `Syntax` to use,
        -- we have to use the original command syntax before macro expansions,
        -- whereas the `Syntax` in the `InfoTree` is always from some stage of elaboration.
        ti.stx.getRangeWithTrailing? == appStx.getRangeWithTrailing?
      | _ => false
    | return none
  let app := appInfo.expr
  let some fmt ← appCtx.runMetaM appInfo.lctx do
      let appType ← instantiateMVars <| ← Meta.inferType app
      if ! appType.isForall then
        return none
      let (stx, _) ← PrettyPrinter.delabCore appType
        (delab := PrettyPrinter.Delaborator.delabForallWithSignature)
      return some <| ← PrettyPrinter.ppTerm ⟨stx⟩
    | return none
  return some {
    signatures := #[{ label := toString fmt : Lsp.SignatureInformation }]
    activeSignature? := some 0
    -- We do not mark the active parameter at all, as this would require retaining parameter indices
    -- through the delaborator.
    -- However, since we display the signature help using the `TermInfo` of the application,
    -- not the function itself, this is not a problem:
    -- The parameters keeps reducing as one adds arguments to the function, and the active
    -- parameter is then always the first explicit one.
    -- This feels very intuitive, so we don't need to thread any additional information
    -- through the delaborator for highlighting the active parameter.
    activeParameter? := none
  }

inductive CandidateKind where
  /--
  Cursor is in the position of the argument to a pipe, like `<|` or `$`. Low precedence.
  Ensures that `fun <| otherFun <cursor>` yields the signature help of `otherFun`, not `fun`.
  -/
  | pipeArg
  /--
  Cursor is in the position of the trailing whitespace of some term. Medium precedence.
  Ensures that `fun otherFun <cursor>` yields the signature help of `fun`, not `otherFun`.
  -/
  | termArg
  /--
  Cursor is in the position of the argument to a function that already has other arguments applied
  to it. High precedence.
  -/
  | appArg

def CandidateKind.prio : CandidateKind → Nat
  | .pipeArg => 0
  | .termArg => 1
  | .appArg  => 2

structure Candidate where
  kind   : CandidateKind
  appStx : Syntax

inductive SearchControl where
  /-- In a syntax stack, keep searching upwards, continuing with the parent of the current term. -/
  | continue
  /-- Stop the search through a syntax stack. -/
  | stop

private def lineCommentPosition? (s : String) : Option s.Pos :=
  s.find? "--"

private def isPositionInLineComment (text : FileMap) (pos : String.Pos.Raw) : Bool := Id.run do
  let requestedLineNumber := text.toPosition pos |>.line
  let lineStartPos := text.lineStart requestedLineNumber
  let lineEndPos := text.lineStart (requestedLineNumber + 1)
  let line := String.Pos.Raw.extract text.source lineStartPos lineEndPos
  let some lineCommentPos := lineCommentPosition? line
    | return false
  return pos >= lineCommentPos.offset.offsetBy lineStartPos

open CandidateKind in
def findSignatureHelp? (text : FileMap) (ctx? : Option Lsp.SignatureHelpContext) (cmdStx : Syntax)
    (tree : Elab.InfoTree) (requestedPos : String.Pos.Raw) : IO (Option Lsp.SignatureHelp) := do
  -- HACK: Since comments are whitespace, the signature help can trigger on comments.
  -- This is especially annoying on end-of-line comments, as the signature help will trigger on
  -- every space in the comment.
  -- This branch avoids this particular annoyance, but doesn't prevent the signature help from
  -- triggering on other comment kinds.
  if isPositionInLineComment text requestedPos then
    return none
  let stack? := cmdStx.findStack? fun stx => Id.run do
    let some range := stx.getRangeWithTrailing? (canonicalOnly := true)
      | return false
    return range.contains requestedPos (includeStop := true)
  let some stack := stack?
    | return none
  let stack := stack.toArray.map (·.1)
  let mut candidates : Array Candidate := #[]
  for h:i in *...stack.size do
    let stx := stack[i]
    let parent := stack[i+1]?.getD .missing
    let (kind?, control) := determineCandidateKind stx parent
    if let some kind := kind? then
      candidates := candidates.push ⟨kind, stx⟩
    if control matches .stop then
      break
  -- Uses a stable sort so that we prefer inner candidates over outer candidates.
  candidates := candidates.mergeSort (fun c1 c2 => c1.kind.prio >= c2.kind.prio)
  -- Look through all candidates until we find a signature help.
  -- This helps in cases where the priority puts terms without `TermInfo` or ones that are not
  -- applications of a `forall` in front of ones that do.
  -- This usually happens when `.termArg` candidates overshadow `.pipeArg` candidates,
  -- but the `.termArg` candidates are not semantically valid left-hand sides of applications.
  let hasHighPrioCandidate := candidates.any (·.kind.prio > CandidateKind.termArg.prio)
  for candidate in candidates do
    if candidate.kind matches .termArg && hasHighPrioCandidate then
      -- If all high prio candidates agree that there is no function application here,
      -- we trust them instead of falling back to `.termArg` candidates.
      -- This ensures that no signature help is displayed for a function that is passed as
      -- the last argument to another function.
      return none
    if let some signatureHelp ← determineSignatureHelp tree candidate.appStx then
      return some signatureHelp
  return none
where
  determineCandidateKind (stx : Syntax) (parent : Syntax)
      : Option CandidateKind × SearchControl := Id.run do
    let c kind? : Option CandidateKind × SearchControl := (kind?, .continue)
    let some tailPos := stx.getTailPos? (canonicalOnly := true)
      | return (none, .continue)
    -- If the cursor is not in the trailing range of the syntax, then we don't display a signature
    -- help. This prevents two undesirable scenarios:
    -- - Since for applications `f 0 0 0`, the `InfoTree` only contains `TermInfo` for
    --   `f` and `f 0 0 0`, we can't display accurate signature help for the sub-applications
    --   `f 0` or `f 0 0`. Hence, we only display the signature help after `f` and `f 0 0 0`,
    --   i.e. in the trailing range of the syntax of a candidate.
    -- - When the search through the syntax stack passes through a node with more than one child
    --   that is not an application, terminating the search if the cursor is on the interior of the
    --   syntax ensures that we do not display signature help for functions way outside of the
    --   current term that is being edited.
    --   We still want to display it for such complex terms if we are in the trailing range of the
    --   term since the complex term might produce a function for which we want to display a
    --   signature help.
    -- If we are ever on the interior of a term, then we will also be on the interior of terms
    -- further up in the syntax stack, as these subsume the inner term, and so we terminate
    -- the search early in this case.
    if requestedPos < tailPos then
      return (none, .stop)
    let isManualTrigger := ctx?.any (·.triggerKind matches .invoked)
    let isRetrigger := ctx?.any (·.isRetrigger)
    let isCursorAfterTailPosLine :=
      (text.toPosition requestedPos).line != (text.toPosition tailPos).line
    -- Application arguments are allowed anywhere in the trailing whitespace of a function,
    -- e.g. on successive lines, but displaying the signature help in all of those lines
    -- can be annoying (e.g. when `#check`ing a function and typing in the lines after it).
    -- Hence, we only display the signature help automatically when the cursor is on the same line
    -- as the tail position of the syntax, but allow users to display it by manually triggering
    -- the signature help (`Ctrl+Shift+Space` in VS Code). We also display it in successive lines
    -- if the user never closed it in the meantime, i.e. when the signature help was simply
    -- retriggered.
    if ! isManualTrigger && ! isRetrigger && isCursorAfterTailPosLine then
      return (none, .continue)
    if stx matches .ident .. then
      match parent with
      -- Do not yield a candidate `f` for `_ |>.f <cursor>`, `_.f <cursor>` or `.f <cursor>`.
      -- Since `f` is an `identArg` candidate, has a `TermInfo` of its own and is a subterm of
      -- these dot notations, we need to avoid picking its `TermInfo` by accident.
      | `($_ |>.$_:ident $_*) => return c none
      | `($_.$_:ident) => return c none
      | `(.$_:ident) => return c none
      | _ => return c termArg
    let .node (kind := kind) (args := args) .. := stx
      | return c none
    -- `nullKind` is usually used for grouping together arguments, so we just skip it until
    -- we have more tangible nodes at hand.
    if kind == nullKind then
      return c none
    if kind == ``Parser.Term.app then
      return c appArg
    match stx with
    | `($_ <| $_) => return c pipeArg
    | `($_ $ $_) => return c pipeArg
    | `($_ |>.$_:ident $_*) => return c pipeArg
    | `(.$_:ident) => return c termArg
    | `($_.$_:ident) => return c termArg
    | _ =>
      if args.size <= 1 then
        return c none
      return c termArg
