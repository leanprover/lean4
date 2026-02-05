/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
prelude

public import Lean.Elab.Term.TermElabM

set_option linter.missingDocs true

public section

namespace Lean.Doc
open Lean Elab Term

/--
A name of an import that should be present for a delayed check.
-/
structure PostponedImport : Type where
  /-- The module to be imported -/
  name : Name
deriving BEq, Hashable, Repr

instance : ToExpr PostponedImport where
  toTypeExpr := .const ``PostponedImport []
  toExpr | ⟨v⟩ => .app (.const ``PostponedImport.mk []) (toExpr v)

instance : Ord PostponedImport where
  compare
    | ⟨x⟩, ⟨y⟩ => x.quickCmp y

/--
A postponed check for an inline docstring element.
-/
structure PostponedCheck : Type where
  /--
  The handler to call to carry out the check. It should be a `PostponedCheckHandler.`
  -/
  handler : Name
  /--
  The imports that should be available when the test is carried out.
  -/
  imports : Array PostponedImport
  /--
  Information required to carry out the check.
  -/
  info : Dynamic
deriving TypeName

instance : Repr PostponedCheck where
  reprPrec v _ := "{ handler := " ++ repr v.handler ++ ", imports := " ++ repr v.imports ++ "}"

/--
A procedure to carry out some postponed check from a docstring.
-/
abbrev PostponedCheckHandler := (declName : Name) → (info : Dynamic) → TermElabM Unit

private unsafe def getHandlerUnsafe (name : Name) : TermElabM PostponedCheckHandler :=
  evalConstCheck PostponedCheckHandler ``PostponedCheckHandler name

@[implemented_by getHandlerUnsafe]
private opaque getHandler (name : Name) : TermElabM PostponedCheckHandler

private structure Stats where
  passed : Nat := 0
  failed : Array Exception := #[]

private def Stats.total (s : Stats) : Nat :=
  s.passed + s.failed.size

private abbrev CheckM := StateRefT Stats TermElabM

private def runCheck (act : TermElabM Unit) : CheckM Unit := do
  try
    act
    modify fun s => { s with passed := s.passed + 1 }
  catch
    | e =>
      modify fun s => { s with failed := s.failed.push e }

private partial def checkInlinePostponed (declName : Name) (inline : Inline ElabInline) : CheckM Unit := do
  match inline with
  | .other x is =>
    if let some { handler, imports, info } := x.val.get? PostponedCheck then
      for ⟨m⟩ in imports do
        unless (← getEnv).header.moduleNames.contains m do
          throwError "Check in `{.ofConstName declName}` requires that `{m}` is imported, but it is not."
      runCheck <| (← getHandler handler) declName info
    for i in is do
      checkInlinePostponed declName i
  | .concat is | .emph is | .bold is | .link is _ | .footnote _ is =>
    for i in is do
      checkInlinePostponed declName i
  | .image .. | .linebreak .. | .text .. | .code .. | .math .. => pure ()

private partial def checkBlockPostponed (declName : Name) (doc : Block ElabInline ElabBlock) : CheckM Unit := do
  match doc with
  | .other x bs =>
    if let some { handler, imports, info } := x.val.get? PostponedCheck then
      for ⟨m⟩ in imports do
        unless (← getEnv).header.moduleNames.contains m do
          throwError "Check in `{.ofConstName declName}` requires that `{m}` is imported, but it is not."
      runCheck <| (← getHandler handler) declName info
    for b in bs do
      checkBlockPostponed declName b
  | .concat bs | .blockquote bs =>
    for b in bs do
      checkBlockPostponed declName b
  | .ul items | .ol _ items =>
    for item in items do
      for b in item.contents do
        checkBlockPostponed declName b
  | .dl items =>
    for item in items do
      for i in item.term do
        checkInlinePostponed declName i
      for b in item.desc do
        checkBlockPostponed declName b
  | .para is =>
    for i in is do
      checkInlinePostponed declName i
  | .code .. => pure ()

private partial def checkPartPostponed (declName : Name) (doc : Part ElabInline ElabBlock Empty) : CheckM Unit := do
  for b in doc.content do
    checkBlockPostponed declName b
  for s in doc.subParts do
    checkPartPostponed declName s

private def checkDocStringPostponed (declName : Name) (doc : VersoDocString) : CheckM Unit := do
  let {text, subsections} := doc
  for b in text do
    checkBlockPostponed declName b
  for s in subsections do
    checkPartPostponed declName s

/--
Runs the postponed checks in all docstrings, reporting on the result.
-/
def checkPostponed : TermElabM Unit := do
  let mut checked : Array (Name × Stats) := #[]
  let st := versoDocStringExt.toEnvExtension.getState (← getEnv)
  for (decl, docs) in ← getBuiltinVersoDocStrings do
    let ((), out) ← checkDocStringPostponed decl docs |>.run {}
    if out.total > 0 then
      checked := checked.push (decl, out)
  for mod in st.importedEntries do
    for (decl, docs) in mod do
      let ((), out) ← checkDocStringPostponed decl docs |>.run {}
      if out.total > 0 then
        checked := checked.push (decl, out)
  for (decl, docs) in st.state do
    let ((), out) ← checkDocStringPostponed decl docs |>.run {}
    if out.total > 0 then
      checked := checked.push (decl, out)

  let msg : MessageData :=
    .trace { cls := `checks } m!"Postponed checks: {checked.size} declarations, \
        {checked.map (·.2.passed) |>.sum} passed, \
        {checked.map (·.2.failed.size) |>.sum} failed" <|
      checked.map fun (declName, stats) =>
        .trace {cls := `check} m!"`{.ofConstName declName}`: \
            {stats.passed} passed, \
            {stats.failed.size} failed" <|
          stats.failed.map (·.toMessageData)

  logInfo msg

/--
A postponed check that a syntax kind name exists.
-/
structure PostponedKind where
  /-- The kind's name. -/
  name : Name
deriving TypeName

/--
A name that will be checked to exist later.
-/
structure PostponedName where
  /--
  The name to check for.
  -/
  name : Name
deriving TypeName
