/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Data.Lsp.Utf16
import Lean.Meta.InferType
import Lean.Util.Recognizers

/-!
# Utilities for creating and recognizing `sorry`

This module
-/

namespace Lean.Meta

/--
Returns `sorryAx type synthetic`. Recall that `synthetic` is true if this sorry is from an error.

See also `Lean.Meta.mkLabeledSorry`, for creating a `sorry` that encodes the origin position of the `sorry`,
and which has facilities for making a `sorry` that is not defeq to any other `sorry`.
-/
def mkSorry (type : Expr) (synthetic : Bool) : MetaM Expr := do
  let u ← getLevel type
  return mkApp2 (mkConst ``sorryAx [u]) type (toExpr synthetic)

structure SorryLabelView where
  /--
  Records the origin module name, logical source position, and LSP range for the `sorry`.
  The logical source position is used when displaying the sorry when the `pp.sorrySource` option is true,
  and the LSP range is used for "go to definition".
  -/
  module? : Option (Name × Position × Lsp.Range) := none

def SorryLabelView.encode (view : SorryLabelView) : CoreM Name :=
  let name :=
    if let some (mod, pos, range) := view.module? then
      mod |>.num pos.line |>.num pos.column |>.num range.start.line |>.num range.start.character |>.num range.end.line |>.num range.end.character
    else
      .anonymous
  mkFreshUserName (name.str "_sorry")

def SorryLabelView.decode? (name : Name) : Option SorryLabelView := do
  guard <| name.hasMacroScopes
  let .str name "_sorry" := name.eraseMacroScopes | failure
  if let .num (.num (.num (.num (.num (.num name posLine) posCol) startLine) startChar) endLine) endChar := name then
    return { module? := some (name, ⟨posLine, posCol⟩, ⟨⟨startLine, startChar⟩, ⟨endLine, endChar⟩⟩) }
  else
    failure

/--
Makes a `sorryAx` that encodes the current ref into the term to support "go to definition" for the `sorry`.
If `unique` is true, the `sorry` is unique, in the sense that it is not defeq to any other `sorry` created by `mkLabeledSorry`.
-/
def mkLabeledSorry (type : Expr) (synthetic : Bool) (unique : Bool) : MetaM Expr := do
  let tag ←
    if let (some startPos, some endPos) := ((← getRef).getPos?, (← getRef).getTailPos?) then
      let fileMap ← getFileMap
      let pos := fileMap.toPosition startPos
      let range := fileMap.utf8RangeToLspRange ⟨startPos, endPos⟩
      SorryLabelView.encode { module? := (← getMainModule, pos, range) }
    else
      SorryLabelView.encode {}
  if unique then
    let e ← mkSorry (mkForall `tag .default (mkConst ``Lean.Name) type) synthetic
    return .app e (toExpr tag)
  else
    let e ← mkSorry (mkForall `tag .default (mkConst ``Unit) type) synthetic
    let tag' := mkApp4 (mkConst ``Function.const [levelOne, levelOne]) (mkConst ``Unit) (mkConst ``Lean.Name) (mkConst ``Unit.unit) (toExpr tag)
    return .app e tag'

/--
Returns a `SorryLabelView` if `e` is an application of an expression returned by `mkLabeledSorry`.
If it is, then the `sorry` takes the first three arguments, and the tag is at argument 3.
-/
def isLabeledSorry? (e : Expr) : Option SorryLabelView := do
  guard <| e.isAppOf ``sorryAx
  let numArgs := e.getAppNumArgs
  guard <| numArgs ≥ 3
  let arg := e.getArg! 2
  if let some tag := arg.name? then
    SorryLabelView.decode? tag
  else
    guard <| arg.isAppOfArity ``Function.const 4
    guard <| arg.appFn!.appArg!.isAppOfArity ``Unit.unit 0
    let tag ← arg.appArg!.name?
    SorryLabelView.decode? tag
