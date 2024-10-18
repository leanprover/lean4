/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.MonadEnv
import Lean.AuxRecursor
import Lean.ToExpr

namespace Lean

/-- Store position information for declarations. -/
structure DeclarationRange where
  pos          : Position
  /-- A precomputed UTF-16 `character` field as in `Lean.Lsp.Position`. We need to store this
  because LSP clients want us to report the range in terms of UTF-16, but converting a Unicode
  codepoint stored in `Lean.Position` to UTF-16 requires loading and mapping the target source
  file, which is IO-heavy. -/
  charUtf16    : Nat
  endPos       : Position
  /-- See `charUtf16`. -/
  endCharUtf16 : Nat
  deriving Inhabited, DecidableEq, Repr

instance : ToExpr DeclarationRange where
  toExpr r   := mkAppN (mkConst ``DeclarationRange.mk) #[toExpr r.pos, toExpr r.charUtf16, toExpr r.endPos, toExpr r.endCharUtf16]
  toTypeExpr := mkConst ``DeclarationRange

structure DeclarationRanges where
  range          : DeclarationRange
  selectionRange : DeclarationRange
  deriving Inhabited, Repr

instance : ToExpr DeclarationRanges where
  toExpr r   := mkAppN (mkConst ``DeclarationRanges.mk) #[toExpr r.range, toExpr r.selectionRange]
  toTypeExpr := mkConst ``DeclarationRanges

builtin_initialize builtinDeclRanges : IO.Ref (NameMap DeclarationRanges) ← IO.mkRef {}
builtin_initialize declRangeExt : MapDeclarationExtension DeclarationRanges ← mkMapDeclarationExtension

def addBuiltinDeclarationRanges (declName : Name) (declRanges : DeclarationRanges) : IO Unit :=
  builtinDeclRanges.modify (·.insert declName declRanges)

def addDeclarationRanges [Monad m] [MonadEnv m] (declName : Name) (declRanges : DeclarationRanges) : m Unit := do
  unless declRangeExt.contains (← getEnv) declName do
    modifyEnv fun env => declRangeExt.insert env declName declRanges

def findDeclarationRangesCore? [Monad m] [MonadEnv m] (declName : Name) : m (Option DeclarationRanges) :=
  return declRangeExt.find? (← getEnv) declName

def findDeclarationRanges? [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (declName : Name) : m (Option DeclarationRanges) := do
  let env ← getEnv
  let ranges ← if isAuxRecursor env declName || isNoConfusion env declName || (← isRec declName)  then
    findDeclarationRangesCore? declName.getPrefix
  else
    findDeclarationRangesCore? declName
  match ranges with
  | none => return (← builtinDeclRanges.get (m := BaseIO)).find? declName
  | some _ => return ranges

end Lean
