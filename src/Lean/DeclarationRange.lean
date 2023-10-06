/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MonadEnv
import Lean.AuxRecursor
import Lean.ToExpr
import Lean.Data.Lsp.PositionEncodingKind

namespace Lean

/-- A precomputed `character` field as in `Lean.Lsp.Position`. We
need to store this because some LSP clients want us to report the range
in terms of UTF-16, but converting a Unicode codepoint stored in
`Lean.Position` to UTF-16 requires loading and mapping the target
source file, which is IO-heavy.

To avoid a tricky invariant that there's a globally consistent
setting, all three possibilities are cached. -/
structure EncodedPosition where
  utf8 : Nat
  utf16 : Nat
  utf32 : Nat
  deriving Inhabited, DecidableEq, Repr

instance : ToExpr EncodedPosition where
  toExpr p := mkAppN (mkConst ``EncodedPosition.mk) #[toExpr p.utf8, toExpr p.utf16, toExpr p.utf32]
  toTypeExpr := mkConst ``EncodedPosition

def EncodedPosition.get (pos : EncodedPosition) : Lsp.PositionEncodingKind → Nat
  | .utf8 => pos.utf8
  | .utf16 => pos.utf16
  | .utf32 => pos.utf32

/-- Store position information for declarations. -/
structure DeclarationRange where
  pos        : Position
  charLsp    : EncodedPosition
  endPos     : Position
  endCharLsp : EncodedPosition
  deriving Inhabited, DecidableEq, Repr

instance : ToExpr DeclarationRange where
  toExpr r   := mkAppN (mkConst ``DeclarationRange.mk) #[toExpr r.pos, toExpr r.charLsp, toExpr r.endPos, toExpr r.endCharLsp]
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

def addDeclarationRanges [MonadEnv m] (declName : Name) (declRanges : DeclarationRanges) : m Unit :=
  modifyEnv fun env => declRangeExt.insert env declName declRanges

def findDeclarationRangesCore? [Monad m] [MonadEnv m] (declName : Name) : m (Option DeclarationRanges) :=
  return declRangeExt.find? (← getEnv) declName

def findDeclarationRanges? [Monad m] [MonadEnv m] [MonadLiftT IO m] (declName : Name) : m (Option DeclarationRanges) := do
  let env ← getEnv
  let ranges ← if isAuxRecursor env declName || isNoConfusion env declName || (← isRec declName)  then
    findDeclarationRangesCore? declName.getPrefix
  else
    findDeclarationRangesCore? declName
  match ranges with
  | none => return (← builtinDeclRanges.get (m := IO)).find? declName
  | some _ => return ranges

end Lean
