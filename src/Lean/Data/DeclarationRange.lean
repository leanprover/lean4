/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.Position

/-!
# Data types for declaration ranges

The environment extension for declaration ranges is in `Lean.DeclarationRange`.
-/

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

/--
A declaration location is a declaration range along with the name of the module the declaration resides in.
-/
structure DeclarationLocation where
  module : Name
  range : DeclarationRange
  deriving Inhabited, DecidableEq, Repr
