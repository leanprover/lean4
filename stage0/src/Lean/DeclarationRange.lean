/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MonadEnv
import Lean.AuxRecursor

namespace Lean

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

structure DeclarationRanges where
  range          : DeclarationRange
  selectionRange : DeclarationRange
  deriving Inhabited, Repr

builtin_initialize declRangeExt : MapDeclarationExtension DeclarationRanges ← mkMapDeclarationExtension `declranges

def addDeclarationRanges [MonadEnv m] (declName : Name) (declRanges : DeclarationRanges) : m Unit :=
  modifyEnv fun env => declRangeExt.insert env declName declRanges

def findDeclarationRangesCore? [Monad m] [MonadEnv m] (declName : Name) : m (Option DeclarationRanges) :=
  return declRangeExt.find? (← getEnv) declName

def findDeclarationRanges? [Monad m] [MonadEnv m] (declName : Name) : m (Option DeclarationRanges) := do
  let env ← getEnv
  if isAuxRecursor env declName || isNoConfusion env declName || (← isRec declName)  then
    findDeclarationRangesCore? declName.getPrefix
  else
    findDeclarationRangesCore? declName

end Lean
