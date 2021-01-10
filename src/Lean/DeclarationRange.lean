/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MonadEnv

namespace Lean

structure DeclarationRange where
  pos    : Position
  endPos : Position
  deriving Inhabited, DecidableEq

structure DeclarationRanges where
  range          : DeclarationRange
  selectionRange : DeclarationRange
  deriving Inhabited

builtin_initialize declRangeExt : MapDeclarationExtension DeclarationRanges ← mkMapDeclarationExtension `declranges

def addDeclarationRanges [MonadEnv m] (declName : Name) (declRanges : DeclarationRanges) : m Unit :=
  modifyEnv fun env => declRangeExt.insert env declName declRanges

def findDeclarationRanges? [Monad m] [MonadEnv m] (declName : Name) : m (Option DeclarationRanges) :=
  return declRangeExt.find? (← getEnv) declName

end Lean
