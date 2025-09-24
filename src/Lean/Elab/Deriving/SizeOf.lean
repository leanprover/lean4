/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.SizeOf
public import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

public section

/-!
Remark: `SizeOf` instances are automatically generated. We add support for `deriving instance` for `SizeOf`
just to be able to use them to define instances for types defined at `Prelude.lean`
-/

namespace Lean.Elab.Deriving.SizeOf

open Command

def mkSizeOfHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      withoutExposeFromCtors declName <| liftTermElabM <| Meta.mkSizeOfInstances declName
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `SizeOf mkSizeOfHandler

end Lean.Elab.Deriving.SizeOf
