/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Attributes

namespace Lean

builtin_initialize opaqueReprAttr : TagAttribute ←
  registerTagAttribute `opaque_repr "instruct the compiler that this type has an opaque representation, and should not be treated as a wrapper type."

@[export lean_has_opaque_repr_attribute]
def hasOpaqueReprAttribute (env : Environment) (n : Name) : Bool :=
  opaqueReprAttr.hasTag env n

end Lean
