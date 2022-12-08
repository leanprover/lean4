/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Attributes

namespace Lean

builtin_initialize neverExtractAttr : TagAttribute ←
  registerTagAttribute `never_extract "instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects."

@[export lean_has_never_extract_attribute]
partial def hasNeverExtractAttribute (env : Environment) (n : Name) : Bool :=
  let rec visit (n : Name) : Bool := neverExtractAttr.hasTag env n || (n.isInternal && visit n.getPrefix)
  visit n

end Lean
