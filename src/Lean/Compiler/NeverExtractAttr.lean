/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Attributes

public section

namespace Lean

/--
Instructs the compiler that function applications using the tagged declaration should not be
extracted when they are closed terms, and that common subexpression elimination should not be
performed.

Ordinarily, the Lean compiler identifies closed terms (without free variables) and extracts them
to top-level definitions. This optimization can prevent unnecessary recomputation of values.

Preventing the extraction of closed terms is useful for declarations that have implicit effects
that should be repeated.
-/
@[builtin_doc]
builtin_initialize neverExtractAttr : TagAttribute ←
  registerTagAttribute `never_extract "instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects."

partial def hasNeverExtractAttribute (env : Environment) (n : Name) : Bool :=
  let rec visit (n : Name) : Bool := neverExtractAttr.hasTag env n || (n.isInternal && visit n.getPrefix)
  visit n

end Lean
