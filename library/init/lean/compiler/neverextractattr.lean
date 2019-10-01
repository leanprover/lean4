/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment
import init.lean.attributes

namespace Lean

def mkNeverExtractAttr : IO TagAttribute :=
registerTagAttribute `neverExtract "instruct the compiler that function applications using the tagged declaration should not be extracted when they are closed terms, nor common subexpression should be performed. This is useful for declarations that have implicit effects."

@[init mkNeverExtractAttr]
constant neverExtractAttr : TagAttribute := default _

@[export lean_has_never_extract_attribute]
def hasNeverExtractAttribute (env : Environment) (n : Name) : Bool :=
neverExtractAttr.hasTag env n

end Lean
