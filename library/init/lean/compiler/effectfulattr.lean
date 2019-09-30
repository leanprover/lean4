/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.environment
import init.lean.attributes

namespace Lean

def mkEffectfulAttr : IO TagAttribute :=
registerTagAttribute `effectful "mark that a declaration has implicit effects, and the compiler should avoid optimizations such as common subexpression elimination and closed term extraction"

@[init mkEffectfulAttr]
constant effectfulAttr : TagAttribute := default _

@[export lean_has_effectful_attribute]
def hasEffectfulAttribute (env : Environment) (n : Name) : Bool :=
effectfulAttr.hasTag env n

end Lean
