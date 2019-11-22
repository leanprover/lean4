/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Attributes

namespace Lean
namespace EqnCompiler

def mkMatchPatternAttr : IO TagAttribute :=
registerTagAttribute `matchPattern "mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)"

@[init mkMatchPatternAttr]
constant matchPatternAttr : TagAttribute := arbitrary _

@[export lean_has_match_pattern_attribute]
def hasMatchPatternAttribute (env : Environment) (n : Name) : Bool :=
matchPatternAttr.hasTag env n

end EqnCompiler
end Lean
