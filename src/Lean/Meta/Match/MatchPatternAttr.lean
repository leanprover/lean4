/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean

builtin_initialize matchPatternAttr : TagAttribute ←
  registerTagAttribute `match_pattern "mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)"

@[export lean_has_match_pattern_attribute]
def hasMatchPatternAttribute (env : Environment) (n : Name) : Bool :=
  matchPatternAttr.hasTag env n

end Lean
