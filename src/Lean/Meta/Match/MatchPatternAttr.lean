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
Instructs the pattern matcher to unfold occurrences of this definition.

By default, only constructors and literals can be used for pattern matching. Using
`@[match_pattern]` allows using other definitions, as long as they eventually reduce to
constructors and literals.

Example:
```
@[match_pattern]
def yellowString : String := "yellow"

def isYellow (color : String) : Bool :=
  match color with
  | yellowString => true
  | _ => false
```
-/
@[builtin_doc]
builtin_initialize matchPatternAttr : TagAttribute ←
  registerTagAttribute `match_pattern "mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)"
    (validate := fun declName => do
      withExporting (isExporting := !isPrivateName declName) do
        if !(← getConstInfo declName).isDefinition then
          throwError "invalid `@[match_pattern]` attribute, `{.ofConstName declName}` is not an exposed definition")

@[export lean_has_match_pattern_attribute]
def hasMatchPatternAttribute (env : Environment) (n : Name) : Bool :=
  matchPatternAttr.hasTag env n

end Lean
