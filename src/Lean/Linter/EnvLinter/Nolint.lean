/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski

Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
module

prelude
public import Lean.Attributes
import Init.Linter

public section

namespace Lean.Linter.EnvLinter

/-- Defines the user attribute `builtin_nolint` for skipping environment linters. -/
builtin_initialize builtinNolintAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `builtin_nolint
    descr := "Do not report this declaration in any of the tests of `lake builtin-lint`"
    getParam := fun _ => fun
      | `(attr| builtin_nolint $[$ids]*) => pure <| ids.map (·.getId.eraseMacroScopes)
      | _ => Elab.throwUnsupportedSyntax
  }

/-- Returns true if `decl` should be checked
using `linter`, i.e., if there is no `builtin_nolint` attribute. -/
def shouldBeLinted [Monad m] [MonadEnv m] (linter : Name) (decl : Name) : m Bool :=
  return !((builtinNolintAttr.getParam? (← getEnv) decl).getD #[]).contains linter

end Lean.Linter.EnvLinter
