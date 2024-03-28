/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Extra notation that depends on Init/Meta
-/

prelude
import Init.Data.ToString.Macro
import Init.Meta

namespace Lean

macro "Macro.trace[" id:ident "]" s:interpolatedStr(term) : term =>
  `(Macro.trace $(quote id.getId.eraseMacroScopes) (s! $s))

end Lean
