/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.Format.Basic
public import Init.Data.ToString.Macro

public section

namespace Std

syntax:max "f!" interpolatedStr(term) : term

macro_rules
  | `(f! $interpStr) => do interpStr.expandInterpolatedStr (← `(Format)) (← `(Std.format))

end Std
