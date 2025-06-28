/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public meta import Init.Meta

public section

syntax:max "s!" interpolatedStr(term) : term

macro_rules
  | `(s! $interpStr) => do interpStr.expandInterpolatedStr (← `(String)) (← `(toString))
