/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Data.Options

public section

namespace Lean

register_builtin_option maxRecDepth : Nat := {
  defValue := defaultMaxRecDepth
  descr    := "maximum recursion depth for many Lean procedures"
}

end Lean
