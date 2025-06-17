/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude

import Init.Grind.Module.Basic

namespace Lean.Grind

instance : AddRightCancel Nat where
  add_right_cancel _ _ _ := Nat.add_right_cancel

end Lean.Grind
