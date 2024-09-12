/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

namespace Lean.Grind

theorem intro_with_eq (p p' q : Prop) (he : p = p') (h : p' → q) : p → q :=
  fun hp => h (he.mp hp)

end Lean.Grind
