/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core

attribute [grind_cases] And Prod False Empty True Unit Exists

namespace Lean.Grind.Eager

attribute [scoped grind_cases] Or

end Lean.Grind.Eager
