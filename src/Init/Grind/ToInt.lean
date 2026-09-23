/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude

public section

namespace Lean.Grind

/--
TODO: delete this class (and this file) after the next `update-stage0`. The current
stage0 binary's `getToIntId?` still resolves the constant `Lean.Grind.ToInt` by name
while building the stage1 library; the class only needs to exist, no instances.
-/
class ToInt (α : Type u) where

end Lean.Grind
