/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude

public import Lean.Attributes

namespace Lean

builtin_initialize allowNativeDecideAttr : TagAttribute ←
  registerTagAttribute `allow_native_decide
    "mark definition as allowed to be used in `native_decide` computations"
