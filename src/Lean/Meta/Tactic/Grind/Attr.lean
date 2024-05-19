/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Grind
open Simp

builtin_initialize grindNormExt : SimpExtension ←
  registerSimpAttr `grind_norm "simplification/normalization theorems for `grind`"

builtin_initialize grindNormSimprocExt : SimprocExtension ←
  registerSimprocAttr `grind_norm_proc "simplification/normalization procedured for `grind`" none

end Lean.Meta.Grind
