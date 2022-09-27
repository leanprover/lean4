/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic
import Init.PanicAux

universe u

namespace Option

@[inline] def get! {α : Type u} [Inhabited α] : Option α → (info : CallerInfo := by caller_info) → α
  | some x, _ => x
  | none  , _ => panic! "value is none"

end Option
