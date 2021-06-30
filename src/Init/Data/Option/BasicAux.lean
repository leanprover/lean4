/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Option.Basic
import Init.Util

universe u

namespace Option

@[inline] def get! {α : Type u} [Inhabited α] : Option α → α
  | some x => x
  | none   => panic! "value is none"

end Option
