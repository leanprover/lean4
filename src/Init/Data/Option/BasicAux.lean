/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Option.Basic
public import Init.Util

public section

universe u

namespace Option

/--
Extracts the value from an `Option`, panicking on `none`.
-/
@[inline, expose] def get! {α : Type u} [Inhabited α] : Option α → α
  | some x => x
  | none   => panic! "value is none"

end Option
