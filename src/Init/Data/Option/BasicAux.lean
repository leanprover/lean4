/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
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

/--
Extracts the value from an `Option`, returning `Classical.ofNonempty` on `none`.

This is the noncomputable analogue of `Option.get!` that uses `Nonempty` instead of `Inhabited`.
-/
noncomputable def getV {α : Type u} [Nonempty α] : Option α → α
  | some x => x
  | none   => Classical.ofNonempty

theorem getV_eq_get? {α : Type u} {_ : Nonempty α} {x : Option α} :
    x.getV =
      match x with
      | some a => a
      | none => Classical.ofNonempty := by
  simp [getV]

end Option
