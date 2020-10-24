#lang lean4
/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt
import Init.Data.String
universes u

class Hashable (α : Type u) :=
  (hash : α → USize)

export Hashable (hash)

@[extern "lean_usize_mix_hash"]
constant mixHash (u₁ u₂ : USize) : USize

@[extern "lean_string_hash"]
protected constant String.hash (s : @& String) : USize

instance : Hashable String := ⟨String.hash⟩

instance : Hashable Nat := {
  hash := fun n => USize.ofNat n
}

instance {α β} [Hashable α] [Hashable β] : Hashable (α × β) := {
  hash := fun (a, b) => mixHash (hash a) (hash b)
}

protected def Option.hash {α} [Hashable α] : Option α → USize
  | none   => 11
  | some a => mixHash (hash a) 13

instance {α} [Hashable α] : Hashable (Option α) := {
  hash := fun
    | none   => 11
    | some a => mixHash (hash a) 13
}

instance {α} [Hashable α] : Hashable (List α) := {
  hash := fun as => as.foldl (fun r a => mixHash r (hash a)) 7
}
