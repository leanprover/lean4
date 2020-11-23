/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt
import Init.Data.String
universes u

instance : Hashable Nat := {
  hash := fun n => USize.ofNat n
}

instance [Hashable α] [Hashable β] : Hashable (α × β) := {
  hash := fun (a, b) => mixHash (hash a) (hash b)
}

protected def Option.hash [Hashable α] : Option α → USize
  | none   => 11
  | some a => mixHash (hash a) 13

instance [Hashable α] : Hashable (Option α) := {
  hash := fun
    | none   => 11
    | some a => mixHash (hash a) 13
}

instance [Hashable α] : Hashable (List α) := {
  hash := fun as => as.foldl (fun r a => mixHash r (hash a)) 7
}
