/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt
import Init.Data.String
universes u

instance : HashableUSize Nat where
  hashUSize n := USize.ofNat n

instance [HashableUSize α] [HashableUSize β] : HashableUSize (α × β) where
  hashUSize | (a, b) => mixUSizeHash (hashUSize a) (hashUSize b)

instance : HashableUSize Bool where
  hashUSize
    | true  => 11
    | false => 13

protected def Option.hash [HashableUSize α] : Option α → USize
  | none   => 11
  | some a => mixUSizeHash (hashUSize a) 13

instance [HashableUSize α] : HashableUSize (Option α) where
  hashUSize
    | none   => 11
    | some a => mixUSizeHash (hashUSize a) 13

instance [HashableUSize α] : HashableUSize (List α) where
  hashUSize as := as.foldl (fun r a => mixUSizeHash r (hashUSize a)) 7

instance : HashableUSize UInt32 where
  hashUSize n := n.toUSize

instance : HashableUSize UInt64 where
  hashUSize n := n.toUSize

instance : HashableUSize USize where
  hashUSize n := n

instance : HashableUSize Int where
  hashUSize
    | Int.ofNat n => USize.ofNat (2 * n)
    | Int.negSucc n => USize.ofNat (2 * n + 1)

instance (P : Prop) : HashableUSize P where
  hashUSize := Function.const P 0
