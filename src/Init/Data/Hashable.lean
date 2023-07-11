/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt.Basic
import Init.Data.String
universe u

instance : Hashable Nat where
  hash n := UInt64.ofNat n

instance : Hashable String.Pos where
  hash p := UInt64.ofNat p.byteIdx

instance [Hashable α] [Hashable β] : Hashable (α × β) where
  hash | (a, b) => mixHash (hash a) (hash b)

instance : Hashable Bool where
  hash
    | true  => 11
    | false => 13

instance [Hashable α] : Hashable (Option α) where
  hash
    | none   => 11
    | some a => mixHash (hash a) 13

instance [Hashable α] : Hashable (List α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

instance [Hashable α] : Hashable (Array α) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

instance : Hashable UInt8 where
  hash n := n.toUInt64

instance : Hashable UInt16 where
  hash n := n.toUInt64

instance : Hashable UInt32 where
  hash n := n.toUInt64

instance : Hashable UInt64 where
  hash n := n

instance : Hashable USize where
  hash n := n.toUInt64

instance : Hashable (Fin n) where
  hash v := v.val.toUInt64

instance : Hashable Int where
  hash
    | Int.ofNat n => UInt64.ofNat (2 * n)
    | Int.negSucc n => UInt64.ofNat (2 * n + 1)

instance (P : Prop) : Hashable P where
  hash _ := 0

/-- An opaque (low-level) hash operation used to implement hashing for pointers. -/
@[always_inline, inline] def hash64 (u : UInt64) : UInt64 :=
  mixHash u 11
