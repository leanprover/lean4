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

instance : Hashable ByteArray where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

instance : Hashable (Fin n) where
  hash v := v.val.toUInt64

instance : Hashable Char where
  hash c := c.val.toUInt64

instance : Hashable Int where
  hash
    | Int.ofNat n => UInt64.ofNat (2 * n)
    | Int.negSucc n => UInt64.ofNat (2 * n + 1)

instance (P : Prop) : Hashable P where
  hash _ := 0

/-- An opaque (low-level) hash operation used to implement hashing for pointers. -/
@[always_inline, inline] def hash64 (u : UInt64) : UInt64 :=
  mixHash u 11

/-- `LawfulHashable α` says that the `BEq α` and `Hashable α` instances on `α` are compatible, i.e.,
that `a == b` implies `hash a = hash b`. This is automatic if the `BEq` instance is lawful.
-/
class LawfulHashable (α : Type u) [BEq α] [Hashable α] where
  /-- If `a == b`, then `hash a = hash b`. -/
  hash_eq (a b : α) : a == b → hash a = hash b

theorem hash_eq [BEq α] [Hashable α] [LawfulHashable α] {a b : α} : a == b → hash a = hash b :=
  LawfulHashable.hash_eq a b

instance (priority := low) [BEq α] [Hashable α] [LawfulBEq α] : LawfulHashable α where
  hash_eq _ _ h := eq_of_beq h ▸ rfl
