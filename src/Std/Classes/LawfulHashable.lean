/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

class LawfulHashable (α : Type u) [BEq α] [Hashable α] where
  hash_eq (a b : α) : a == b → hash a = hash b

theorem hash_eq [BEq α] [Hashable α] [LawfulHashable α] {a b : α} : a == b → hash a = hash b :=
  LawfulHashable.hash_eq a b

instance (priority := low) [BEq α] [Hashable α] [LawfulBEq α] : LawfulHashable α where
  hash_eq _ _ h := eq_of_beq h ▸ rfl
