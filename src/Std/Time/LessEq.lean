/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Lean.Data.Rat

namespace Std

set_option linter.all true

/--
Type class to check if a number `n` is less or equal than `m` in compile time and give me a proof.
-/
class Le (n : Nat) (m : Nat) where
  /-- The proof that n ≤ m. -/
  p : n ≤ m

instance : Le n n where
  p := Nat.le_refl n

instance (m : Nat) : Le 0 m where
  p := Nat.zero_le m

instance {n m : Nat} [Le n m] : Le (Nat.succ n) (Nat.succ m) where
  p := Nat.succ_le_succ (Le.p)
