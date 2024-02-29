/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Omega
import Init.Data.BitVec

namespace Lean.FinContra
/-!
Helper lemmas for the `finContra` tactic used by the `match`-compiler.
-/

theorem BitVec.lt_two_pow (a : BitVec n) : a.toNat < 2^n :=
  Fin.isLt a.toFin

theorem BitVec.val_ne_of_ne {i j : BitVec n} (h : i ≠ j) : i.toNat ≠ j.toNat :=
  (BitVec.toNat_ne i j).mp h

theorem step {a b : Nat} (h₁ : ¬ a = b) (h₂ : a < b + 1) : a < b := by
  omega

theorem false_of_lt_zero {a : Nat} (h : a < 0) : False :=
  Nat.not_lt_zero a h

end Lean.FinContra
