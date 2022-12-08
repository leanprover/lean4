/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Nat.Log2

def Fin.log2 (n : Fin m) : Fin m := ⟨Nat.log2 n.val, Nat.lt_of_le_of_lt (Nat.log2_le_self n.val) n.isLt⟩
