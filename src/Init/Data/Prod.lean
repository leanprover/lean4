/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SimpLemmas

instance [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] : LawfulBEq (α × β) where
  eq_of_beq {a b} h := by cases a; cases b; simp [BEq.beq] at h; have ⟨h₁, h₂⟩ := h; rw [eq_of_beq h₁, eq_of_beq h₂]
  rfl {a} := by cases a; simp [BEq.beq, LawfulBEq.rfl]
