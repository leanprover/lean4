/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.SimpLemmas

instance [BEq α] [BEq β] [LawfulBEq α] [LawfulBEq β] : LawfulBEq (α × β) where
  eq_of_beq {a b} (h : a.1 == b.1 && a.2 == b.2) := by
    cases a; cases b
    refine congr (congrArg _ (eq_of_beq ?_)) (eq_of_beq ?_) <;> simp_all
  rfl {a} := by cases a; simp [BEq.beq, LawfulBEq.rfl]
