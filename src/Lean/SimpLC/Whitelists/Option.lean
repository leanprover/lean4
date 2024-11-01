/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.SimpLC.Whitelists.Root

-- These higher order simp lemmas cause many confluence problems. Reconsider?
simp_lc ignore Option.map_subtype
simp_lc ignore Option.bind_subtype

namespace Option

attribute [simp] not_mem_none

-- This is a plausible simp lemma, except that its discrimination key `@some _ _.1` is too weak.
theorem foo {a : { x // x ∈ o }} : some a.val = o := by
  match o, a with
  | none, ⟨x, h⟩ => simp at h
  | some b, ⟨x, h⟩ =>
    simp only [mem_def, some.injEq] at h
    simp [h]
simp_lc whitelist Option.mem_attach Option.mem_def

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Option _root_
