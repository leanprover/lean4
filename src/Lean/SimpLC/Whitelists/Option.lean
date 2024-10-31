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

-- TODO: re-evaluate these (appeared while moving `SimpLC` into Lean.)
-- Will be resolved by https://github.com/leanprover/lean4/pull/5892
simp_lc whitelist Option.forIn'_toList forIn'_eq_forIn

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Option _root_
