import Simplc

-- These higher order simp lemmas cause many confluence problems. Reconsider?
simp_lc ignore Option.map_subtype
simp_lc ignore Option.bind_subtype

namespace Option

attribute [simp] not_mem_none

example {a : { x // x ∈ o }} : some a.val = o := by
  match o, a with
  | none, ⟨x, h⟩ => simp at h
  | some b, ⟨x, h⟩ =>
    simp only [mem_def, some.injEq] at h
    simp [h]
simp_lc whitelist Option.mem_attach Option.mem_def

#guard_msgs (drop info) in
simp_lc check in Option
