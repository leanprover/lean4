reset_grind_attrs%

attribute [grind] List.length_set
attribute [grind →] List.eq_nil_of_length_eq_zero

open List in
example {as : List α} {i : Nat} (h : i < as.length) :
    as.set i as[i] = as := by
  apply ext_getElem
  · sorry
  · intro n h₁ h₂
    -- works:
    grind [getElem_set]

attribute [grind] List.getElem_set

open List in
example {as : List α} {i : Nat} (h : i < as.length) :
    as.set i as[i] = as := by
  apply ext_getElem
  · sorry
  · intro n h₁ h₂
    -- fails:
    grind

---
reset_grind_attrs%

theorem getElem?_eq_some_iff {l : List α} : l[i]? = some a ↔ ∃ h : i < l.length, l[i] = a := by
  induction l
  · sorry
  · cases i
    · -- Better support for implication and dependent implication.
      -- We need inequality propagation (or case-splits)
      grind
    · -- Similarly
      grind

---
reset_grind_attrs%

attribute [grind] List.getElem_append_left List.getElem_append_right
attribute [grind] List.length_cons List.length_nil

example {l : List α} {a : α} {i : Nat} (h : i = l.length) (w) :
    (l ++ [a])[i]'w = a := by
  grind -- Similar to issue above.

---
