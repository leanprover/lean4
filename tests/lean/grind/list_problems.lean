theorem getElem?_eq_some_iff {l : List α} : l[i]? = some a ↔ ∃ h : i < l.length, l[i] = a := by
  induction l
  · grind
  · cases i
    · -- Fails because of the issue:
      --   [issue] failed to create E-match local theorem for
      --     ∀ (x : 1 ≤ tail.length), ¬tail[0] = a
      -- despite having asserted `1 ≤ tail.length `.
      grind
    · -- Similarly
      grind

attribute [grind] List.getElem_append_left List.getElem_append_right

@[simp] theorem getElem_concat_length {l : List α} {a : α} {i : Nat} (h : i = l.length) (w) :
    (l ++ [a])[i]'w = a := by
  subst h; grind
-- [issue] failed to create E-match local theorem for
--   ∀ (h₁ : True), (l ++ [a])[l.length] = [a][l.length - l.length]
