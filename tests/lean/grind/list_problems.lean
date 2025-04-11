reset_grind_attrs%
set_option grind.warning false

attribute [grind] List.length_cons List.length_nil List.length_append

@[grind] theorem append_aux (as bs : List α) (i : Nat) (h : i < (as ++ bs).length) :
        (as ++ bs)[i] = if _ : i < as.length then as[i] else bs[i - as.length]'(by grind) := by
  sorry

attribute [grind] List.nil_append
attribute [grind] List.eq_nil_of_length_eq_zero

example {l : List α} {a : α} {i : Nat} (h : i = l.length) (w) :
    (l ++ [a])[i]'w = a := by
--  set_option trace.Meta.isDefEq true in
  set_option trace.grind.ematch.instance true in
  grind  -- Similar to issue above.

---
