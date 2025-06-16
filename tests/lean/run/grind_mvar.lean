open List
reset_grind_attrs%
attribute [grind →] Array.eq_empty_of_append_eq_empty eq_nil_of_length_eq_zero
attribute [grind] Vector.getElem?_append getElem?_dropLast

#guard_msgs (trace) in -- should not report any issues
set_option trace.grind.issues true
theorem dropLast_concat : dropLast (l₁ ++ [b]) = l₁ := by
   fail_if_success grind
   grind -ext only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
