reset_grind_attrs%
open List

theorem length_pos_of_ne_nil {l : List α} (h : l ≠ []) : 0 < l.length := by
  cases l <;> simp_all

theorem getLast?_dropLast {xs : List α} :
    xs.dropLast.getLast? = if xs.length ≤ 1 then none else xs[xs.length - 2]? := by
  grind (splits := 23) only [List.getElem?_eq_none, List.getElem?_reverse, getLast?_eq_getElem?,
    List.head?_eq_getLast?_reverse, getElem?_dropLast, List.getLast?_reverse, List.length_dropLast,
    List.length_reverse, length_nil, List.reverse_reverse, head?_nil, List.getElem?_eq_none,
    length_pos_of_ne_nil, getLast?_nil, List.head?_reverse, List.getLast?_eq_head?_reverse,
    → List.eq_nil_of_length_eq_zero, = List.getElem?_nil, reverse_nil, cases Or]
