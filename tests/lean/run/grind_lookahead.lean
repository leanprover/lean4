set_option grind.warning false
reset_grind_attrs%

attribute [grind] List.eq_nil_of_length_eq_zero

example (as : List α) (h : as.length < 2) (h : as.length ≠ 1) (f : List α → Nat) :
    f as = f [] := by
  grind

example (as : List α) (h : as.length < 2) (h : as.length ≠ 1) : as = [] := by
  grind -lookahead

example (as : List α) (h : as.length < 2) (h : as.length ≠ 1) : as = [] := by
  grind (splits := 0)

example (as : List α) (h : as.length < 2) (h : as.length ≠ 1) (f : List α → Nat)
    : f as = f [] := by
  fail_if_success grind (splits := 0) -lookahead -- Need lookahead or case-splits
  sorry
