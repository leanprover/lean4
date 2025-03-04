axiom testSorry {α : Sort _} : α

def foo (n : Nat)  : Nat := foo (n - 1)
decreasing_by
  skip
  match n with
  | 0 => exact sorry
  | _ + 1 => exact sorry
