axiom testSorry {α : Sort _} : α

def foo (n : Nat)  : Nat := foo (n - 1)
decreasing_by
  skip
  match n with
  | 0 => exact testSorry
  | _ + 1 => exact testSorry

def bar (n : Nat) (m : Nat): Nat := bar (n - 1) (m - 1)
decreasing_by
  show _ < _
  match ‹Nat› with
  | 0 => exact testSorry
  | _ + 1 => exact testSorry
