module
@[expose] public section -- TODO: remove after we fix congr_eq
example (x n : Nat)
    : 0 < match x with
          | 0  => 1
          | _ => x + n := by
  grind

example (x y : Nat)
    : 0 < match x, y with
          | 0, 0   => 1
          | _, _ => x + y := by -- x or y must be greater than 0
  grind
