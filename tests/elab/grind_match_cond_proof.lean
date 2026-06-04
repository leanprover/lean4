-- Better as a `theorem` and not an `example` until #13950 is fixed
theorem test (a b : Bool) (q : Bool) (hq : q = true) :
    match a, b with
    | false, false => q = true
    | true, true => q = true
    | _, _ => True := by
  grind
