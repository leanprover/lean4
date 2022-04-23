open Nat.SOM
example : (x + y) * (x + y + 1) = x * (1 + y + x) + (y + 1 + x) * y :=
  let ctx := [x, y]
  let lhs : Expr := .mul (.add (.var 0) (.var 1)) (.add (.add (.var 0) (.var 1)) (.num 1))
  let rhs : Expr := .add (.mul (.var 0) (.add (.add (.num 1) (.var 1)) (.var 0)))
                         (.mul (.add (.add (.var 1) (.num 1)) (.var 0)) (.var 1))
  Expr.eq_of_toPoly_eq ctx lhs rhs (Eq.refl true)
