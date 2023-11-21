import Lean.Data.Rat

/-!
Tests for `pp.numericTypes` and `pp.natLit`

RFC #3021
-/

open Lean (Rat)

section

/-!
Both raw nat lits and non-raw natural numbers pretty print the same by default
-/
#check nat_lit 22
#check 22

set_option pp.natLit true

/-!
The raw nat lit pretty prints with the `nat_lit` prefix when `pp.natLit` is true.
-/
#check nat_lit 22
#check 22

end

section
set_option pp.numericTypes true

/-!
The `pp.numericTypes` option sets `pp.natLit` to true.
-/
#check nat_lit 22

/-!
Natural number literal
-/
#check (22 : Rat)

/-!
Negative integer literal
-/
#check (-22 : Rat)

/-!
Rational literal of two natural numbers
-/
#check (22 / 17 : Rat)

/-!
Rational literal of a negative integer and a rational
-/
#check (-22 / 17 : Rat)

/-!
Not a rational literal since the denominator is negative.
-/
#check (-22 / -17 : Rat)

/-!
Natural number literal for `Fin`.
-/
#check (17 : Fin 22)

/-!
Natural number literal for `Nat`.
-/
#check 2

/-!
Natural number literals in the context of an equation.
-/
#check 2 + 1 = 3

/-!
Testing `pp.all` override. The `2` should not appear with `nat_lit` in the `OfNat.ofNat` expression.
-/
set_option pp.all true
#check 2

end

section
set_option pp.all true

/-!
Testing `pp.all`.
-/
#check 2

/-!
Testing `pp.all` when `pp.natLit` is *explicitly* set to true.
-/
set_option pp.natLit true
#check 2

end
