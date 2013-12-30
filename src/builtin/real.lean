Import basic.
Import nat.
Import int.

Variable Real : Type.
Alias ℝ : Real.

Builtin Real::numeral.

Builtin Real::add : Real → Real → Real.
Infixl 65 + : Real::add.

Builtin Real::mul : Real → Real → Real.
Infixl 70 * : Real::mul.

Builtin Real::div : Real → Real → Real.
Infixl 70 / : Real::div.

Builtin Real::le : Real → Real → Bool.
Infix  50 <= : Real::le.
Infix  50 ≤  : Real::le.

Definition Real::ge (a b : Real) : Bool := b ≤ a.
Infix 50 >= : Real::ge.
Infix 50 ≥  : Real::ge.

Definition Real::lt (a b : Real) : Bool := ¬ (a ≥ b).
Infix 50 <  : Real::lt.

Definition Real::gt (a b : Real) : Bool := ¬ (a ≤ b).
Infix 50 >  : Real::gt.

Definition Real::sub (a b : Real) : Real := a + -1.0 * b.
Infixl 65 - : Real::sub.

Definition Real::neg (a : Real) : Real := -1.0 * a.
Notation 75 - _ : Real::neg.

Definition Real::abs (a : Real) : Real := if (0.0 ≤ a) a (- a).
Notation 55 | _ | : Real::abs.

Builtin int_to_real : Int → Real.
Coercion int_to_real.

Definition nat_to_real (a : Nat) : Real := int_to_real (nat_to_int a).
Coercion nat_to_real.
