Import Int.

Variable Real : Type.
Alias ℝ : Real.
Builtin int_to_real : Int → Real.
Coercion int_to_real.
Definition nat_to_real (a : Nat) : Real := int_to_real (nat_to_int a).
Coercion nat_to_real.

Namespace Real.
Builtin numeral.

Builtin add : Real → Real → Real.
Infixl 65 + : add.

Builtin mul : Real → Real → Real.
Infixl 70 * : mul.

Builtin div : Real → Real → Real.
Infixl 70 / : div.

Builtin le : Real → Real → Bool.
Infix  50 <= : le.
Infix  50 ≤  : le.

Definition ge (a b : Real) : Bool := b ≤ a.
Infix 50 >= : ge.
Infix 50 ≥  : ge.

Definition lt (a b : Real) : Bool := ¬ (a ≥ b).
Infix 50 <  : lt.

Definition gt (a b : Real) : Bool := ¬ (a ≤ b).
Infix 50 >  : gt.

Definition sub (a b : Real) : Real := a + -1.0 * b.
Infixl 65 - : sub.

Definition neg (a : Real) : Real := -1.0 * a.
Notation 75 - _ : neg.

Definition abs (a : Real) : Real := if (0.0 ≤ a) a (- a).
Notation 55 | _ | : abs.
EndNamespace.
