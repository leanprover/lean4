Import nat.

Variable Int : Type.
Alias ℤ : Int.

Builtin Int::numeral.

Builtin Int::add : Int → Int → Int.
Infixl 65 + : Int::add.

Builtin Int::mul : Int → Int → Int.
Infixl 70 * : Int::mul.

Builtin Int::div : Int → Int → Int.
Infixl 70 div : Int::div.

Builtin Int::le : Int → Int → Bool.
Infix  50 <= : Int::le.
Infix  50 ≤  : Int::le.

Definition Int::ge (a b : Int) : Bool := b ≤ a.
Infix 50 >= : Int::ge.
Infix 50 ≥  : Int::ge.

Definition Int::lt (a b : Int) : Bool := ¬ (a ≥ b).
Infix 50 <  : Int::lt.

Definition Int::gt (a b : Int) : Bool := ¬ (a ≤ b).
Infix 50 >  : Int::gt.

Definition Int::sub (a b : Int) : Int := a + -1 * b.
Infixl 65 - : Int::sub.

Definition Int::neg (a : Int) : Int := -1 * a.
Notation 75 - _ : Int::neg.

Definition Int::mod (a b : Int) : Int := a - b * (a div b).
Infixl 70 mod : Int::mod.

Builtin nat_to_int : Nat → Int.
Coercion nat_to_int.

Definition Int::divides (a b : Int) : Bool := (b mod a) = 0.
Infix 50 | : Int::divides.

Definition Int::abs (a : Int) : Int := if (0 ≤ a) a (- a).
Notation 55 | _ | : Int::abs.

Definition Nat::sub (a b : Nat) : Int := nat_to_int a - nat_to_int b.
Infixl 65 - : Nat::sub.

Definition Nat::neg (a : Nat) : Int := - (nat_to_int a).
Notation 75 - _ : Nat::neg.

SetOpaque Int::sub true.
SetOpaque Int::neg true.
SetOpaque Int::mod true.
SetOpaque Int::divides true.
SetOpaque Int::abs true.
SetOpaque Int::ge true.
SetOpaque Int::lt true.
SetOpaque Int::gt true.
SetOpaque Nat::sub true.
SetOpaque Nat::neg true.
