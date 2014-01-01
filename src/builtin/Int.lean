Import Nat.

Variable Int : Type.
Alias ℤ : Int.
Builtin nat_to_int : Nat → Int.
Coercion nat_to_int.

Namespace Int.
Builtin numeral.

Builtin add : Int → Int → Int.
Infixl 65 + : add.

Builtin mul : Int → Int → Int.
Infixl 70 * : mul.

Builtin div : Int → Int → Int.
Infixl 70 div : div.

Builtin le : Int → Int → Bool.
Infix  50 <= : le.
Infix  50 ≤  : le.

Definition ge (a b : Int) : Bool := b ≤ a.
Infix 50 >= : ge.
Infix 50 ≥  : ge.

Definition lt (a b : Int) : Bool := ¬ (a ≥ b).
Infix 50 <  : lt.

Definition gt (a b : Int) : Bool := ¬ (a ≤ b).
Infix 50 >  : gt.

Definition sub (a b : Int) : Int := a + -1 * b.
Infixl 65 - : sub.

Definition neg (a : Int) : Int := -1 * a.
Notation 75 - _ : neg.

Definition mod (a b : Int) : Int := a - b * (a div b).
Infixl 70 mod : mod.

Definition divides (a b : Int) : Bool := (b mod a) = 0.
Infix 50 | : divides.

Definition abs (a : Int) : Int := if (0 ≤ a) a (- a).
Notation 55 | _ | : abs.

SetOpaque sub true.
SetOpaque neg true.
SetOpaque mod true.
SetOpaque divides true.
SetOpaque abs true.
SetOpaque ge true.
SetOpaque lt true.
SetOpaque gt true.
EndNamespace.

Namespace Nat.
Definition sub (a b : Nat) : Int := nat_to_int a - nat_to_int b.
Infixl 65 - : sub.

Definition neg (a : Nat) : Int := - (nat_to_int a).
Notation 75 - _ : neg.

SetOpaque sub true.
SetOpaque neg true.
EndNamespace.