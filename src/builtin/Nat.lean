Import kernel.

Variable Nat : Type.
Alias ℕ : Nat.

Namespace Nat.

Builtin numeral.

Builtin add : Nat → Nat → Nat.
Infixl 65 +  : add.

Builtin mul : Nat → Nat → Nat.
Infixl 70 *  : mul.

Builtin le  : Nat → Nat → Bool.
Infix  50 <= : le.
Infix  50 ≤  : le.

Definition ge (a b : Nat) := b ≤ a.
Infix 50 >= : ge.
Infix 50 ≥  : ge.

Definition lt (a b : Nat) := ¬ (a ≥ b).
Infix 50 <  : lt.

Definition gt (a b : Nat) := ¬ (a ≤ b).
Infix 50 >  : gt.

Definition id (a : Nat) := a.
Notation 55 | _ | : id.

SetOpaque ge true.
SetOpaque lt true.
SetOpaque gt true.
SetOpaque id true.

EndNamespace.