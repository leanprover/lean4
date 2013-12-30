Import kernel.

Variable Nat : Type.
Alias ℕ : Nat.

Builtin Nat::numeral.

Builtin Nat::add : Nat → Nat → Nat.
Infixl 65 +  : Nat::add.

Builtin Nat::mul : Nat → Nat → Nat.
Infixl 70 *  : Nat::mul.

Builtin Nat::le  : Nat → Nat → Bool.
Infix  50 <= : Nat::le.
Infix  50 ≤  : Nat::le.

Definition Nat::ge (a b : Nat) := b ≤ a.
Infix 50 >= : Nat::ge.
Infix 50 ≥  : Nat::ge.

Definition Nat::lt (a b : Nat) := ¬ (a ≥ b).
Infix 50 <  : Nat::lt.

Definition Nat::gt (a b : Nat) := ¬ (a ≤ b).
Infix 50 >  : Nat::gt.

Definition Nat::id (a : Nat) := a.
Notation 55 | _ | : Nat::id.

SetOpaque Nat::ge true.
SetOpaque Nat::lt true.
SetOpaque Nat::gt true.
SetOpaque Nat::id true.