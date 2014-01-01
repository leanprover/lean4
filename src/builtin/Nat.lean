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

Axiom PlusZero (a : Nat)   : a + 0 = a.
Axiom PlusSucc (a b : Nat) : a + (b + 1) = (a + b) + 1.
Axiom Induction {P : Nat -> Bool} (Hb : P 0) (Hi : Pi (n : Nat) (H : P n), P (n + 1)) (a : Nat) : P a.

Theorem ZeroPlus (a : Nat) : 0 + a = a
:= Induction (show 0 + 0 = 0, Trivial)
             (fun (n : Nat) (H : 0 + n = n),
                  (show 0 + (n + 1) = n + 1,
                       let L1 : 0 + (n + 1) = (0 + n) + 1 := PlusSucc 0 n
                       in Subst L1 H))
             a.

Theorem SuccPlus (a b : Nat) : (a + 1) + b = (a + b) + 1
:= Induction (show (a + 1) + 0 = (a + 0) + 1,
                   (Subst (PlusZero (a + 1)) (Symm (PlusZero a))))
             (fun (n : Nat) (H : (a + 1) + n = (a + n) + 1),
                  (show (a + 1) + (n + 1) = (a + (n + 1)) + 1,
                        let L1 : (a + 1) + (n + 1) = ((a + 1) + n) + 1 := PlusSucc (a + 1) n,
                            L2 : (a + 1) + (n + 1) = ((a + n) + 1) + 1 := Subst L1 H,
                            L3 : (a + n) + 1 = a + (n + 1)             := Symm (PlusSucc a n)
                         in Subst L2 L3))
             b.

Theorem PlusComm (a b : Nat) : a + b = b + a
:= Induction (show a + 0 = 0 + a,
                   let L1 : a + 0 = a  := PlusZero a,
                       L2 : a = 0 + a  := Symm (ZeroPlus a)
                   in Trans L1 L2)
             (fun (n : Nat) (H : a + n = n + a),
                  (show a + (n + 1) = (n + 1) + a,
                        let L1 : a + (n + 1) = (a + n) + 1 := PlusSucc a n,
                            L2 : a + (n + 1) = (n + a) + 1 := Subst L1 H,
                            L3 : (n + a) + 1 = (n + 1) + a := Symm (SuccPlus n a)
                        in Trans L2 L3))
             b.

SetOpaque ge true.
SetOpaque lt true.
SetOpaque gt true.
SetOpaque id true.
EndNamespace.