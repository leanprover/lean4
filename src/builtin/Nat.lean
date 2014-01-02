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

Axiom SuccInj {a b : Nat} (H : a + 1 = b + 1) : a = b
Axiom PlusZero (a : Nat)   : a + 0 = a.
Axiom PlusSucc (a b : Nat) : a + (b + 1) = (a + b) + 1.
Axiom MulZero (a : Nat)    : a * 0 = 0.
Axiom MulSucc (a b : Nat)  : a * (b + 1) = a * b + a.
Axiom Induction {P : Nat → Bool} (Hb : P 0) (Hi : Π (n : Nat) (H : P n), P (n + 1)) (a : Nat) : P a.

Theorem ZeroNeOne : 0 ≠ 1 := Trivial.

Theorem ZeroPlus (a : Nat) : 0 + a = a
:= Induction (show 0 + 0 = 0, Trivial)
             (λ (n : Nat) (Hi : 0 + n = n),
                let L1 : 0 + (n + 1) = (0 + n) + 1 := PlusSucc 0 n
                in  show 0 + (n + 1) = n + 1,         Subst L1 Hi)
             a.

Theorem SuccPlus (a b : Nat) : (a + 1) + b = (a + b) + 1
:= Induction (show (a + 1) + 0 = (a + 0) + 1,
                   (Subst (PlusZero (a + 1)) (Symm (PlusZero a))))
             (λ (n : Nat) (Hi : (a + 1) + n = (a + n) + 1),
                let L1 : (a + 1) + (n + 1) = ((a + 1) + n) + 1 := PlusSucc (a + 1) n,
                    L2 : (a + 1) + (n + 1) = ((a + n) + 1) + 1 := Subst L1 Hi,
                    L3 : (a + n) + 1 = a + (n + 1)             := Symm (PlusSucc a n)
                in show (a + 1) + (n + 1) = (a + (n + 1)) + 1,    Subst L2 L3)
             b.

Theorem PlusComm (a b : Nat) : a + b = b + a
:= Induction (show a + 0 = 0 + a,
                   let L1 : a + 0 = a  := PlusZero a,
                       L2 : a = 0 + a  := Symm (ZeroPlus a)
                   in Trans L1 L2)
             (λ (n : Nat) (Hi : a + n = n + a),
                let L1 : a + (n + 1) = (a + n) + 1 := PlusSucc a n,
                    L2 : a + (n + 1) = (n + a) + 1 := Subst L1 Hi,
                    L3 : (n + a) + 1 = (n + 1) + a := Symm (SuccPlus n a)
                in  show a + (n + 1) = (n + 1) + a,   Trans L2 L3)
             b.

Theorem PlusAssoc (a b c : Nat) : a + (b + c) = (a + b) + c
:= Induction (show 0 + (b + c) = (0 + b) + c,
                   Subst (ZeroPlus (b + c)) (Symm (ZeroPlus b)))
             (λ (n : Nat) (Hi : n + (b + c) = (n + b) + c),
                let L1 : (n + 1) + (b + c) = (n + (b + c)) + 1 := SuccPlus n (b + c),
                    L2 : (n + 1) + (b + c) = ((n + b) + c) + 1 := Subst L1 Hi,
                    L3 : ((n + b) + 1) + c = ((n + b) + c) + 1 := SuccPlus (n + b) c,
                    L4 : (n + b) + 1 = (n + 1) + b             := Symm (SuccPlus n b),
                    L5 : ((n + 1) + b) + c = ((n + b) + c) + 1 := Subst L3 L4,
                    L6 : ((n + b) + c) + 1 = ((n + 1) + b) + c := Symm L5
                in  show (n + 1) + (b + c) = ((n + 1) + b) + c,   Trans L2 L6)
             a.

Theorem ZeroMul (a : Nat) : 0 * a = 0
:= Induction (show 0 * 0 = 0, Trivial)
             (λ (n : Nat) (Hi : 0 * n = 0),
                let L1 : 0 * (n + 1) = (0 * n) + 0 := MulSucc 0 n,
                    L2 : 0 * (n + 1) = 0 + 0       := Subst L1 Hi
                in  show 0 * (n + 1) = 0,          L2)
             a.

Theorem SuccMul (a b : Nat) : (a + 1) * b = a * b + b
:= Induction (show (a + 1) * 0 = a * 0 + 0,
                   Trans (MulZero (a + 1)) (Symm (Subst (PlusZero (a * 0)) (MulZero a))))
             (λ (n : Nat) (Hi : (a + 1) * n = a * n + n),
                let L1  : (a + 1) * (n + 1)   = (a + 1) * n + (a + 1)  := MulSucc (a + 1) n,
                    L2  : (a + 1) * (n + 1)   = a * n + n + (a + 1)    := Subst L1 Hi,
                    L3  : a * n + n + (a + 1) = a * n + n + a + 1      := PlusAssoc (a * n + n) a 1,
                    L4  : a * n + n + a       = a * n + (n + a)        := Symm (PlusAssoc (a * n) n a),
                    L5  : a * n + n + (a + 1) = a * n + (n + a) + 1    := Subst L3 L4,
                    L6  : a * n + n + (a + 1) = a * n + (a + n) + 1    := Subst L5 (PlusComm n a),
                    L7  : a * n + (a + n)     = a * n + a + n          := PlusAssoc (a * n) a n,
                    L8  : a * n + n + (a + 1) = a * n + a + n + 1      := Subst L6 L7,
                    L9  : a * n + a           = a * (n + 1)            := Symm (MulSucc a n),
                    L10 : a * n + n + (a + 1) = a * (n + 1) + n + 1    := Subst L8 L9,
                    L11 : a * (n + 1) + n + 1 = a * (n + 1) + (n + 1)  := Symm (PlusAssoc (a * (n + 1)) n 1)
                    in show (a + 1) * (n + 1) = a * (n + 1) + (n + 1),
                       Trans (Trans L2 L10) L11)
             b.

Theorem OneMul (a : Nat) : 1 * a = a
:= Induction (show 1 * 0 = 0, Trivial)
             (λ (n : Nat) (Hi : 1 * n = n),
                let L1 : 1 * (n + 1) = 1 * n + 1 := MulSucc 1 n
                in show 1 * (n + 1) = n + 1, Subst L1 Hi)
             a.

Theorem MulOne (a : Nat) : a * 1 = a
:= Induction (show 0 * 1 = 0, Trivial)
             (λ (n : Nat) (Hi : n * 1 = n),
                let L1 : (n + 1) * 1 = n * 1 + 1 := SuccMul n 1
                in  show (n + 1) * 1 = n + 1, Subst L1 Hi)
             a.

Theorem MulComm (a b : Nat) : a * b = b * a
:= Induction (show a * 0 = 0 * a, Trans (MulZero a) (Symm (ZeroMul a)))
             (λ (n : Nat) (Hi : a * n = n * a),
                let L1 : a * (n + 1) = a * n + a := MulSucc a n,
                    L2 : (n + 1) * a = n * a + a := SuccMul n a,
                    L3 : (n + 1) * a = a * n + a := Subst L2 (Symm Hi)
                in show a * (n + 1) = (n + 1) * a, Trans L1 (Symm L3))
             b.


Theorem Distribute (a b c : Nat) : a * (b + c) = a * b + a * c
:= Induction (let L1 : 0 * (b + c)   = 0     := ZeroMul (b + c),
                  L2 : 0 * b + 0 * c = 0 + 0 := Subst (Subst (Refl (0 * b + 0 * c)) (ZeroMul b)) (ZeroMul c),
                  L3 : 0 + 0 = 0             := Trivial
              in show 0 * (b + c) = 0 * b + 0 * c, Trans L1 (Symm (Trans L2 L3)))
             (λ (n : Nat) (Hi : n * (b + c) = n * b + n * c),
                let L1  : (n + 1) * (b + c)       = n * (b + c) + (b + c)     := SuccMul n (b + c),
                    L2  : (n + 1) * (b + c)       = n * b + n * c + (b + c)   := Subst L1 Hi,
                    L3  : n * b + n * c + (b + c) = n * b + n * c + b + c     := PlusAssoc (n * b + n * c) b c,
                    L4  : n * b + n * c + b       = n * b + (n * c + b)       := Symm (PlusAssoc (n * b) (n * c) b),
                    L5  : n * b + n * c + b       = n * b + (b + n * c)       := Subst L4 (PlusComm (n * c) b),
                    L6  : n * b + (b + n * c)     = n * b + b + n * c         := PlusAssoc (n * b) b (n * c),
                    L7  : n * b + (b + n * c)     = (n + 1) * b + n * c       := Subst L6 (Symm (SuccMul n b)),
                    L8  : n * b + n * c + b       = (n + 1) * b + n * c       := Trans L5 L7,
                    L9  : n * b + n * c + (b + c) = (n + 1) * b + n * c + c   := Subst L3 L8,
                    L10 : (n + 1) * b + n * c + c = (n + 1) * b + (n * c + c) := Symm (PlusAssoc ((n + 1) * b) (n * c) c),
                    L11 : (n + 1) * b + n * c + c = (n + 1) * b + (n + 1) * c := Subst L10 (Symm (SuccMul n c)),
                    L12 : n * b + n * c + (b + c) = (n + 1) * b + (n + 1) * c := Trans L9 L11
                in show (n + 1) * (b + c) = (n + 1) * b + (n + 1) * c,
                   Trans L2 L12)
             a.

Theorem Distribute2 (a b c : Nat) : (a + b) * c = a * c + b * c
:= let L1 : (a + b) * c = c * (a + b)   := MulComm (a + b) c,
       L2 : c * (a + b) = c * a + c * b := Distribute c a b,
       L3 : (a + b) * c = c * a + c * b := Trans L1 L2
   in Subst (Subst L3 (MulComm c a)) (MulComm c b).

Theorem MulAssoc (a b c : Nat) : a * (b * c) = a * b * c
:= Induction (let L1 : 0 * (b * c) = 0       := ZeroMul (b * c),
                  L2 : 0 * b * c   = 0 * c   := Subst (Refl (0 * b * c)) (ZeroMul b),
                  L3 : 0 * c       = 0       := ZeroMul c
              in show 0 * (b * c) = 0 * b * c, Trans L1 (Symm (Trans L2 L3)))
             (λ (n : Nat) (Hi : n * (b * c) = n * b * c),
                let L1 : (n + 1) * (b * c)     = n * (b * c) + (b * c)   := SuccMul n (b * c),
                    L2 : (n + 1) * (b * c)     = n * b * c + (b * c)     := Subst L1 Hi,
                    L3 : n * b * c + (b * c)   = (n * b + b) * c         := Symm (Distribute2 (n * b) b c),
                    L4 : n * b * c + (b * c)   = (n + 1) * b * c         := Subst L3 (Symm (SuccMul n b))
                in show (n + 1) * (b * c) = (n + 1) * b * c, Trans L2 L4)
             a.

SetOpaque ge true.
SetOpaque lt true.
SetOpaque gt true.
SetOpaque id true.
EndNamespace.