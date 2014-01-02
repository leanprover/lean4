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
Axiom Induction {P : Nat → Bool} (Hb : P 0) (iH : Π (n : Nat) (H : P n), P (n + 1)) (a : Nat) : P a.

Theorem ZeroNeOne : 0 ≠ 1 := Trivial.

Theorem ZeroPlus (a : Nat) : 0 + a = a
:= Induction (show 0 + 0 = 0, Trivial)
             (λ (n : Nat) (iH : 0 + n = n),
                calc  0 + (n + 1)  =  (0 + n) + 1   :  PlusSucc 0 n
                              ...  =  n + 1         :  { iH })
             a.

Theorem SuccPlus (a b : Nat) : (a + 1) + b = (a + b) + 1
:= Induction (calc (a + 1) + 0   =  a + 1        :  PlusZero (a + 1)
                        ...      =  (a + 0) + 1  :  { Symm (PlusZero a) })
             (λ (n : Nat) (iH : (a + 1) + n = (a + n) + 1),
                calc   (a + 1) + (n + 1)   =   ((a + 1) + n) + 1  :  PlusSucc (a + 1) n
                                   ...     =   ((a + n) + 1) + 1  :  { iH }
                                   ...     =   (a + (n + 1)) + 1  :  { show (a + n) + 1 = a + (n + 1), Symm (PlusSucc a n) })
             b.

Theorem PlusComm (a b : Nat) : a + b = b + a
:= Induction (calc a + 0   = a     : PlusZero a
                     ...   = 0 + a : Symm (ZeroPlus a))
             (λ (n : Nat) (iH : a + n = n + a),
                calc   a + (n + 1)   =   (a + n) + 1 : PlusSucc a n
                             ...     =   (n + a) + 1 : { iH }
                             ...     =   (n + 1) + a : Symm (SuccPlus n a))
             b.

Theorem PlusAssoc (a b c : Nat) : a + (b + c) = (a + b) + c
:= Induction (calc 0 + (b + c)  =  b + c        : ZeroPlus (b + c)
                         ...    =  (0 + b) + c  : { Symm (ZeroPlus b) })
             (λ (n : Nat) (iH : n + (b + c) = (n + b) + c),
                calc (n + 1) + (b + c)   =    (n + (b + c)) + 1   :  SuccPlus n (b + c)
                                  ...    =    ((n + b) + c) + 1   :  { iH }
                                  ...    =    ((n + b) + 1) + c   :  Symm (SuccPlus (n + b) c)
                                  ...    =    ((n + 1) + b) + c   :  { show (n + b) + 1 = (n + 1) + b,  Symm (SuccPlus n b) })
             a.

Theorem ZeroMul (a : Nat) : 0 * a = 0
:= Induction (show 0 * 0 = 0, Trivial)
             (λ (n : Nat) (iH : 0 * n = 0),
                calc  0 * (n + 1)  =  (0 * n) + 0 : MulSucc 0 n
                              ...  =  0 + 0       : { iH }
                              ...  =  0           : Trivial)
             a.

Theorem SuccMul (a b : Nat) : (a + 1) * b = a * b + b
:= Induction (calc (a + 1) * 0   =  0         : MulZero (a + 1)
                           ...   =  a * 0     : Symm (MulZero a)
                           ...   =  a * 0 + 0 : Symm (PlusZero (a * 0)))
             (λ (n : Nat) (iH : (a + 1) * n = a * n + n),
                calc   (a + 1) * (n + 1)  =    (a + 1) * n + (a + 1)  :  MulSucc (a + 1) n
                                   ...    = a * n + n + (a + 1)       :  { iH }
                                   ...    = a * n + n + a + 1         :  PlusAssoc (a * n + n) a 1
                                   ...    = a * n + (n + a) + 1       :  { show  a * n + n + a = a * n + (n + a), Symm (PlusAssoc (a * n) n a) }
                                   ...    = a * n + (a + n) + 1       :  { PlusComm n a }
                                   ...    = a * n + a + n + 1         :  { PlusAssoc (a * n) a n }
                                   ...    = a * (n + 1) + n + 1       :  { Symm (MulSucc a n) }
                                   ...    = a * (n + 1) + (n + 1)     :  Symm (PlusAssoc (a * (n + 1)) n 1))
             b.

Theorem OneMul (a : Nat) : 1 * a = a
:= Induction (show 1 * 0 = 0, Trivial)
             (λ (n : Nat) (iH : 1 * n = n),
                calc  1 * (n + 1)  =  1 * n + 1 :  MulSucc 1 n
                              ...  =  n + 1     : { iH })
             a.

Theorem MulOne (a : Nat) : a * 1 = a
:= Induction (show 0 * 1 = 0, Trivial)
             (λ (n : Nat) (iH : n * 1 = n),
                calc  (n + 1) * 1  =  n * 1 + 1 : SuccMul n 1
                             ...   =  n + 1     : { iH })
             a.

Theorem MulComm (a b : Nat) : a * b = b * a
:= Induction (calc a * 0  = 0      : MulZero a
                     ...  = 0 * a  : Symm (ZeroMul a))
             (λ (n : Nat) (iH : a * n = n * a),
                calc  a * (n + 1)   =   a * n + a   : MulSucc a n
                              ...   =   n * a + a   : { iH }
                              ...   =   (n + 1) * a : Symm (SuccMul n a))
             b.


Theorem Distribute (a b c : Nat) : a * (b + c) = a * b + a * c
:= Induction (calc 0 * (b + c)   = 0              : ZeroMul (b + c)
                           ...   = 0 + 0          : Trivial
                           ...   = 0 * b + 0      : { Symm (ZeroMul b) }
                           ...   = 0 * b + 0 * c  : { Symm (ZeroMul c) })
             (λ (n : Nat) (iH : n * (b + c) = n * b + n * c),
                calc  (n + 1) * (b + c)  =   n * (b + c) + (b + c)     : SuccMul n (b + c)
                                ...      =   n * b + n * c + (b + c)   : { iH }
                                ...      =   n * b + n * c + b + c     : PlusAssoc (n * b + n * c) b c
                                ...      =   n * b + (n * c + b) + c   : { Symm (PlusAssoc (n * b) (n * c) b) }
                                ...      =   n * b + (b + n * c) + c   : { PlusComm (n * c) b }
                                ...      =   n * b + b + n * c + c     : { PlusAssoc (n * b) b (n * c) }
                                ...      =   (n + 1) * b + n * c + c   : { Symm (SuccMul n b) }
                                ...      =   (n + 1) * b + (n * c + c) : Symm (PlusAssoc ((n + 1) * b) (n * c) c)
                                ...      =   (n + 1) * b + (n + 1) * c : { Symm (SuccMul n c) })
             a.

Theorem Distribute2 (a b c : Nat) : (a + b) * c = a * c + b * c
:= calc (a + b) * c  =  c * (a + b)    :  MulComm (a + b) c
                ...  =  c * a + c * b  :  Distribute c a b
                ...  =  a * c + c * b  :  { MulComm c a }
                ...  =  a * c + b * c  :  { MulComm c b }.

Theorem MulAssoc (a b c : Nat) : a * (b * c) = a * b * c
:= Induction (calc  0 * (b * c)    =  0           : ZeroMul (b * c)
                            ...    =  0 * c       : Symm (ZeroMul c)
                            ...    =  (0 * b) * c : { Symm (ZeroMul b) })
             (λ (n : Nat) (iH : n * (b * c) = n * b * c),
                calc  (n + 1) * (b * c)    =   n * (b * c) + (b * c)   :  SuccMul n (b * c)
                                  ...      =   n * b * c + (b * c)     :  { iH }
                                  ...      =   (n * b + b) * c         :  Symm (Distribute2 (n * b) b c)
                                  ...      =   (n + 1) * b * c         :  { Symm (SuccMul n b) })
             a.

SetOpaque ge true.
SetOpaque lt true.
SetOpaque gt true.
SetOpaque id true.
EndNamespace.