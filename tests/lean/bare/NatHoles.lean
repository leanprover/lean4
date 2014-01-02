(*
   Nat library full of "holes".
   We provide only the proof skeletons, and let Lean infer the rest.
*)
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
                calc  0 + (n + 1)  =  (0 + n) + 1   :  PlusSucc _ _
                              ...  =  n + 1         :  { iH })
             a.

Theorem SuccPlus (a b : Nat) : (a + 1) + b = (a + b) + 1
:= Induction (calc (a + 1) + 0   =  a + 1        :  PlusZero _
                        ...      =  (a + 0) + 1  :  { Symm (PlusZero _) })
             (λ (n : Nat) (iH : (a + 1) + n = (a + n) + 1),
                calc   (a + 1) + (n + 1)   =   ((a + 1) + n) + 1  :  PlusSucc _ _
                                   ...     =   ((a + n) + 1) + 1  :  { iH }
                                   ...     =   (a + (n + 1)) + 1  :  { Symm (PlusSucc _ _) })
             b.

Theorem PlusComm (a b : Nat) : a + b = b + a
:= Induction (calc a + 0   = a     : PlusZero a
                     ...   = 0 + a : Symm (ZeroPlus a))
             (λ (n : Nat) (iH : a + n = n + a),
                calc   a + (n + 1)   =   (a + n) + 1 : PlusSucc _ _
                             ...     =   (n + a) + 1 : { iH }
                             ...     =   (n + 1) + a : Symm (SuccPlus _ _))
             b.

Theorem PlusAssoc (a b c : Nat) : a + (b + c) = (a + b) + c
:= Induction (calc 0 + (b + c)  =  b + c        : ZeroPlus _
                         ...    =  (0 + b) + c  : { Symm (ZeroPlus _) })
             (λ (n : Nat) (iH : n + (b + c) = (n + b) + c),
                calc (n + 1) + (b + c)   =    (n + (b + c)) + 1   :  SuccPlus _ _
                                  ...    =    ((n + b) + c) + 1   :  { iH }
                                  ...    =    ((n + b) + 1) + c   :  Symm (SuccPlus _ _)
                                  ...    =    ((n + 1) + b) + c   :  { Symm (SuccPlus _ _) })
             a.

Theorem ZeroMul (a : Nat) : 0 * a = 0
:= Induction (show 0 * 0 = 0, Trivial)
             (λ (n : Nat) (iH : 0 * n = 0),
                calc  0 * (n + 1)  =  (0 * n) + 0 : MulSucc _ _
                              ...  =  0 + 0       : { iH }
                              ...  =  0           : Trivial)
             a.

Theorem SuccMul (a b : Nat) : (a + 1) * b = a * b + b
:= Induction (calc (a + 1) * 0   =  0         : MulZero _
                           ...   =  a * 0     : Symm (MulZero _)
                           ...   =  a * 0 + 0 : Symm (PlusZero _))
             (λ (n : Nat) (iH : (a + 1) * n = a * n + n),
                calc   (a + 1) * (n + 1)  =    (a + 1) * n + (a + 1)  :  MulSucc _ _
                                   ...    = a * n + n + (a + 1)       :  { iH }
                                   ...    = a * n + n + a + 1         :  PlusAssoc _ _ _
                                   ...    = a * n + (n + a) + 1       :  { Symm (PlusAssoc _ _ _) }
                                   ...    = a * n + (a + n) + 1       :  { PlusComm _ _ }
                                   ...    = a * n + a + n + 1         :  { PlusAssoc _ _ _ }
                                   ...    = a * (n + 1) + n + 1       :  { Symm (MulSucc _ _) }
                                   ...    = a * (n + 1) + (n + 1)     :  Symm (PlusAssoc _ _ _))
             b.

Theorem OneMul (a : Nat) : 1 * a = a
:= Induction (show 1 * 0 = 0, Trivial)
             (λ (n : Nat) (iH : 1 * n = n),
                calc  1 * (n + 1)  =  1 * n + 1 :  MulSucc _ _
                              ...  =  n + 1     : { iH })
             a.

Theorem MulOne (a : Nat) : a * 1 = a
:= Induction (show 0 * 1 = 0, Trivial)
             (λ (n : Nat) (iH : n * 1 = n),
                calc  (n + 1) * 1  =  n * 1 + 1 : SuccMul _ _
                             ...   =  n + 1     : { iH })
             a.

Theorem MulComm (a b : Nat) : a * b = b * a
:= Induction (calc a * 0  = 0      : MulZero a
                     ...  = 0 * a  : Symm (ZeroMul a))
             (λ (n : Nat) (iH : a * n = n * a),
                calc  a * (n + 1)   =   a * n + a   : MulSucc _ _
                              ...   =   n * a + a   : { iH }
                              ...   =   (n + 1) * a : Symm (SuccMul _ _))
             b.


Theorem Distribute (a b c : Nat) : a * (b + c) = a * b + a * c
:= Induction (calc 0 * (b + c)   = 0              : ZeroMul _
                           ...   = 0 + 0          : Trivial
                           ...   = 0 * b + 0      : { Symm (ZeroMul _) }
                           ...   = 0 * b + 0 * c  : { Symm (ZeroMul _) })
             (λ (n : Nat) (iH : n * (b + c) = n * b + n * c),
                calc  (n + 1) * (b + c)  =   n * (b + c) + (b + c)     : SuccMul _ _
                                ...      =   n * b + n * c + (b + c)   : { iH }
                                ...      =   n * b + n * c + b + c     : PlusAssoc _ _ _
                                ...      =   n * b + (n * c + b) + c   : { Symm (PlusAssoc _ _ _) }
                                ...      =   n * b + (b + n * c) + c   : { PlusComm _ _ }
                                ...      =   n * b + b + n * c + c     : { PlusAssoc _ _ _ }
                                ...      =   (n + 1) * b + n * c + c   : { Symm (SuccMul _ _) }
                                ...      =   (n + 1) * b + (n * c + c) : Symm (PlusAssoc _ _ _)
                                ...      =   (n + 1) * b + (n + 1) * c : { Symm (SuccMul _ _) })
             a.

Theorem Distribute2 (a b c : Nat) : (a + b) * c = a * c + b * c
:= calc (a + b) * c  =  c * (a + b)    :  MulComm _ _
                ...  =  c * a + c * b  :  Distribute _ _ _
                ...  =  a * c + c * b  :  { MulComm _ _ }
                ...  =  a * c + b * c  :  { MulComm _ _}.

Theorem MulAssoc (a b c : Nat) : a * (b * c) = a * b * c
:= Induction (calc  0 * (b * c)    =  0           : ZeroMul _
                            ...    =  0 * c       : Symm (ZeroMul _)
                            ...    =  (0 * b) * c : { Symm (ZeroMul _) })
             (λ (n : Nat) (iH : n * (b * c) = n * b * c),
                calc  (n + 1) * (b * c)    =   n * (b * c) + (b * c)   :  SuccMul _ _
                                  ...      =   n * b * c + (b * c)     :  { iH }
                                  ...      =   (n * b + b) * c         :  Symm (Distribute2 _ _ _)
                                  ...      =   (n + 1) * b * c         :  { Symm (SuccMul _ _) })
             a.

SetOpaque ge true.
SetOpaque lt true.
SetOpaque gt true.
SetOpaque id true.
EndNamespace.