Import kernel.
Import macros.

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

Axiom SuccNeZero (a : Nat) : a + 1 ≠ 0.
Axiom SuccInj {a b : Nat} (H : a + 1 = b + 1) : a = b
Axiom PlusZero (a : Nat)   : a + 0 = a.
Axiom PlusSucc (a b : Nat) : a + (b + 1) = (a + b) + 1.
Axiom MulZero (a : Nat)    : a * 0 = 0.
Axiom MulSucc (a b : Nat)  : a * (b + 1) = a * b + a.
Axiom LeDef (a b : Nat) : a ≤ b ⇔ ∃ c, a + c = b.
Axiom Induction {P : Nat → Bool} (a : Nat) (H1 : P 0) (H2 : Π (n : Nat) (iH : P n), P (n + 1)) : P a.

Theorem ZeroNeOne : 0 ≠ 1 := Trivial.

Theorem NeZeroPred' (a : Nat) : a ≠ 0 ⇒ ∃ b, b + 1 = a
:= Induction a
    (assume H : 0 ≠ 0, FalseElim (∃ b, b + 1 = 0) H)
    (λ (n : Nat) (iH : n ≠ 0 ⇒ ∃ b, b + 1 = n),
        assume H : n + 1 ≠ 0,
            DisjCases (EM (n = 0))
                      (λ Heq0 : n = 0, ExistsIntro 0 (calc 0 + 1 = n + 1 : { Symm Heq0 }))
                      (λ Hne0 : n ≠ 0,
                          obtain (w : Nat) (Hw : w + 1 = n), from (MP iH Hne0),
                                 ExistsIntro (w + 1) (calc w + 1 + 1 = n + 1 : { Hw }))).

Theorem NeZeroPred {a : Nat} (H : a ≠ 0) : ∃ b, b + 1 = a
:= MP (NeZeroPred' a) H.

Theorem Destruct {B : Bool} {a : Nat} (H1: a = 0 → B) (H2 : Π n, a = n + 1 → B) : B
:= DisjCases (EM (a = 0))
             (λ Heq0 : a = 0, H1 Heq0)
             (λ Hne0 : a ≠ 0, obtain (w : Nat) (Hw : w + 1 = a), from (NeZeroPred Hne0),
                                H2 w (Symm Hw)).

Theorem ZeroPlus (a : Nat) : 0 + a = a
:= Induction a
    (show 0 + 0 = 0, Trivial)
    (λ (n : Nat) (iH : 0 + n = n),
        calc  0 + (n + 1)  =  (0 + n) + 1   :  PlusSucc 0 n
                      ...  =  n + 1         :  { iH }).

Theorem SuccPlus (a b : Nat) : (a + 1) + b = (a + b) + 1
:= Induction b
    (calc (a + 1) + 0   =  a + 1        :  PlusZero (a + 1)
               ...      =  (a + 0) + 1  :  { Symm (PlusZero a) })
    (λ (n : Nat) (iH : (a + 1) + n = (a + n) + 1),
        calc   (a + 1) + (n + 1)   =   ((a + 1) + n) + 1  :  PlusSucc (a + 1) n
                           ...     =   ((a + n) + 1) + 1  :  { iH }
                           ...     =   (a + (n + 1)) + 1  :  { show (a + n) + 1 = a + (n + 1), Symm (PlusSucc a n) }).

Theorem PlusComm (a b : Nat) : a + b = b + a
:= Induction b
    (calc a + 0   = a     : PlusZero a
            ...   = 0 + a : Symm (ZeroPlus a))
    (λ (n : Nat) (iH : a + n = n + a),
        calc   a + (n + 1)   =   (a + n) + 1 : PlusSucc a n
                     ...     =   (n + a) + 1 : { iH }
                     ...     =   (n + 1) + a : Symm (SuccPlus n a)).

Theorem PlusAssoc (a b c : Nat) : a + (b + c) = (a + b) + c
:= Induction a
    (calc 0 + (b + c)  =  b + c        : ZeroPlus (b + c)
                ...    =  (0 + b) + c  : { Symm (ZeroPlus b) })
    (λ (n : Nat) (iH : n + (b + c) = (n + b) + c),
        calc (n + 1) + (b + c)   =    (n + (b + c)) + 1   :  SuccPlus n (b + c)
                          ...    =    ((n + b) + c) + 1   :  { iH }
                          ...    =    ((n + b) + 1) + c   :  Symm (SuccPlus (n + b) c)
                          ...    =    ((n + 1) + b) + c   :  { show (n + b) + 1 = (n + 1) + b,  Symm (SuccPlus n b) }).

Theorem ZeroMul (a : Nat) : 0 * a = 0
:= Induction a
    (show 0 * 0 = 0, Trivial)
    (λ (n : Nat) (iH : 0 * n = 0),
        calc  0 * (n + 1)  =  (0 * n) + 0 : MulSucc 0 n
                      ...  =  0 + 0       : { iH }
                      ...  =  0           : Trivial).

Theorem SuccMul (a b : Nat) : (a + 1) * b = a * b + b
:= Induction b
    (calc (a + 1) * 0   =  0         : MulZero (a + 1)
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
                           ...    = a * (n + 1) + (n + 1)     :  Symm (PlusAssoc (a * (n + 1)) n 1)).

Theorem OneMul (a : Nat) : 1 * a = a
:= Induction a
    (show 1 * 0 = 0, Trivial)
    (λ (n : Nat) (iH : 1 * n = n),
        calc  1 * (n + 1)  =  1 * n + 1 :  MulSucc 1 n
                      ...  =  n + 1     : { iH }).

Theorem MulOne (a : Nat) : a * 1 = a
:= Induction a
    (show 0 * 1 = 0, Trivial)
    (λ (n : Nat) (iH : n * 1 = n),
        calc  (n + 1) * 1  =  n * 1 + 1 : SuccMul n 1
                     ...   =  n + 1     : { iH }).

Theorem MulComm (a b : Nat) : a * b = b * a
:= Induction b
    (calc a * 0  = 0      : MulZero a
            ...  = 0 * a  : Symm (ZeroMul a))
    (λ (n : Nat) (iH : a * n = n * a),
         calc  a * (n + 1)   =   a * n + a   : MulSucc a n
                       ...   =   n * a + a   : { iH }
                       ...   =   (n + 1) * a : Symm (SuccMul n a)).

Theorem Distribute (a b c : Nat) : a * (b + c) = a * b + a * c
:= Induction a
    (calc 0 * (b + c)   = 0              : ZeroMul (b + c)
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
                        ...      =   (n + 1) * b + (n + 1) * c : { Symm (SuccMul n c) }).

Theorem Distribute2 (a b c : Nat) : (a + b) * c = a * c + b * c
:= calc (a + b) * c  =  c * (a + b)    :  MulComm (a + b) c
                ...  =  c * a + c * b  :  Distribute c a b
                ...  =  a * c + c * b  :  { MulComm c a }
                ...  =  a * c + b * c  :  { MulComm c b }.

Theorem MulAssoc (a b c : Nat) : a * (b * c) = a * b * c
:= Induction a
    (calc  0 * (b * c)    =  0           : ZeroMul (b * c)
                   ...    =  0 * c       : Symm (ZeroMul c)
                   ...    =  (0 * b) * c : { Symm (ZeroMul b) })
    (λ (n : Nat) (iH : n * (b * c) = n * b * c),
        calc  (n + 1) * (b * c)    =   n * (b * c) + (b * c)   :  SuccMul n (b * c)
                          ...      =   n * b * c + (b * c)     :  { iH }
                          ...      =   (n * b + b) * c         :  Symm (Distribute2 (n * b) b c)
                          ...      =   (n + 1) * b * c         :  { Symm (SuccMul n b) }).

Theorem PlusInj' (a b c : Nat) : a + b = a + c ⇒ b = c
:= Induction a
    (assume H : 0 + b = 0 + c,
        calc b   =  0 + b   : Symm (ZeroPlus b)
             ... =  0 + c   : H
             ... =  c       : ZeroPlus c)
    (λ (n : Nat) (iH : n + b = n + c ⇒ b = c),
        assume H : n + 1 + b = n + 1 + c,
            let L1 : n + b + 1 = n + c + 1
                   := (calc n + b + 1  =  n + (b + 1)  : Symm (PlusAssoc n b 1)
                               ...     =  n + (1 + b)  : { PlusComm b 1 }
                               ...     =  n + 1 + b    : PlusAssoc n 1 b
                               ...     =  n + 1 + c    : H
                               ...     =  n + (1 + c)  : Symm (PlusAssoc n 1 c)
                               ...     =  n + (c + 1)  : { PlusComm 1 c }
                               ...     =  n + c + 1    : PlusAssoc n c 1),
                L2 : n + b = n + c := SuccInj L1
            in MP iH L2).

Theorem PlusInj {a b c : Nat} (H : a + b = a + c) : b = c
:= MP (PlusInj' a b c) H.

Theorem PlusEq0 {a b : Nat} (H : a + b = 0) : a = 0
:= Destruct (λ H1 : a = 0, H1)
            (λ (n : Nat) (H1 : a = n + 1),
               AbsurdElim (a = 0)
                          H (calc a + b  =  n + 1 + b   : { H1 }
                                    ...  =  n + (1 + b) : Symm (PlusAssoc n 1 b)
                                    ...  =  n + (b + 1) : { PlusComm 1 b }
                                    ...  =  n + b + 1   : PlusAssoc n b 1
                                    ...  ≠  0           : SuccNeZero (n + b)))

Theorem LeIntro {a b c : Nat} (H : a + c = b) : a ≤ b
:= EqMP (Symm (LeDef a b)) (show (∃ x, a + x = b), ExistsIntro c H).

Theorem LeElim {a b : Nat} (H : a ≤ b) : ∃ x, a + x = b
:= EqMP (LeDef a b) H.

Theorem LeRefl (a : Nat) : a ≤ a := LeIntro (PlusZero a).

Theorem LeZero (a : Nat) : 0 ≤ a := LeIntro (ZeroPlus a).

Theorem LeTrans {a b c : Nat} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
:= obtain (w1 : Nat) (Hw1 : a + w1 = b), from (LeElim H1),
   obtain (w2 : Nat) (Hw2 : b + w2 = c), from (LeElim H2),
      LeIntro (calc a + (w1 + w2) =  a + w1 + w2  :  PlusAssoc a w1 w2
                             ...  =  b + w2       :  { Hw1 }
                             ...  =  c            :  Hw2).

Theorem LeInj {a b : Nat} (H : a ≤ b) (c : Nat) : a + c ≤ b + c
:= obtain (w : Nat) (Hw : a + w = b), from (LeElim H),
      LeIntro (calc a + c + w  = a + (c + w)   :  Symm (PlusAssoc a c w)
                         ...   = a + (w + c)   :  { PlusComm c w }
                         ...   = a + w + c     :  PlusAssoc a w c
                         ...   = b + c         :  { Hw }).

Theorem LeAntiSymm {a b : Nat} (H1 : a ≤ b) (H2 : b ≤ a) : a = b
:= obtain (w1 : Nat) (Hw1 : a + w1 = b), from (LeElim H1),
   obtain (w2 : Nat) (Hw2 : b + w2 = a), from (LeElim H2),
    let L1 : w1 + w2 = 0
           := PlusInj (calc a + (w1 + w2) = a + w1 + w2 : { PlusAssoc a w1 w2 }
                                     ...  = b + w2      : { Hw1 }
                                     ...  = a           : Hw2
                                     ...  = a + 0       : Symm (PlusZero a)),
        L2 : w1 = 0  := PlusEq0 L1
    in calc a  =  a  + 0  :  Symm (PlusZero a)
           ... =  a  + w1 : { Symm L2 }
           ... =  b       : Hw1.

SetOpaque ge true.
SetOpaque lt true.
SetOpaque gt true.
SetOpaque id true.
EndNamespace.