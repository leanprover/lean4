import kernel
import macros

variable Nat : Type
alias ℕ : Nat

namespace Nat
builtin numeral

builtin add : Nat → Nat → Nat
infixl 65 +  : add

builtin mul : Nat → Nat → Nat
infixl 70 *  : mul

builtin le  : Nat → Nat → Bool
infix  50 <= : le
infix  50 ≤  : le

definition ge (a b : Nat) := b ≤ a
infix 50 >= : ge
infix 50 ≥  : ge

definition lt (a b : Nat) := ¬ (a ≥ b)
infix 50 <  : lt

definition gt (a b : Nat) := ¬ (a ≤ b)
infix 50 >  : gt

definition id (a : Nat) := a
notation 55 | _ | : id

axiom SuccNeZero (a : Nat) : a + 1 ≠ 0
axiom SuccInj {a b : Nat} (H : a + 1 = b + 1) : a = b
axiom PlusZero (a : Nat)   : a + 0 = a
axiom PlusSucc (a b : Nat) : a + (b + 1) = (a + b) + 1
axiom MulZero (a : Nat)    : a * 0 = 0
axiom MulSucc (a b : Nat)  : a * (b + 1) = a * b + a
axiom LeDef (a b : Nat) : a ≤ b ⇔ ∃ c, a + c = b
axiom Induction {P : Nat → Bool} (a : Nat) (H1 : P 0) (H2 : Π (n : Nat) (iH : P n), P (n + 1)) : P a

theorem ZeroNeOne : 0 ≠ 1 := Trivial

theorem NeZeroPred' (a : Nat) : a ≠ 0 ⇒ ∃ b, b + 1 = a
:= Induction a
    (Assume H : 0 ≠ 0, FalseElim (∃ b, b + 1 = 0) H)
    (λ (n : Nat) (iH : n ≠ 0 ⇒ ∃ b, b + 1 = n),
        Assume H : n + 1 ≠ 0,
            DisjCases (EM (n = 0))
                      (λ Heq0 : n = 0, ExistsIntro 0 (calc 0 + 1 = n + 1 : { Symm Heq0 }))
                      (λ Hne0 : n ≠ 0,
                          Obtain (w : Nat) (Hw : w + 1 = n), from (MP iH Hne0),
                                 ExistsIntro (w + 1) (calc w + 1 + 1 = n + 1 : { Hw })))

theorem NeZeroPred {a : Nat} (H : a ≠ 0) : ∃ b, b + 1 = a
:= MP (NeZeroPred' a) H

theorem Destruct {B : Bool} {a : Nat} (H1: a = 0 → B) (H2 : Π n, a = n + 1 → B) : B
:= DisjCases (EM (a = 0))
             (λ Heq0 : a = 0, H1 Heq0)
             (λ Hne0 : a ≠ 0, Obtain (w : Nat) (Hw : w + 1 = a), from (NeZeroPred Hne0),
                                H2 w (Symm Hw))

theorem ZeroPlus (a : Nat) : 0 + a = a
:= Induction a
    (have 0 + 0 = 0 : Trivial)
    (λ (n : Nat) (iH : 0 + n = n),
        calc  0 + (n + 1)  =  (0 + n) + 1   :  PlusSucc 0 n
                    ...    =  n + 1         :  { iH })

theorem SuccPlus (a b : Nat) : (a + 1) + b = (a + b) + 1
:= Induction b
    (calc (a + 1) + 0   =  a + 1        :  PlusZero (a + 1)
                  ...   =  (a + 0) + 1  :  { Symm (PlusZero a) })
    (λ (n : Nat) (iH : (a + 1) + n = (a + n) + 1),
        calc   (a + 1) + (n + 1)   =   ((a + 1) + n) + 1  :  PlusSucc (a + 1) n
                              ...  =   ((a + n) + 1) + 1  :  { iH }
                              ...  =   (a + (n + 1)) + 1  :  { have (a + n) + 1 = a + (n + 1) : Symm (PlusSucc a n) })

theorem PlusComm (a b : Nat) : a + b = b + a
:= Induction b
    (calc a + 0   = a     : PlusZero a
            ...   = 0 + a : Symm (ZeroPlus a))
    (λ (n : Nat) (iH : a + n = n + a),
        calc   a + (n + 1)   =   (a + n) + 1 : PlusSucc a n
                       ...   =   (n + a) + 1 : { iH }
                       ...   =   (n + 1) + a : Symm (SuccPlus n a))

theorem PlusAssoc (a b c : Nat) : a + (b + c) = (a + b) + c
:= Induction a
    (calc 0 + (b + c)  =  b + c        : ZeroPlus (b + c)
                  ...  =  (0 + b) + c  : { Symm (ZeroPlus b) })
    (λ (n : Nat) (iH : n + (b + c) = (n + b) + c),
        calc (n + 1) + (b + c)   =    (n + (b + c)) + 1   :  SuccPlus n (b + c)
                          ...    =    ((n + b) + c) + 1   :  { iH }
                          ...    =    ((n + b) + 1) + c   :  Symm (SuccPlus (n + b) c)
                          ...    =    ((n + 1) + b) + c   :  { have (n + b) + 1 = (n + 1) + b :  Symm (SuccPlus n b) })

theorem ZeroMul (a : Nat) : 0 * a = 0
:= Induction a
    (have 0 * 0 = 0 : Trivial)
    (λ (n : Nat) (iH : 0 * n = 0),
        calc  0 * (n + 1)  =  (0 * n) + 0 : MulSucc 0 n
                      ...  =  0 + 0       : { iH }
                      ...  =  0           : Trivial)

theorem SuccMul (a b : Nat) : (a + 1) * b = a * b + b
:= Induction b
    (calc (a + 1) * 0   =  0         : MulZero (a + 1)
                   ...  =  a * 0     : Symm (MulZero a)
                   ...  =  a * 0 + 0 : Symm (PlusZero (a * 0)))
    (λ (n : Nat) (iH : (a + 1) * n = a * n + n),
        calc   (a + 1) * (n + 1)  =    (a + 1) * n + (a + 1)  :  MulSucc (a + 1) n
                            ...   = a * n + n + (a + 1)       :  { iH }
                            ...   = a * n + n + a + 1         :  PlusAssoc (a * n + n) a 1
                            ...   = a * n + (n + a) + 1       :  { have  a * n + n + a = a * n + (n + a) : Symm (PlusAssoc (a * n) n a) }
                            ...   = a * n + (a + n) + 1       :  { PlusComm n a }
                            ...   = a * n + a + n + 1         :  { PlusAssoc (a * n) a n }
                            ...   = a * (n + 1) + n + 1       :  { Symm (MulSucc a n) }
                            ...   = a * (n + 1) + (n + 1)     :  Symm (PlusAssoc (a * (n + 1)) n 1))

theorem OneMul (a : Nat) : 1 * a = a
:= Induction a
    (have 1 * 0 = 0 : Trivial)
    (λ (n : Nat) (iH : 1 * n = n),
        calc  1 * (n + 1)  =  1 * n + 1 :  MulSucc 1 n
                      ...  =  n + 1     : { iH })

theorem MulOne (a : Nat) : a * 1 = a
:= Induction a
    (have 0 * 1 = 0 : Trivial)
    (λ (n : Nat) (iH : n * 1 = n),
        calc  (n + 1) * 1  =  n * 1 + 1 : SuccMul n 1
                      ...  =  n + 1     : { iH })

theorem MulComm (a b : Nat) : a * b = b * a
:= Induction b
    (calc a * 0  = 0      : MulZero a
            ...  = 0 * a  : Symm (ZeroMul a))
    (λ (n : Nat) (iH : a * n = n * a),
         calc  a * (n + 1)   =   a * n + a   : MulSucc a n
                       ...   =   n * a + a   : { iH }
                       ...   =   (n + 1) * a : Symm (SuccMul n a))

theorem Distribute (a b c : Nat) : a * (b + c) = a * b + a * c
:= Induction a
    (calc 0 * (b + c)   = 0              : ZeroMul (b + c)
                  ...   = 0 + 0          : Trivial
                  ...   = 0 * b + 0      : { Symm (ZeroMul b) }
                  ...   = 0 * b + 0 * c  : { Symm (ZeroMul c) })
    (λ (n : Nat) (iH : n * (b + c) = n * b + n * c),
        calc  (n + 1) * (b + c)  =   n * (b + c) + (b + c)     : SuccMul n (b + c)
                            ...  =   n * b + n * c + (b + c)   : { iH }
                            ...  =   n * b + n * c + b + c     : PlusAssoc (n * b + n * c) b c
                            ...  =   n * b + (n * c + b) + c   : { Symm (PlusAssoc (n * b) (n * c) b) }
                            ...  =   n * b + (b + n * c) + c   : { PlusComm (n * c) b }
                            ...  =   n * b + b + n * c + c     : { PlusAssoc (n * b) b (n * c) }
                            ...  =   (n + 1) * b + n * c + c   : { Symm (SuccMul n b) }
                            ...  =   (n + 1) * b + (n * c + c) : Symm (PlusAssoc ((n + 1) * b) (n * c) c)
                            ...  =   (n + 1) * b + (n + 1) * c : { Symm (SuccMul n c) })

theorem Distribute2 (a b c : Nat) : (a + b) * c = a * c + b * c
:= calc (a + b) * c  =  c * (a + b)    :  MulComm (a + b) c
                ...  =  c * a + c * b  :  Distribute c a b
                ...  =  a * c + c * b  :  { MulComm c a }
                ...  =  a * c + b * c  :  { MulComm c b }

theorem MulAssoc (a b c : Nat) : a * (b * c) = a * b * c
:= Induction a
    (calc  0 * (b * c)    =  0           : ZeroMul (b * c)
                   ...    =  0 * c       : Symm (ZeroMul c)
                   ...    =  (0 * b) * c : { Symm (ZeroMul b) })
    (λ (n : Nat) (iH : n * (b * c) = n * b * c),
        calc  (n + 1) * (b * c)    =   n * (b * c) + (b * c)   :  SuccMul n (b * c)
                            ...    =   n * b * c + (b * c)     :  { iH }
                            ...    =   (n * b + b) * c         :  Symm (Distribute2 (n * b) b c)
                            ...    =   (n + 1) * b * c         :  { Symm (SuccMul n b) })

theorem PlusInj' (a b c : Nat) : a + b = a + c ⇒ b = c
:= Induction a
    (Assume H : 0 + b = 0 + c,
        calc b   =  0 + b   : Symm (ZeroPlus b)
           ...   =  0 + c   : H
           ...   =  c       : ZeroPlus c)
    (λ (n : Nat) (iH : n + b = n + c ⇒ b = c),
        Assume H : n + 1 + b = n + 1 + c,
            let L1 : n + b + 1 = n + c + 1
                   := (calc n + b + 1  =  n + (b + 1)  : Symm (PlusAssoc n b 1)
                                  ...  =  n + (1 + b)  : { PlusComm b 1 }
                                  ...  =  n + 1 + b    : PlusAssoc n 1 b
                                  ...  =  n + 1 + c    : H
                                  ...  =  n + (1 + c)  : Symm (PlusAssoc n 1 c)
                                  ...  =  n + (c + 1)  : { PlusComm 1 c }
                                  ...  =  n + c + 1    : PlusAssoc n c 1),
                L2 : n + b = n + c := SuccInj L1
            in MP iH L2)

theorem PlusInj {a b c : Nat} (H : a + b = a + c) : b = c
:= MP (PlusInj' a b c) H

theorem PlusEq0 {a b : Nat} (H : a + b = 0) : a = 0
:= Destruct (λ H1 : a = 0, H1)
            (λ (n : Nat) (H1 : a = n + 1),
               AbsurdElim (a = 0)
                          H (calc a + b  =  n + 1 + b   : { H1 }
                                    ...  =  n + (1 + b) : Symm (PlusAssoc n 1 b)
                                    ...  =  n + (b + 1) : { PlusComm 1 b }
                                    ...  =  n + b + 1   : PlusAssoc n b 1
                                    ...  ≠  0           : SuccNeZero (n + b)))

theorem LeIntro {a b c : Nat} (H : a + c = b) : a ≤ b
:= EqMP (Symm (LeDef a b)) (have (∃ x, a + x = b) : ExistsIntro c H)

theorem LeElim {a b : Nat} (H : a ≤ b) : ∃ x, a + x = b
:= EqMP (LeDef a b) H

theorem LeRefl (a : Nat) : a ≤ a := LeIntro (PlusZero a)

theorem LeZero (a : Nat) : 0 ≤ a := LeIntro (ZeroPlus a)

theorem LeTrans {a b c : Nat} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
:= Obtain (w1 : Nat) (Hw1 : a + w1 = b), from (LeElim H1),
   Obtain (w2 : Nat) (Hw2 : b + w2 = c), from (LeElim H2),
      LeIntro (calc a + (w1 + w2) =  a + w1 + w2  :  PlusAssoc a w1 w2
                              ... =  b + w2       :  { Hw1 }
                              ... =  c            :  Hw2)

theorem LeInj {a b : Nat} (H : a ≤ b) (c : Nat) : a + c ≤ b + c
:= Obtain (w : Nat) (Hw : a + w = b), from (LeElim H),
      LeIntro (calc a + c + w  = a + (c + w)   :  Symm (PlusAssoc a c w)
                          ...  = a + (w + c)   :  { PlusComm c w }
                          ...  = a + w + c     :  PlusAssoc a w c
                          ...  = b + c         :  { Hw })

theorem LeAntiSymm {a b : Nat} (H1 : a ≤ b) (H2 : b ≤ a) : a = b
:= Obtain (w1 : Nat) (Hw1 : a + w1 = b), from (LeElim H1),
   Obtain (w2 : Nat) (Hw2 : b + w2 = a), from (LeElim H2),
    let L1 : w1 + w2 = 0
           := PlusInj (calc a + (w1 + w2) = a + w1 + w2 : { PlusAssoc a w1 w2 }
                                      ... = b + w2      : { Hw1 }
                                      ... = a           : Hw2
                                      ... = a + 0       : Symm (PlusZero a)),
        L2 : w1 = 0  := PlusEq0 L1
    in calc a  =  a  + 0  :  Symm (PlusZero a)
          ...  =  a  + w1 : { Symm L2 }
          ...  =  b       : Hw1

setopaque ge true
setopaque lt true
setopaque gt true
setopaque id true
end