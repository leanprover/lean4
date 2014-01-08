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

axiom succ::nz (a : Nat) : a + 1 ≠ 0
axiom succ::inj {a b : Nat} (H : a + 1 = b + 1) : a = b
axiom add::zeror (a : Nat)   : a + 0 = a
axiom add::succr (a b : Nat) : a + (b + 1) = (a + b) + 1
axiom mul::zeror (a : Nat)    : a * 0 = 0
axiom mul::succr (a b : Nat)  : a * (b + 1) = a * b + a
axiom le::def (a b : Nat) : a ≤ b = ∃ c, a + c = b
axiom induction {P : Nat → Bool} (a : Nat) (H1 : P 0) (H2 : ∀ (n : Nat) (iH : P n), P (n + 1)) : P a

theorem pred::nz {a : Nat} : a ≠ 0 → ∃ b, b + 1 = a
:= induction a
    (λ H : 0 ≠ 0, false::elim (∃ b, b + 1 = 0) H)
    (λ (n : Nat) (iH : n ≠ 0 → ∃ b, b + 1 = n) (H : n + 1 ≠ 0),
       or::elim (em (n = 0))
           (λ Heq0 : n = 0, exists::intro 0 (calc 0 + 1 = n + 1 : { symm Heq0 }))
           (λ Hne0 : n ≠ 0,
                 obtain (w : Nat) (Hw : w + 1 = n), from (iH Hne0),
                    exists::intro (w + 1) (calc w + 1 + 1 = n + 1 : { Hw })))

theorem discriminate {B : Bool} {a : Nat} (H1: a = 0 → B) (H2 : ∀ n, a = n + 1 → B) : B
:= or::elim (em (a = 0))
             (λ Heq0 : a = 0, H1 Heq0)
             (λ Hne0 : a ≠ 0, obtain (w : Nat) (Hw : w + 1 = a), from (pred::nz Hne0),
                  H2 w (symm Hw))

theorem add::zerol (a : Nat) : 0 + a = a
:= induction a
    (have 0 + 0 = 0 : trivial)
    (λ (n : Nat) (iH : 0 + n = n),
        calc  0 + (n + 1)  =  (0 + n) + 1   :  add::succr 0 n
                    ...    =  n + 1         :  { iH })

theorem add::succl (a b : Nat) : (a + 1) + b = (a + b) + 1
:= induction b
    (calc (a + 1) + 0   =  a + 1        :  add::zeror (a + 1)
                  ...   =  (a + 0) + 1  :  { symm (add::zeror a) })
    (λ (n : Nat) (iH : (a + 1) + n = (a + n) + 1),
        calc   (a + 1) + (n + 1)   =   ((a + 1) + n) + 1  :  add::succr (a + 1) n
                              ...  =   ((a + n) + 1) + 1  :  { iH }
                              ...  =   (a + (n + 1)) + 1  :  { have (a + n) + 1 = a + (n + 1) : symm (add::succr a n) })

theorem add::comm (a b : Nat) : a + b = b + a
:= induction b
    (calc a + 0   = a     : add::zeror a
            ...   = 0 + a : symm (add::zerol a))
    (λ (n : Nat) (iH : a + n = n + a),
        calc   a + (n + 1)   =   (a + n) + 1 : add::succr a n
                       ...   =   (n + a) + 1 : { iH }
                       ...   =   (n + 1) + a : symm (add::succl n a))

theorem add::assoc (a b c : Nat) : a + (b + c) = (a + b) + c
:= induction a
    (calc 0 + (b + c)  =  b + c        : add::zerol (b + c)
                  ...  =  (0 + b) + c  : { symm (add::zerol b) })
    (λ (n : Nat) (iH : n + (b + c) = (n + b) + c),
        calc (n + 1) + (b + c)   =    (n + (b + c)) + 1   :  add::succl n (b + c)
                          ...    =    ((n + b) + c) + 1   :  { iH }
                          ...    =    ((n + b) + 1) + c   :  symm (add::succl (n + b) c)
                          ...    =    ((n + 1) + b) + c   :  { have (n + b) + 1 = (n + 1) + b :  symm (add::succl n b) })

theorem mul::zerol (a : Nat) : 0 * a = 0
:= induction a
    (have 0 * 0 = 0 : trivial)
    (λ (n : Nat) (iH : 0 * n = 0),
        calc  0 * (n + 1)  =  (0 * n) + 0 : mul::succr 0 n
                      ...  =  0 + 0       : { iH }
                      ...  =  0           : trivial)

theorem mul::succl (a b : Nat) : (a + 1) * b = a * b + b
:= induction b
    (calc (a + 1) * 0   =  0         : mul::zeror (a + 1)
                   ...  =  a * 0     : symm (mul::zeror a)
                   ...  =  a * 0 + 0 : symm (add::zeror (a * 0)))
    (λ (n : Nat) (iH : (a + 1) * n = a * n + n),
        calc   (a + 1) * (n + 1)  =    (a + 1) * n + (a + 1)  :  mul::succr (a + 1) n
                            ...   = a * n + n + (a + 1)       :  { iH }
                            ...   = a * n + n + a + 1         :  add::assoc (a * n + n) a 1
                            ...   = a * n + (n + a) + 1       :  { have  a * n + n + a = a * n + (n + a) : symm (add::assoc (a * n) n a) }
                            ...   = a * n + (a + n) + 1       :  { add::comm n a }
                            ...   = a * n + a + n + 1         :  { add::assoc (a * n) a n }
                            ...   = a * (n + 1) + n + 1       :  { symm (mul::succr a n) }
                            ...   = a * (n + 1) + (n + 1)     :  symm (add::assoc (a * (n + 1)) n 1))

theorem mul::onel (a : Nat) : 1 * a = a
:= induction a
    (have 1 * 0 = 0 : trivial)
    (λ (n : Nat) (iH : 1 * n = n),
        calc  1 * (n + 1)  =  1 * n + 1 :  mul::succr 1 n
                      ...  =  n + 1     : { iH })

theorem mul::oner (a : Nat) : a * 1 = a
:= induction a
    (have 0 * 1 = 0 : trivial)
    (λ (n : Nat) (iH : n * 1 = n),
        calc  (n + 1) * 1  =  n * 1 + 1 : mul::succl n 1
                      ...  =  n + 1     : { iH })

theorem mul::comm (a b : Nat) : a * b = b * a
:= induction b
    (calc a * 0  = 0      : mul::zeror a
            ...  = 0 * a  : symm (mul::zerol a))
    (λ (n : Nat) (iH : a * n = n * a),
         calc  a * (n + 1)   =   a * n + a   : mul::succr a n
                       ...   =   n * a + a   : { iH }
                       ...   =   (n + 1) * a : symm (mul::succl n a))

theorem distributer (a b c : Nat) : a * (b + c) = a * b + a * c
:= induction a
    (calc 0 * (b + c)   = 0              : mul::zerol (b + c)
                  ...   = 0 + 0          : trivial
                  ...   = 0 * b + 0      : { symm (mul::zerol b) }
                  ...   = 0 * b + 0 * c  : { symm (mul::zerol c) })
    (λ (n : Nat) (iH : n * (b + c) = n * b + n * c),
        calc  (n + 1) * (b + c)  =   n * (b + c) + (b + c)     : mul::succl n (b + c)
                            ...  =   n * b + n * c + (b + c)   : { iH }
                            ...  =   n * b + n * c + b + c     : add::assoc (n * b + n * c) b c
                            ...  =   n * b + (n * c + b) + c   : { symm (add::assoc (n * b) (n * c) b) }
                            ...  =   n * b + (b + n * c) + c   : { add::comm (n * c) b }
                            ...  =   n * b + b + n * c + c     : { add::assoc (n * b) b (n * c) }
                            ...  =   (n + 1) * b + n * c + c   : { symm (mul::succl n b) }
                            ...  =   (n + 1) * b + (n * c + c) : symm (add::assoc ((n + 1) * b) (n * c) c)
                            ...  =   (n + 1) * b + (n + 1) * c : { symm (mul::succl n c) })

theorem distributel (a b c : Nat) : (a + b) * c = a * c + b * c
:= calc (a + b) * c  =  c * (a + b)    :  mul::comm (a + b) c
                ...  =  c * a + c * b  :  distributer c a b
                ...  =  a * c + c * b  :  { mul::comm c a }
                ...  =  a * c + b * c  :  { mul::comm c b }

theorem mul::assoc (a b c : Nat) : a * (b * c) = a * b * c
:= induction a
    (calc  0 * (b * c)    =  0           : mul::zerol (b * c)
                   ...    =  0 * c       : symm (mul::zerol c)
                   ...    =  (0 * b) * c : { symm (mul::zerol b) })
    (λ (n : Nat) (iH : n * (b * c) = n * b * c),
        calc  (n + 1) * (b * c)    =   n * (b * c) + (b * c)   :  mul::succl n (b * c)
                            ...    =   n * b * c + (b * c)     :  { iH }
                            ...    =   (n * b + b) * c         :  symm (distributel (n * b) b c)
                            ...    =   (n + 1) * b * c         :  { symm (mul::succl n b) })

theorem add::inj {a b c : Nat} : a + b = a + c → b = c
:= induction a
    (λ H : 0 + b = 0 + c,
        calc b   =  0 + b   : symm (add::zerol b)
           ...   =  0 + c   : H
           ...   =  c       : add::zerol c)
    (λ (n : Nat) (iH : n + b = n + c → b = c) (H : n + 1 + b = n + 1 + c),
       let L1 : n + b + 1 = n + c + 1
           := (calc n + b + 1  =  n + (b + 1)  : symm (add::assoc n b 1)
                          ...  =  n + (1 + b)  : { add::comm b 1 }
                          ...  =  n + 1 + b    : add::assoc n 1 b
                          ...  =  n + 1 + c    : H
                          ...  =  n + (1 + c)  : symm (add::assoc n 1 c)
                          ...  =  n + (c + 1)  : { add::comm 1 c }
                          ...  =  n + c + 1    : add::assoc n c 1),
           L2 : n + b = n + c := succ::inj L1
       in iH L2)

theorem add::eqz {a b : Nat} (H : a + b = 0) : a = 0
:= discriminate
     (λ H1 : a = 0, H1)
     (λ (n : Nat) (H1 : a = n + 1),
         absurd::elim (a = 0)
            H (calc a + b  =  n + 1 + b   : { H1 }
                   ...  =  n + (1 + b) : symm (add::assoc n 1 b)
                   ...  =  n + (b + 1) : { add::comm 1 b }
                   ...  =  n + b + 1   : add::assoc n b 1
                   ...  ≠  0           : succ::nz (n + b)))

theorem le::intro {a b c : Nat} (H : a + c = b) : a ≤ b
:= (symm (le::def a b)) ◂ (have (∃ x, a + x = b) : exists::intro c H)

theorem le::elim {a b : Nat} (H : a ≤ b) : ∃ x, a + x = b
:= (le::def a b) ◂ H

theorem le::refl (a : Nat) : a ≤ a := le::intro (add::zeror a)

theorem le::zero (a : Nat) : 0 ≤ a := le::intro (add::zerol a)


theorem le::trans {a b c : Nat} (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
:= obtain (w1 : Nat) (Hw1 : a + w1 = b), from (le::elim H1),
   obtain (w2 : Nat) (Hw2 : b + w2 = c), from (le::elim H2),
      le::intro (calc a + (w1 + w2) =  a + w1 + w2  :  add::assoc a w1 w2
                                ... =  b + w2         :  { Hw1 }
                                ... =  c              :  Hw2)

theorem le::add {a b : Nat} (H : a ≤ b) (c : Nat) : a + c ≤ b + c
:= obtain (w : Nat) (Hw : a + w = b), from (le::elim H),
      le::intro (calc a + c + w  = a + (c + w) :  symm (add::assoc a c w)
                            ...  = a + (w + c)   :  { add::comm c w }
                            ...  = a + w + c     :  add::assoc a w c
                            ...  = b + c         :  { Hw })

theorem le::antisym {a b : Nat} (H1 : a ≤ b) (H2 : b ≤ a) : a = b
:= obtain (w1 : Nat) (Hw1 : a + w1 = b), from (le::elim H1),
   obtain (w2 : Nat) (Hw2 : b + w2 = a), from (le::elim H2),
    let L1 : w1 + w2 = 0
           := add::inj (calc a + (w1 + w2) = a + w1 + w2 : { add::assoc a w1 w2 }
                                       ... = b + w2        : { Hw1 }
                                       ... = a             : Hw2
                                       ... = a + 0         : symm (add::zeror a)),
        L2 : w1 = 0  := add::eqz L1
    in calc a  =  a  + 0  : symm (add::zeror a)
          ...  =  a  + w1 : { symm L2 }
          ...  =  b       : Hw1

set::opaque ge true
set::opaque lt true
set::opaque gt true
set::opaque id true
end