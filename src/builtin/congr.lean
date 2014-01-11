-- Congruence theorems for contextual simplification

-- Simplify a → b, by first simplifying a to c using the fact that ¬ b is true, and then
-- b to d using the fact that c is true
theorem imp_congrr {a b c d : Bool} (H_ac : ∀ (H_nb : ¬ b), a = c) (H_bd : ∀ (H_c : c), b = d) : (a → b) = (c → d)
:= or_elim (em b)
      (λ H_b : b,
          or_elim (em c)
             (λ H_c : c,
                 calc (a → b) = (a → true)  : { eqt_intro H_b }
                          ...  = true          : imp_truer a
                          ...  = (c → true)  :  symm (imp_truer c)
                          ...  = (c → b)     : { symm (eqt_intro H_b) }
                          ...  = (c → d)     : { H_bd H_c })
             (λ H_nc : ¬ c,
                 calc (a → b) = (a → true)   : { eqt_intro H_b }
                          ...  = true          : imp_truer a
                          ...  = (false → d)  : symm (imp_falsel d)
                          ...  = (c → d)      : { symm (eqf_intro H_nc) }))
      (λ H_nb : ¬ b,
          or_elim (em c)
             (λ H_c : c,
                 calc (a → b) = (c → b)  : { H_ac H_nb }
                          ...  = (c → d)  : { H_bd H_c })
             (λ H_nc : ¬ c,
                 calc (a → b) = (c → b) : { H_ac H_nb }
                          ...  = (false → b) : { eqf_intro H_nc }
                          ...  = true         : imp_falsel b
                          ...  = (false → d) : symm (imp_falsel d)
                          ...  = (c → d)  :  { symm (eqf_intro H_nc) }))


-- Simplify a → b, by first simplifying b to d using the fact that a is true, and then
-- b to d using the fact that ¬ d is true.
-- This kind of congruence seems to be useful in very rare cases.
theorem imp_congrl {a b c d : Bool} (H_ac : ∀ (H_nd : ¬ d), a = c) (H_bd : ∀ (H_a : a), b = d) : (a → b) = (c → d)
:= or_elim (em a)
      (λ H_a : a,
          or_elim (em d)
             (λ H_d : d,
                 calc (a → b) = (a → d)    : { H_bd H_a }
                          ...  = (a → true) : { eqt_intro H_d }
                          ...  = true         :  imp_truer a
                          ...  = (c → true)  : symm (imp_truer c)
                          ...  = (c → d)     : { symm (eqt_intro H_d) })
             (λ H_nd : ¬ d,
                 calc (a → b) = (c → b)   : { H_ac H_nd }
                          ...  = (c → d)   : { H_bd H_a }))
      (λ H_na : ¬ a,
          or_elim (em d)
             (λ H_d : d,
                 calc (a → b) = (false → b)   :  { eqf_intro H_na }
                          ...  = true           : imp_falsel b
                          ...  = (c → true)    : symm (imp_truer c)
                          ...  = (c → d)       : { symm (eqt_intro H_d) })
             (λ H_nd : ¬ d,
                 calc (a → b) = (false → b) : { eqf_intro H_na }
                          ...  = true         : imp_falsel b
                          ...  = (false → d) : symm (imp_falsel d)
                          ...  = (a → d)  :  { symm (eqf_intro H_na) }
                          ...  = (c → d)  :  { H_ac H_nd }))

-- (Common case) simplify a to c, and then b to d using the fact that c is true
theorem imp_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_c : c), b = d) : (a → b) = (c → d)
:= imp_congrr (λ H, H_ac) H_bd

-- In the following theorems we are using the fact that a ∨ b is defined as ¬ a → b
set_opaque or false
theorem or_congrr {a b c d : Bool} (H_ac : ∀ (H_nb : ¬ b), a = c) (H_bd : ∀ (H_nc : ¬ c), b = d) : (a ∨ b) = (c ∨ d)
:= imp_congrr (λ H_nb : ¬ b, congr2 not (H_ac H_nb)) H_bd
theorem or_congrl {a b c d : Bool} (H_ac : ∀ (H_nd : ¬ d), a = c) (H_bd : ∀ (H_na : ¬ a), b = d) : (a ∨ b) = (c ∨ d)
:= imp_congrl (λ H_nd : ¬ d, congr2 not (H_ac H_nd)) H_bd
set_opaque or true
-- (Common case) simplify a to c, and then b to d using the fact that ¬ c is true
theorem or_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_nc : ¬ c), b = d) : (a ∨ b) = (c ∨ d)
:= or_congrr (λ H, H_ac) H_bd

-- In the following theorems we are using the fact hat a ∧ b is defined as ¬ (a → ¬ b)
set_opaque and false
theorem and_congrr {a b c d : Bool} (H_ac : ∀ (H_b : b), a = c) (H_bd : ∀ (H_c : c), b = d) : (a ∧ b) = (c ∧ d)
:= congr2 not (imp_congrr (λ (H_nnb : ¬ ¬ b), H_ac (not_not_elim H_nnb)) (λ H_c : c, congr2 not (H_bd H_c)))
theorem and_congrl {a b c d : Bool} (H_ac : ∀ (H_d : d), a = c) (H_bd : ∀ (H_a : a), b = d) : (a ∧ b) = (c ∧ d)
:= congr2 not (imp_congrl (λ (H_nnd : ¬ ¬ d), H_ac (not_not_elim H_nnd)) (λ H_a : a, congr2 not (H_bd H_a)))
set_opaque and true
-- (Common case) simplify a to c, and then b to d using the fact that c is true
theorem and_congr {a b c d : Bool} (H_ac : a = c) (H_bd : ∀ (H_c : c), b = d) : (a ∧ b) = (c ∧ d)
:= and_congrr (λ H, H_ac) H_bd


-- Perhaps, we should move the following theorem to the if_then_else module
import if_then_else

-- Simplify the then branch using the fact that c is true, and the else branch that c is false
theorem if_congr {A : TypeU} {b c : Bool} {x y u v : A} (H_bc : b = c) (H_xu : ∀ (H_c : c), x = u) (H_yv : ∀ (H_nc : ¬ c), y = v) :
        (if b then x else y) = (if c then u else v)
:= or_elim (em c)
     (λ H_c : c, calc (if b then x else y) = (if c then x else y)    : { H_bc }
                                      ...  = (if true then x else y) : { eqt_intro H_c }
                                      ...  = x                       : if_true _ _
                                      ...  = u                       : H_xu H_c
                                      ...  = (if true then u else v) : symm (if_true _ _)
                                      ...  = (if c then u else v)    : { symm (eqt_intro H_c) })
     (λ H_nc : ¬ c, calc (if b then x else y) = (if c then x else y)     : { H_bc }
                                         ...  = (if false then x else y) : { eqf_intro H_nc }
                                         ...  = y                        : if_false _ _
                                         ...  = v                        : H_yv H_nc
                                         ...  = (if false then u else v) : symm (if_false _ _)
                                         ...  = (if c then u else v)     : { symm (eqf_intro H_nc) })
