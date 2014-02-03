import tactic
using Nat

-- Manual proof using symmetry, transitivity, distributivity and 1*x=x.
theorem T1 (a b c : Nat)
           (H1 : a = b + c)    -- First hypothesis
           (H2 : b = c)        -- Second hypothesis
           : a = 2*c           -- Conclusion
:= calc a   =   b + c    : H1
       ...  =   c + c    : { H2 }
       ...  =  1*c + 1*c : { symm (mul_onel c) }
       ...  =  (1 + 1)*c : symm (distributel 1 1 c)
       ...  =  2*c       : refl (2*c)

add_rewrite mul_onel

-- The simplifier can already compress the proof above.
theorem T2 (a b c : Nat)
           (H1 : a = b + c)    -- first hypothesis
           (H2 : b = c)        -- second hypothesis
           : a = 2*c
:= calc a   =  1*c + 1*c : by simp
       ...  =  (1 + 1)*c : symm (distributel 1 1 c)
       ...  =  2*c       : refl (2*c)
