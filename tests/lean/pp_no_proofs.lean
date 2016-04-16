import data.nat
open nat

constants (P : ∀ {t:true}, ℕ → Prop) (P0 : @P trivial 0)
          (Ps : ∀ {n}, @P trivial n → @P trivial (succ n))
          (f : Π {n}, @P trivial n → ℕ)

definition messy := f (Ps (Ps (Ps (Ps (Ps (Ps P0))))))

eval messy
set_option pp.proofs false
eval messy
set_option pp.implicit true
eval messy
set_option pp.proofs true
eval messy
