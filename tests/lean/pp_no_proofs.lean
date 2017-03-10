--
open nat

constants (P : ∀ {t:true}, ℕ → Prop) (P0 : @P trivial 0)
          (Ps : ∀ {n}, @P trivial n → @P trivial (succ n))
          (f : Π {n}, @P trivial n → ℕ)

noncomputable definition messy := f (Ps (Ps (Ps (Ps (Ps (Ps P0))))))

#reduce messy
set_option pp.proofs false
#reduce messy
set_option pp.implicit true
#reduce messy
set_option pp.proofs true
#reduce messy
