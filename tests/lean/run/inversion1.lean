import data.fin
open nat

namespace fin

  definition z_cases_on2 (C : fin zero → Type) (p : fin zero) : C p :=
  by cases p

  definition nz_cases_on2 {C  : Π n, fin (succ n) → Type}
                         (H₁ : Π n, C n (fz n))
                         (H₂ : Π n (f : fin n), C n (fs f))
                         {n  : nat}
                         (f  : fin (succ n)) : C n f :=
  begin
    cases f,
    apply (H₁ n),
    apply (H₂ n a)
  end

end fin
