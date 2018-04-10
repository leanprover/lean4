inductive fi : ℕ → Type
| zero : Π {n}, fi (n + 1)
| suc : Π {n}, fi n → fi (n + 1)
open fi

namespace fi

def lift {n k} : Π m,  (fi n → fi k) → fi (n + m) → fi (k + m) :=
begin
    intros m f i, induction m with m ih_m, exact f i,
    cases i with n n i, exact fi.zero,
    exact fi.suc (ih_m i)
end

end fi
