import algebra.function

open function

structure bijection (A : Type) :=
(func finv : A → A)
(linv : finv ∘ func = id)
(rinv : func ∘ finv = id)

attribute bijection.func [coercion]

namespace bijection
  variable {A : Type}

  protected theorem eq {f g : bijection A}
    (func_eq : func f = func g) (finv_eq : finv f = finv g) : f = g :=
  begin
    revert finv_eq,
    revert func_eq,
    cases g with [gfunc, gfinv, glinv, grinv],
    cases f with [func, finv, linv, rinv],
    state,
    esimp,
    intros [func_eq, finv_eq],
    revert grinv, revert glinv, revert rinv, revert linv,
    rewrite [func_eq, finv_eq],
    intros [H1, H2, H3, H4],
    apply rfl
  end

end bijection
