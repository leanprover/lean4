import data.nat.basic data.empty data.prod
open nat eq.ops prod

inductive vector (T : Type) : ℕ → Type :=
|  nil {} : vector T 0
|  cons : T → ∀{n}, vector T n → vector T (succ n)

set_option pp.metavar_args true
set_option pp.implicit true
set_option pp.notation false

namespace vector
  variables {A B C : Type}
  variables {n m : nat}

  theorem z_cases_on {C : vector A 0 → Type} (v : vector A 0) (Hnil : C nil) : C v :=
  begin
    cases v,
    apply Hnil
  end

  protected definition destruct (v : vector A (succ n)) {P : Π {n : nat}, vector A (succ n) → Type}
                      (H : Π {n : nat} (h : A) (t : vector A n), P (cons h t)) : P v :=
  begin
    cases v with [h', n', t'],
    apply (H h' t')
  end

end vector
