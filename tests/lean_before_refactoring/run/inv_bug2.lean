import data.examples.vector
open nat

namespace vector
 variables {A : Type} {n : nat}

  protected definition destruct2 (v : vector A (succ (succ n))) {P : Π {n : nat}, vector A (succ n) → Type}
                                 (H : Π {n : nat} (h : A) (t : vector A n), P (h :: t)) : P v :=
  begin
    cases v with [n', h', t'],
    apply (H h' t')
  end
end vector
