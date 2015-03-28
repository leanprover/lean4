open nat

inductive vec (A : Type) : nat → Type :=
| nil {} : vec A zero
| cons   : Π {n}, A → vec A n → vec A (succ n)

namespace vec
  variables {A B C : Type}
  variables {n m : nat}
  notation a :: b := cons a b

  protected definition destruct (v : vec A (succ n)) {P : Π {n : nat}, vec A (succ n) → Type}
                      (H : Π {n : nat} (h : A) (t : vec A n), P (h :: t)) : P v :=
  begin
    cases v with [n', h', t'],
    apply (H h' t')
  end

end vec
