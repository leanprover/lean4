import logic
open nat

inductive vec (A : Type) : nat → Type :=
vnil : vec A zero |
vone : A → vec A (succ zero) |
vtwo : A → A → vec A (succ (succ zero))

namespace vec

  theorem eone {A : Type} {P : vec A (succ zero) → Type} (H : Π a, P (vone a)) (v : vec A (succ zero)) : P v :=
  begin
    cases v,
    -- apply (H a)
  end
end vec
