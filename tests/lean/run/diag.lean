import data.examples.vector
open nat

namespace vector

definition diag {A} {n} : vector (vector A n) n → vector A n :=
nat.rec_on n
  (λv, nil)
  (λn₁ (r : vector (vector A n₁) n₁ → vector A n₁) (v : vector (vector A (succ n₁)) (succ n₁)),
    let h₁ : A                       := head (head v) in
    let t₁ : vector (vector A n₁) n₁ := map tail (tail v) in
    h₁ :: r t₁)

example : diag ((1 :: 2 :: 3 :: nil) :: (4 :: 5 :: 6 :: nil) :: (7 :: 8 :: 9 :: nil) :: nil) = (1 :: 5 :: 9 :: nil : vector num 3)  :=
rfl

end vector
