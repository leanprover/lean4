import data.nat.basic
open nat

theorem zero_left (n : ℕ) : 0 + n = n :=
nat.induction_on n
    !nat.add_zero
    (take m IH, show 0 + succ m = succ m, from
      calc
        0 + succ m = succ (0 + m) : add_succ
               ... = succ m       : IH)
